#!/usr/bin/env python3
"""Reproduce release evidence. Quick checks are explicitly not exhaustive censuses."""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def check_manifest():
    manifest = json.loads((ROOT / "MANIFEST.json").read_text())
    seen = set()
    for entry in manifest["files"]:
        relative = Path(entry["path"])
        if relative.is_absolute() or ".." in relative.parts or entry["path"] in seen:
            raise ValueError("Unsafe or duplicate manifest path")
        seen.add(entry["path"])
        path = ROOT / relative
        if path.is_symlink() or not path.is_file():
            raise ValueError(f"Missing file or symlink: {relative}")
        data = path.read_bytes()
        if len(data) != entry["bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
            raise ValueError(f"Manifest mismatch: {relative}")
    if not seen:
        raise ValueError("Empty manifest")
    return len(seen)


def main():
    if not __debug__:
        raise SystemExit("Verification requires normal Python; -O is unsupported.")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("quick", "full", "all"), default="quick")
    parser.add_argument("--workers", type=int, default=4)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--toolchain-419", type=Path)
    parser.add_argument("--toolchain-424", type=Path)
    args = parser.parse_args()
    if not 1 <= args.workers <= 4:
        parser.error("workers must be between 1 and 4")
    report = {"mode": args.mode, "status": "running", "checks": [],
              "limits": ["A clean build checks the stated Lean declarations, not the whole paper.",
                         "Quick mode does not rerun the exhaustive impulse censuses.",
                         "No external independent Lean kernel checker is included."]}
    env = dict(os.environ)
    env.pop("PYTHONOPTIMIZE", None)
    env["PYTHONDONTWRITEBYTECODE"] = "1"
    with tempfile.TemporaryDirectory(prefix="collatz-release-") as directory:
        tmp = Path(directory)

        def run(label, command, expected=None):
            start = time.monotonic()
            process = subprocess.run([str(x) for x in command], cwd=ROOT, env=env,
                                     text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            record = {"label": label, "exit_code": process.returncode,
                      "seconds": round(time.monotonic()-start, 3)}
            report["checks"].append(record)
            if process.returncode:
                print(process.stdout)
                print(process.stderr, file=sys.stderr)
                raise RuntimeError(f"Failed: {label}")
            if expected:
                generated = json.loads(process.stdout)
                recorded = json.loads((ROOT / expected).read_text())
                if canonical(generated) != canonical(recorded):
                    raise ValueError(f"Generated JSON differs: {expected}")
                record["all_json_fields_match"] = True
            print(f"PASS {label} ({record['seconds']:.2f}s)", flush=True)
            return process.stdout

        py = sys.executable
        imp = Path("certificates/impulses")
        inv = Path("certificates/inverse")
        try:
            report["manifest_files"] = check_manifest()
            print(f"PASS manifest ({report['manifest_files']} files)", flush=True)
            run("one/two-pair exhaustive census", [py, imp / "small.py"], imp / "small.json")
            run("eight signed layers and endpoint populations",
                [py, imp / "six_impulses/eight_frontier.py"], imp / "six_impulses/eight_frontier.json")
            run("six-impulse complement and literal witnesses", [py, imp / "independent_six/check_complement.py"])
            run("eight-impulse stored shards and every local witness", [py, imp / "full_excursions/run.py", "--check"])
            run("eight-impulse hostile mutations", [py, imp / "test_mutations.py"])
            run("inverse finite steering kernel", [py, inv / "certify_ap.py"], inv / "certificate.json")
            run("inverse translation word examples", [py, inv / "certify_translation.py"], inv / "translation_examples.json")
            run("exact worked exposition examples", [py, "certificates/exposition/verify.py"])
            run("exact inverse worked examples", [py, inv / "worked_examples.py"])
            run("geometry rational certificates and hostile checks", [py, "certificates/geometry/verify.py"])
            run("seven-step independent exact reconstruction", [py, "certificates/seven_step/verify.py"])
            run("seven-step hostile mutations", [py, "certificates/seven_step/test_mutations.py"])
            run("three-family complete affine reconstruction", [py, "certificates/seven_step/three_family.py"])
            run("three-family hostile mutations", [py, "certificates/seven_step/test_three_family.py"])
            if args.mode in ("full", "all"):
                run("all 24-step inverse formulas", [py, inv / "certify_growth.py"], inv / "growth_certificate.json")
                six = tmp / "six"
                run("compile independent six census", ["c++", "-O3", "-std=c++17", "-Wall", "-Wextra", "-Wpedantic",
                                                        imp / "independent_six/verify.cpp", "-o", six])
                run("all six-impulse core words", [six], imp / "independent_six/census.json")
                out = tmp / "eight"
                run("all eight-impulse core words", [py, imp / "full_excursions/run.py", "--workers", args.workers,
                                                    "--output-dir", out])
                for name in ("partitions.json", "results.json"):
                    if canonical(json.loads((out/name).read_text())) != canonical(json.loads((ROOT/imp/"full_excursions"/name).read_text())):
                        raise ValueError("Exhaustive eight census differs: " + name)
                report["eight_full_archive_matches"] = True
                eight = tmp / "eight-independent"
                run("compile independent eight census", ["c++", "-O3", "-std=c++17", "-Wall", "-Wextra", "-Wpedantic",
                                                          imp / "independent_eight/scan.cpp", "-o", eight])
                run("independent complete eight census", [py, imp / "independent_eight/census.py", eight, "--workers", args.workers],
                    imp / "independent_eight/census.json")
            if args.mode == "all":
                cmd = [py, "lean/verify.py", "--check-inventory", "lean/inventory.json", "--output", tmp / "lean.json"]
                for option, value in (("--toolchain-419",args.toolchain_419),("--toolchain-424",args.toolchain_424)):
                    if value:
                        cmd.extend((option,value.resolve()))
                run("all pinned Lean projects and full theorem axiom inventory", cmd)
                run("clean manuscript compilation", [py, "scripts/build_paper.py", "--output", tmp / "paper.pdf"])
            report["status"] = "passed"
        except Exception as error:
            report["status"] = "failed"
            report["error"] = str(error)
            raise
        finally:
            if args.report:
                args.report.resolve().parent.mkdir(parents=True, exist_ok=True)
                args.report.write_text(json.dumps(report,indent=2)+"\n")
    print(f"{args.mode} verification passed. Consult README for the scope of this mode.")


if __name__ == "__main__":
    main()
