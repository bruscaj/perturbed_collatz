"""Clean public h=1 build; full mode requires every replay/comparator/checker gate.

Fetch public dependencies before running this verifier. This program never runs
lake update or the cache downloader. Build mode is explicitly lower assurance.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent
MATHLIB_COMMIT = "56a005855ea17e0b0958f73ec801ae140b0a1679"
OWNED_MODULES = ("Definitions", "ExpectedTypes", "Arithmetic", "DensityBounds",
    "Progressions", "Cylinders", "ExitCylinders", "Gains", "PopulationWeights",
    "CountablePartition", "PartitionGeneral", "PopulationLabels", "SourceDensity",
    "DensityTheorems", "DepthOneSeries", "DepthOneLower", "DepthOneUpper",
    "DepthOneFormula", "DepthOneNumerics", "NumericInfimum", "LogRatioIrrational",
    "PositiveCeilReturns", "DepthOneNonattainment", "Solution")
TARGETS = tuple("ExternalO3Challenge."+name for name in (
    "valuationFoundation", "blockLengthLaw", "fixedPointConvention", "correctionZeroIrrelevant",
    "densityExists", "densityUnique", "sourceDensityEquivalence", "symbolicMassSummable",
    "densityEqualsSymbolic", "infimumWellPosed", "depthOneSeriesSummable", "depthOneFormula",
    "depthOneNotAttained", "depthOneTail"))
FROZEN_SOURCES = {
    "Definitions.lean": "cf29376721942a78328491cd910690497f95d381711f0d2e758998fbba9374bc",
    "ExpectedTypes.lean": "5ce898eb70690f6f77e26a95cbafb5ef268fa93617ab7418a0b25f6878c34968",
    "Challenge.lean": "636b251a8d0205d2b49559dfaa54298ea2ebc3408ca4c315ce7e2d99dae61514"}
AXIOMS = ("propext", "Quot.sound", "Classical.choice")


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def source_gate(root, inventory=None):
    """Fail closed on frozen meanings, module omissions and edited audit inputs."""
    root = Path(root)
    inventory = inventory or json.loads((HERE/"inventory.json").read_text())
    expected = {m+".lean" for m in OWNED_MODULES} | {"Challenge.lean", "Audit.lean"}
    actual = {p.name for p in root.glob("*.lean")}
    require(actual == expected, f"owned Lean module coverage mismatch: {sorted(actual ^ expected)}")
    for name, pin in FROZEN_SOURCES.items():
        require(digest(root/name) == pin, f"frozen source digest mismatch: {name}")
    require(json.loads((root/"owned_modules.json").read_text()) == list(OWNED_MODULES),
            "owned module register mismatch")
    config = json.loads((root/"comparator.json").read_text())
    require(config["theorem_names"] == list(TARGETS), "frozen target register mismatch")
    require(config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution",
            "comparator module mismatch")
    require(config["permitted_axioms"] == list(AXIOMS), "axiom policy mismatch")
    require(config.get("external_kernels") == {"nanoda": ["nanoda_bin"]},
            "independent checker configuration mismatch")
    require(config.get("definition_names") == [], "unexpected definition holes")
    for name, pin in inventory["sources_sha256"].items():
        path = Path(name)
        require(not path.is_absolute() and ".." not in path.parts, "unsafe source inventory path")
        require((root/path).is_file() and not (root/path).is_symlink(), f"missing source: {name}")
        require(digest(root/path) == pin, f"source inventory mismatch: {name}")


def prepare_dependencies(root, *, dependency_cache=None, mathlib_cache=None):
    """Materialize public Git-pinned cached dependencies; never fetch or mutate the cache.

    dependency_cache is a normal prepared project's .lake/packages directory.
    mathlib_cache is a pinned mathlib checkout with its normal dependency cache.
    Omitting both uses this public project's existing .lake/packages directory.
    This helper intentionally does not accept/rewrite any own proof source.
    """
    root = Path(root)
    require(not (dependency_cache and mathlib_cache), "choose one dependency cache layout")
    manifest = json.loads((HERE/"lake-manifest.json").read_text())
    require(manifest["packagesDir"] == ".lake/packages", "unexpected package layout")
    packages = manifest["packages"]
    names = [p["name"] for p in packages]
    require(len(names) == len(set(names)) and "mathlib" in names, "invalid package inventory")
    destination = root/".lake/packages"
    destination.mkdir(parents=True, exist_ok=True)
    records = []
    for package in packages:
        name = package["name"]
        require(re.fullmatch(r"[A-Za-z0-9_-]+", name), "unsafe package name")
        require(package["type"] == "git" and re.fullmatch(r"[0-9a-f]{40}", package["rev"]),
                f"dependency lacks an exact Git pin: {name}")
        require(package["url"].startswith("https://github.com/") and "@" not in package["url"],
                f"non-public dependency URL: {name}")
        if name == "mathlib":
            require(package["rev"] == MATHLIB_COMMIT, "mathlib revision mismatch")
        if mathlib_cache:
            source = Path(mathlib_cache) if name == "mathlib" else Path(mathlib_cache)/".lake/packages"/name
        else:
            source = Path(dependency_cache or HERE/".lake/packages")/name
        source = source.resolve()
        require(source.is_dir(), f"missing pinned public dependency cache: {name}; fetch dependencies first")
        revision = subprocess.run(["git", "-C", str(source), "rev-parse", "HEAD"],
                                  capture_output=True, text=True, check=True).stdout.strip()
        require(revision == package["rev"], f"dependency source pin mismatch: {name}")
        subprocess.run(["git", "-C", str(source), "diff", "--exit-code", "HEAD", "--"],
                       capture_output=True, text=True, check=True)
        target = destination/name
        require(not target.exists(), f"dependency destination already exists: {name}")

        def ignore(directory, children):
            ignored = {"__pycache__", ".DS_Store"} & set(children)
            if Path(directory) == source/".lake":
                ignored |= {"packages"} & set(children)
            return ignored

        # Preserve Git-tracked relative links (e.g. batteries docs/README.md)
        # rather than changing their file type. No link may escape its package.
        for directory, dirs, files in os.walk(source, followlinks=False):
            if Path(directory) == source/".lake" and "packages" in dirs:
                dirs.remove("packages")
            for entry in dirs+files:
                path = Path(directory)/entry
                if path.is_symlink():
                    require(path.resolve().is_relative_to(source),
                            f"dependency cache link escapes package: {name}")
        shutil.copytree(source, target, symlinks=True, ignore=ignore)
        subprocess.run(["git", "-C", str(target), "diff", "--exit-code", "HEAD", "--"],
                       capture_output=True, text=True, check=True)
        records.append({"name": name, "url": package["url"], "revision": revision})
    return records


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("build", "full"), default="full")
    parser.add_argument("--toolchain", type=Path)
    parser.add_argument("--dependency-cache", type=Path)
    parser.add_argument("--mathlib-cache", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = {"scope": "all 14 frozen O3 prime h=1 targets; not arbitrary h or M4/R8/R9",
              "mode": args.mode, "status": "running", "steps": []}
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "PYTHONOPTIMIZE"):
        env.pop(key, None)
    if args.toolchain:
        env["PATH"] = str(args.toolchain.resolve()/"bin")+os.pathsep+env.get("PATH", "")
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    lake = shutil.which("lake", path=env.get("PATH"))

    def save():
        if args.report:
            args.report.write_text(json.dumps(report, indent=2)+"\n")

    try:
        source_gate(HERE)
        require(lake is not None, "lake unavailable; install pinned Lean or pass --toolchain")
        inventory = json.loads((HERE/"inventory.json").read_text())
        with tempfile.TemporaryDirectory(prefix="collatz-public-h1-") as temporary:
            root = Path(temporary)/"project"
            root.mkdir()
            # Explicit own source/config inventory; never copy ambient build caches.
            for name in inventory["sources_sha256"]:
                shutil.copyfile(HERE/name, root/name)
            shutil.copyfile(HERE/"inventory.json", root/"inventory.json")
            report["dependencies"] = prepare_dependencies(root,
                dependency_cache=args.dependency_cache, mathlib_cache=args.mathlib_cache)
            save()

            def run(label, command):
                row = {"label": label, "command": [str(x) for x in command], "status": "running"}
                report["steps"].append(row)
                save()
                print(f"RUN {label}", flush=True)
                started = time.monotonic()
                result = subprocess.run([str(x) for x in command], cwd=root, env=env,
                                        capture_output=True, text=True)
                row.update({"exit_code": result.returncode, "seconds": round(time.monotonic()-started, 3),
                            "status": "passed" if result.returncode == 0 else "failed",
                            "stdout": result.stdout, "stderr": result.stderr})
                save()
                require(result.returncode == 0, f"required gate failed: {label}")
                print(f"PASS {label} ({row['seconds']}s)", flush=True)
                return result.stdout

            version = run("pinned toolchain", [lake, "env", "lean", "--version"])
            require("version 4.35.0," in version, "wrong h1 toolchain")
            build = run("all own source clean build", [lake, "build"])
            require("warning:" not in build + report["steps"][-1]["stderr"], "own build emitted a warning")
            missing = [m for m in OWNED_MODULES if not (root/f".lake/build/lib/lean/{m}.olean").is_file()]
            require(not missing, f"own modules omitted from build: {missing}")
            source_gate(root, inventory)
            audit = run("all own theorem closures and raw frozen target types",
                        [lake, "env", "lean", "-DwarningAsError=true", "Audit.lean"])
            targets = [json.loads(x.removeprefix("O3_TARGET ")) for x in audit.splitlines()
                       if x.startswith("O3_TARGET ")]
            helpers = [json.loads(x.removeprefix("O3_HELPER ")) for x in audit.splitlines()
                       if x.startswith("O3_HELPER ")]
            targets.sort(key=lambda x:x["declaration"])
            helpers.sort(key=lambda x:x["declaration"])
            require([x["declaration"] for x in targets] == sorted(TARGETS), "missing frozen target implementation")
            require(targets == inventory["targets"], "elaborated frozen target inventory mismatch")
            require(helpers == inventory["helpers"], "own generated-helper inventory mismatch")
            report.update({"targets": targets, "helpers": helpers, "own_module_count": len(OWNED_MODULES),
                           "own_theorem_count": len(targets)+len(helpers)})
            if args.mode == "full":
                roots = sorted({x["declaration"] for x in targets+helpers})
                export = root/".lake/h1-complete-proof-closure.ndjson"
                command = [lake, "env", "leanexport", "Solution", "--", *roots]
                started = time.monotonic()
                with export.open("wb") as stream:
                    result = subprocess.run(command, cwd=root, env=env, stdout=stream,
                                            stderr=subprocess.PIPE, text=True)
                row = {"label": "fresh complete own proof-closure export", "command": command,
                    "exit_code": result.returncode, "seconds": round(time.monotonic()-started, 3),
                    "stderr": result.stderr, "roots": roots, "bytes": export.stat().st_size,
                    "sha256": digest(export), "source_sha256": inventory["sources_sha256"]}
                report["steps"].append(row)
                save()
                require(result.returncode == 0 and export.stat().st_size > 0, "fresh complete proof export failed")
                run("fresh complete proof-closure replay and all bundled checkers",
                    [lake, "check", "--from-export", export, "--paranoid"])
                run("all 14 frozen statements and independent checker",
                    [lake, "comparator", "--config", "comparator.json", "--paranoid"])
                report["status"] = "passed h1 full assurance gates"
            else:
                report["status"] = "partial: clean h1 build and axiom audit only"
                report["missing_gates"] = ["fresh imported-proof replay", "trusted statement comparator",
                                           "independently implemented checker"]
    except Exception as error:
        report.update({"status": "failed", "error": str(error)})
        raise
    finally:
        save()
    print(report["status"])


if __name__ == "__main__":
    main()
