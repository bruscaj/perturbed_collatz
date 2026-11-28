"""Negative controls for five supporting lemmas, not the external headline claims.

Default full mode requires pinned Lean 4.35.0, Linux sandbox support and nanoda.
Use --mode source for portable digest/module controls only; this is explicitly
partial and makes no comparator or independent-replay claim. All mutations live
in temporary copies. Frozen source files and checker configuration stay intact.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
REQUIRED = ("Definitions.lean", "ExpectedTypes.lean", "Challenge.lean",
            "Solution.lean", "Audit.lean", "lakefile.toml", "lean-toolchain",
            "lake-manifest.json", "comparator.json", "freeze.json")
TARGET = "floorDepthEquivalence"


def require(ok, message):
    if not ok:
        raise ValueError(message)


def source_gate(root):
    for name in REQUIRED:
        require((root/name).is_file(), f"missing required module/config: {name}")
    freeze = json.loads((root/"freeze.json").read_text())
    for name, record in freeze["files"].items():
        path = Path(name)
        require(not path.is_absolute() and ".." not in path.parts,
                f"unsafe trusted source path: {name}")
        require((root/path).is_file(), f"missing frozen file: {name}")
        data = (root/path).read_bytes()
        require(hashlib.sha256(data).hexdigest() == record["sha256"],
                f"frozen source digest mismatch: {name}")
        require(len(data) == record["bytes"], f"frozen source size mismatch: {name}")


def replace_target(root, statement, body):
    path = root/"Solution.lean"
    source = path.read_text()
    start = source.index(f"theorem {TARGET} :")
    stop = source.index("\ntheorem depthInvolution", start)
    path.write_text(source[:start] + f"theorem {TARGET} : {statement} := by\n  {body}\n" + source[stop:])


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("source", "full"), default="full")
    parser.add_argument("--toolchain", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = {"scope": "supporting prefix theorems only", "mode": args.mode,
              "status": "running", "controls": [], "commands": []}
    env = dict(os.environ)
    for name in ("LEAN_PATH", "LEAN_SRC_PATH", "PYTHONOPTIMIZE"):
        env.pop(name, None)
    if args.toolchain:
        env["PATH"] = str(args.toolchain.resolve()/"bin") + os.pathsep + env.get("PATH", "")
    lake = shutil.which("lake", path=env.get("PATH"))

    def run(root, label, command, success=True, rejection=None):
        result = subprocess.run(command, cwd=root, env=env, capture_output=True, text=True)
        row = {"label": label, "command": command, "exit_code": result.returncode,
               "stdout": result.stdout, "stderr": result.stderr}
        report["commands"].append(row)
        if success:
            require(result.returncode == 0, f"positive prerequisite failed: {label}")
        else:
            require(result.returncode != 0, f"mutation unexpectedly accepted: {label}")
            if rejection:
                code, message = rejection
                require(code is None or result.returncode == code,
                        f"unexpected rejection exit status for {label}: {result.returncode}")
                require(message in result.stdout + result.stderr,
                        f"wrong rejection reason for {label}; expected {message!r}")
        return result

    try:
        # Positive portable prerequisite checked against the original freeze.
        source_gate(HERE)
        with tempfile.TemporaryDirectory(prefix="external-negative-controls-") as temp:
            base = Path(temp)

            def fixture(name):
                root = base/name
                shutil.copytree(HERE, root, ignore=shutil.ignore_patterns(
                    ".lake", "*.olean", "*.ilean", "__pycache__", "*.log"))
                source_gate(root)
                return root

            definitions = fixture("changed-definitions")
            definition_file = definitions/"Definitions.lean"
            original = definition_file.read_text()
            require("K t ≤ L t" in original, "definition mutation anchor missing")
            definition_file.write_text(original.replace("K t ≤ L t", "K t < L t", 1))
            try:
                source_gate(definitions)
            except ValueError as error:
                require("frozen source digest mismatch: Definitions.lean" in str(error),
                        "definition mutation rejected for wrong reason")
                report["controls"].append({"name": "changed trusted definitions",
                    "gate": "frozen source digest", "result": "rejected", "reason": str(error)})
            else:
                raise ValueError("changed frozen definitions accepted")

            missing = fixture("missing-module")
            (missing/"Definitions.lean").unlink()
            try:
                source_gate(missing)
            except ValueError as error:
                require("missing required module/config: Definitions.lean" in str(error),
                        "missing-module mutation rejected for wrong reason")
                report["controls"].append({"name": "missing required module",
                    "gate": "source module coverage", "result": "rejected", "reason": str(error)})
            else:
                raise ValueError("missing module accepted")

            if args.mode == "full":
                require(lake is not None, "lake unavailable; full controls not executed")
                positive = fixture("positive")
                version = run(positive, "pinned version", [lake, "env", "lean", "--version"])
                require("version 4.35.0," in version.stdout, "wrong supporting toolchain")
                run(positive, "positive complete source-bound proof verification",
                    [sys.executable, str(positive/"verify.py"), "--mode", "full"])

                wrong = fixture("wrong-statement")
                replace_target(wrong, "True", "trivial")
                # Deliberately invoke the comparator directly, bypassing the
                # source/inventory gate, to exercise statement matching itself.
                run(wrong, "wrong-statement builds", [lake, "build"])
                run(wrong, "wrong statement rejected by comparator",
                    [lake, "comparator", "--config", "comparator.json", "--paranoid"],
                    success=False, rejection=(1, "Challenge and solution theorem statement do not match: 'ExternalPrefixChallenge.floorDepthEquivalence'"))
                report["controls"].append({"name": "weakened theorem to True",
                    "gate": "elaborated comparator", "result": "rejected"})

                axiom = fixture("hidden-imported-axiom")
                (axiom/"BadPremise.lean").write_text(
                    "import ExpectedTypes\nnamespace BadPremise\n"
                    "axiom hiddenFloor : ExternalPrefixSpec.FloorDepthEquivalence\n"
                    "end BadPremise\n")
                with (axiom/"lakefile.toml").open("a") as out:
                    out.write('\n[[lean_lib]]\nname = "BadPremise"\n')
                replace_target(axiom, "FloorDepthEquivalence", "exact BadPremise.hiddenFloor")
                solution = axiom/"Solution.lean"
                solution.write_text("import BadPremise\n" + solution.read_text())
                run(axiom, "hidden-axiom builds", [lake, "build"])
                run(axiom, "hidden imported axiom rejected by closure audit",
                    [lake, "env", "lean", "-DwarningAsError=true", "Audit.lean"],
                    success=False, rejection=(None, "has forbidden axiom BadPremise.hiddenFloor"))
                report["controls"].append({"name": "hidden imported custom axiom",
                    "gate": "transitive axiom audit", "result": "rejected"})
                report["status"] = "passed supporting negative controls and positive full prerequisites"
            else:
                report["status"] = "partial: portable source controls passed"
                report["not_executed"] = ["fresh replay", "statement-comparator rejection",
                                          "hidden-axiom Lean rejection", "independent checker"]
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        raise
    finally:
        if args.report:
            args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in ("scope", "mode", "status", "controls")}))


if __name__ == "__main__":
    main()
