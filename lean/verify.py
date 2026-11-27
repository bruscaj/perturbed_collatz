#!/usr/bin/env python3
"""Build every released Lean module in clean temporary projects and audit axioms.

Requires the pinned versions through elan, or explicit toolchain directories.
No installed package, cached project object, or private repository file is used.
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
PROJECTS = {"frontier": "4.24.0", "inverse": "4.24.0", "perturbed": "4.19.0", "sprint": "4.24.0"}
SOURCE_FILES = {
    "frontier": [
        "Collatz/SevenStepCertificate.lean",
        "Collatz/SevenStepCertificate/A3Recursive.lean",
        "Collatz/SevenStepCertificate/A3TwoStage.lean",
        "Collatz/SevenStepCertificate/B1AllGuards.lean",
        "Collatz/SevenStepCertificate/B1ComplementWitness.lean",
        "Collatz/SevenStepCertificate/B1Entry.lean",
        "Collatz/SevenStepCertificate/B1FinalObligation.lean",
        "Collatz/SevenStepCertificate/B1Primitives.lean",
        "Collatz/SevenStepCertificate/B1Recursive.lean",
        "Collatz/SevenStepCertificate/B1Repayment.lean",
        "Collatz/SevenStepCertificate/B1RepaymentArithmetic.lean",
        "Collatz/SevenStepCertificate/B1RepaymentPrimitive.lean",
        "Collatz/SevenStepCertificate/B1SelfReturns.lean",
        "Collatz/SevenStepCertificate/B1Terminals.lean",
        "Collatz/SevenStepCertificate/Basic.lean",
        "Collatz/SevenStepCertificate/Certificates.lean",
        "Collatz/SevenStepCertificate/FrontierIdentities.lean",
        "Collatz/SevenStepCertificate/N03Recursive.lean",
        "Collatz/SevenStepCertificate/N03TwoStage.lean",
        "Collatz/SevenStepCertificate/RefinedFrontier.lean",
        "Collatz/SevenStepCertificate/Relational.lean",
        "Collatz/SevenStepCertificate/ResidualInduction.lean",
        "A3SharedComponent.lean",
        "AffineCounterTermination.lean",
        "ResidualVerification.lean",
        "B1GuardComplement.lean",
        "CoverAlgebra.lean",
        "FamilyCoverTheory.lean",
        "GeneralRepaymentBound.lean",
        "PeriodComposition.lean",
        "RepaymentBound.lean",
        "RepaymentPhysical.lean",
    ],
    "inverse": ["Collatz/Admissibility.lean", "Collatz/BinaryZoom.lean",
                "Collatz/Branches.lean", "Collatz/Coverage.lean",
                "Collatz/CycleMultiplier.lean", "Collatz/Physical.lean",
                "Collatz/ReleaseBridge.lean", "Collatz/SevenFrontier.lean",
                "Collatz/SevenRows.lean", "Collatz/SevenStep.lean", "Collatz/Tree.lean"],
    "perturbed": ["Collatz.lean", "BasinGrowth.lean", "InverseBranch.lean",
                  "ResidueTrack.lean", "TernaryPump.lean", "ProgressionSteering.lean"],
    "sprint": ["RootInverseHeight.lean", "RootPacket.lean"],
}

EXTRA_BUILD_TARGETS = {"frontier": [], "inverse": ["Collatz.ReleaseBridge"], "perturbed": [], "sprint": []}
ADVERSARIAL_FILES = {"frontier": ["FrontierAdversarial.lean"], "inverse": ["SevenAdversarial.lean"], "perturbed": [], "sprint": []}


def source_inventory(project: str) -> tuple[dict, int]:
    """Check this release's simple, single-namespace source layout for omissions.

    Lean itself supplies every theorem type and axiom closure. This text scan
    only makes omitted named source theorems or unlisted modules a hard failure.
    A future change to the source's namespace style requires updating this scan.
    """
    root = HERE / project
    wrappers = {"Audit.lean", "Inventory.lean",
                "Collatz.lean" if project == "inverse" else "All.lean"}
    actual = {str(path.relative_to(root)) for path in root.rglob("*.lean")
              if ".lake" not in path.parts}
    expected = set(SOURCE_FILES[project]) | wrappers | set(ADVERSARIAL_FILES[project])
    if actual != expected:
        raise RuntimeError(f"{project}: unlisted or missing Lean modules: {actual ^ expected}")
    declarations = {}
    private_count = 0
    for relative in SOURCE_FILES[project]:
        content = (root / relative).read_text()
        namespaces = re.findall(r"^namespace\s+(\S+)\s*$", content, re.MULTILINE)
        if len(namespaces) != 1:
            raise RuntimeError(f"{relative}: update the inventory for changed namespace layout")
        for number, line in enumerate(content.splitlines(), 1):
            match = re.match(r"^(private )?theorem\s+(\S+)", line)
            if match:
                if match.group(1):
                    private_count += 1
                else:
                    name = namespaces[0] + "." + match.group(2)
                    if name in declarations:
                        raise RuntimeError(f"duplicate named theorem {name}")
                    declarations[name] = {"source": relative, "line": number}
    return declarations, private_count


def run(command: list[str], cwd: Path, env: dict[str, str]) -> dict:
    start = time.monotonic()
    result = subprocess.run(command, cwd=cwd, env=env, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    record = {"command": [Path(command[0]).name, *command[1:]],
              "exit_code": result.returncode,
              "seconds": round(time.monotonic() - start, 3), "output": result.stdout}
    if result.returncode:
        print(result.stdout, end="")
        raise RuntimeError(json.dumps(record))
    return record


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain-419", type=Path, help="Lean 4.19.0 installation root")
    parser.add_argument("--toolchain-424", type=Path, help="Lean 4.24.0 installation root")
    parser.add_argument("--output", type=Path, help="Write a JSON verification report")
    parser.add_argument("--check-inventory", type=Path,
                        help="Also compare source hashes, types, and axioms against a saved inventory")
    args = parser.parse_args()
    report = {"status": "running", "scope": "four legacy released Lean projects; external support checked separately",
              "independent_kernel": "not run", "projects": {}}
    try:
        for project, expected in PROJECTS.items():
            expected_declarations, private_count = source_inventory(project)
            install = args.toolchain_419 if expected == "4.19.0" else args.toolchain_424
            env = dict(os.environ)
            # Discard ambient search paths that could import private or stale objects.
            env.pop("LEAN_PATH", None)
            env.pop("LEAN_SRC_PATH", None)
            if install:
                env["PATH"] = str(install.resolve() / "bin") + os.pathsep + env.get("PATH", "")
                lake = str(install.resolve() / "bin/lake")
            else:
                lake = shutil.which("lake", path=env.get("PATH"))
                if not lake:
                    raise RuntimeError("lake is unavailable; install elan or pass both --toolchain options")
            with tempfile.TemporaryDirectory(prefix="collatz-release-lean-") as tmp:
                destination = Path(tmp) / project
                shutil.copytree(HERE / project, destination,
                                ignore=shutil.ignore_patterns(".lake", "*.olean", "*.ilean", "*.trace"))
                steps = []
                version = run([lake, "env", "lean", "--version"], destination, env)
                steps.append(version)
                if not re.search(r"\bversion " + re.escape(expected) + r"(?:,|\s|$)", version["output"]):
                    raise RuntimeError(f"{project}: expected Lean {expected}, got {version['output'].strip()}")
                steps.append(run([lake, "build"], destination, env))
                if EXTRA_BUILD_TARGETS[project]:
                    steps.append(run([lake, "build", *EXTRA_BUILD_TARGETS[project]], destination, env))
                for fixture in ADVERSARIAL_FILES[project]:
                    steps.append(run([lake, "env", "lean", "-DwarningAsError=true", fixture], destination, env))
                audit = run([lake, "env", "lean", "-DwarningAsError=true", "Audit.lean"], destination, env)
                steps.append(audit)
                inventory = run([lake, "env", "lean", "-DwarningAsError=true", "Inventory.lean"], destination, env)
                steps.append(inventory)
                declarations = []
                module_audit = None
                for line in inventory["output"].splitlines():
                    if line.startswith("RELEASE_THEOREM "):
                        declarations.append(json.loads(line.removeprefix("RELEASE_THEOREM ")))
                    if line.startswith("RELEASE_AUDIT "):
                        module_audit = json.loads(line.removeprefix("RELEASE_AUDIT "))
                if not declarations:
                    raise RuntimeError(f"{project}: theorem inventory was empty")
                actual_names = [entry["declaration"] for entry in declarations]
                if len(actual_names) != len(set(actual_names)) or set(actual_names) != set(expected_declarations):
                    raise RuntimeError(f"{project}: Lean inventory does not match named public source theorems")
                if not module_audit or not module_audit["theorem_constants_including_private_and_generated"]:
                    raise RuntimeError(f"{project}: complete module axiom audit was empty")
                for entry in declarations:
                    entry.update(expected_declarations[entry["declaration"]])
                hashes = {str(p.relative_to(HERE / project)): hashlib.sha256(p.read_bytes()).hexdigest()
                          for p in sorted((HERE / project).rglob("*.lean"))}
                report["projects"][project] = {
                    "status": "passed", "lean_version": expected, "clean_build": True,
                    "theorem_count": len(declarations), "private_source_theorem_count": private_count,
                    "module_audit": module_audit, "adversarial_files": ADVERSARIAL_FILES[project], "sources_sha256": hashes,
                    "declarations": sorted(declarations, key=lambda x: x["declaration"]), "steps": steps}
                print(f"{project}: clean build and full module axiom audit passed; "
                      f"{len(declarations)} named public source theorems")
        if args.check_inventory:
            recorded = json.loads(args.check_inventory.read_text())
            for project in PROJECTS:
                for field in ("lean_version", "theorem_count", "private_source_theorem_count",
                              "module_audit", "adversarial_files", "sources_sha256", "declarations"):
                    if report["projects"][project][field] != recorded["projects"][project][field]:
                        raise RuntimeError(f"{project}: saved inventory differs in {field}")
            print("Saved inventory matches current sources, checked statements, and axiom dependencies")
        report["status"] = "passed"
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        raise
    finally:
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(json.dumps(report, indent=2) + "\n")


if __name__ == "__main__":
    main()
