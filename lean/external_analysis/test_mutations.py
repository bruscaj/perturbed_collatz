"""Negative controls for the fourteen frozen O3′ h=1 targets.

--mode source is portable and checks original source hashes/module/target
coverage only. It is explicitly partial and does not run a statement comparator.
Full mode requires Linux, pinned Lean 4.35.0 and prepared pinned dependencies.
It first requires the positive full fourteen-target verifier to pass, then runs
actual comparator, axiom-closure and Lean arithmetic rejection fixtures.
Production sources, proof targets and checker configuration are never modified.
"""
from __future__ import annotations

import argparse
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
from fractions import Fraction

HERE = Path(__file__).resolve().parent
TARGETS = tuple("ExternalO3Challenge." + name for name in (
    "valuationFoundation", "blockLengthLaw", "fixedPointConvention",
    "correctionZeroIrrelevant", "densityExists", "densityUnique",
    "sourceDensityEquivalence", "symbolicMassSummable", "densityEqualsSymbolic",
    "infimumWellPosed", "depthOneSeriesSummable", "depthOneFormula",
    "depthOneNotAttained", "depthOneTail"))
SPEC_PINS = {
    "Definitions.lean": "cf29376721942a78328491cd910690497f95d381711f0d2e758998fbba9374bc",
    "ExpectedTypes.lean": "5ce898eb70690f6f77e26a95cbafb5ef268fa93617ab7418a0b25f6878c34968",
    "Challenge.lean": "636b251a8d0205d2b49559dfaa54298ea2ebc3408ca4c315ce7e2d99dae61514",
}
OWNED = (
    "Definitions", "ExpectedTypes", "Arithmetic", "DensityBounds", "Progressions",
    "Cylinders", "ExitCylinders", "Gains", "PopulationWeights", "CountablePartition",
    "PartitionGeneral", "PopulationLabels", "SourceDensity", "DensityTheorems",
    "DepthOneSeries", "DepthOneLower", "DepthOneUpper", "DepthOneFormula",
    "DepthOneNumerics", "NumericInfimum", "LogRatioIrrational", "PositiveCeilReturns",
    "DepthOneNonattainment", "Solution")
REQUIRED = tuple(name + ".lean" for name in OWNED) + (
    "Challenge.lean", "Audit.lean", "verify.py", "inventory.json", "specification.json",
    "owned_modules.json", "comparator.json", "lakefile.toml", "lake-manifest.json",
    "lean-toolchain")


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read_json(path):
    return json.loads(path.read_text())


def target_names(rows):
    if isinstance(rows, dict):
        return tuple(rows)
    require(isinstance(rows, list), "unsupported target inventory format")
    return tuple(row if isinstance(row, str) else row["declaration"] for row in rows)


def exact_targets(names, label):
    require(len(names) == len(TARGETS) and set(names) == set(TARGETS),
            f"{label} target coverage mismatch: all fourteen frozen targets are required")


def source_gate(root, reference=None):
    """Compare against immutable original pins, not a mutated fixture's new freeze."""
    for name in REQUIRED:
        require((root/name).is_file(), f"missing required module/config: {name}")
    require((root/"lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0",
            "pinned toolchain source mismatch")
    specification = read_json(root/"specification.json")
    require(specification["mathlib_commit"] == "56a005855ea17e0b0958f73ec801ae140b0a1679",
            "pinned mathlib source mismatch")
    for name, digest in SPEC_PINS.items():
        record = specification["files"][name]
        require(record["sha256"] == digest, f"trusted specification pin changed: {name}")
        data = (root/name).read_bytes()
        require(hashlib.sha256(data).hexdigest() == digest,
                f"original frozen source digest mismatch: {name}")
        require(record["bytes"] == len(data), f"original frozen source size mismatch: {name}")
    exact_targets(tuple(specification["challenge_holes"]), "specification")
    comparator = read_json(root/"comparator.json")
    exact_targets(tuple(comparator["theorem_names"]), "configured")
    require(set(comparator["permitted_axioms"]) == {"propext", "Quot.sound", "Classical.choice"},
            "configured axiom whitelist mismatch")
    owned = tuple(read_json(root/"owned_modules.json"))
    require(len(owned) == len(OWNED) and set(owned) == set(OWNED),
            "owned module coverage mismatch")
    inventory = read_json(root/"inventory.json")
    exact_targets(target_names(inventory["targets"]), "inventory")
    require(len(inventory["owned_modules"]) == len(OWNED) and
            set(inventory["owned_modules"]) == set(OWNED), "inventory owned module coverage mismatch")
    expected = inventory["sources_sha256"] if reference is None else reference["sources_sha256"]
    if reference is not None:
        require(inventory["sources_sha256"] == expected, "original source inventory changed")
        require(inventory["targets"] == reference["targets"], "inventory statement coverage changed")
        require(inventory["helpers"] == reference["helpers"], "inventory helper coverage changed")
    for name, digest in expected.items():
        path = Path(name)
        require(not path.is_absolute() and ".." not in path.parts, f"unsafe source path: {name}")
        require((root/path).is_file(), f"missing inventoried source: {name}")
        require(hashlib.sha256((root/path).read_bytes()).hexdigest() == digest,
                f"original source inventory digest mismatch: {name}")
    return {"sources_sha256": dict(inventory["sources_sha256"]),
            "targets": inventory["targets"], "helpers": inventory["helpers"]}


def replace_once(path, old, new):
    source = path.read_text()
    require(source.count(old) == 1, f"mutation anchor is not unique in {path.name}")
    path.write_text(source.replace(old, new, 1))


def replace_formula_wrapper(root, statement, body):
    path = root/"Solution.lean"
    pattern = r"(?m)^theorem depthOneFormula : [^\n]+$"
    text, count = re.subn(pattern, f"theorem depthOneFormula : {statement} := {body}", path.read_text())
    require(count == 1, "depthOneFormula wrapper mutation anchor missing")
    path.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("source", "full"), default="full")
    parser.add_argument("--toolchain", type=Path)
    parser.add_argument("--mathlib-cache", type=Path)
    parser.add_argument("--dependency-cache", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = {"scope": "fourteen frozen O3 prime h=1 targets; not arbitrary-depth O3 prime",
              "mode": args.mode, "status": "running", "controls": [], "commands": []}
    env = dict(os.environ)
    for name in ("LEAN_PATH", "LEAN_SRC_PATH", "PYTHONOPTIMIZE"):
        env.pop(name, None)
    if args.toolchain:
        env["PATH"] = str(args.toolchain.resolve()/"bin") + os.pathsep + env.get("PATH", "")
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    lake = shutil.which("lake", path=env.get("PATH"))
    reference = None
    try:
        reference = source_gate(HERE)
        # Exact literal boundary example, independent of the Lean proof code:
        # phi(r)=(r-1)log(3/2), x=3 gives zero leading gain but actual failure.
        def valuation(n):
            require(n > 0, "valuation fixture requires positivity")
            return (n & -n).bit_length() - 1
        x = 3
        y = (3*x + 1) // 2**valuation(3*x + 1)
        length_change = valuation(y + 1) - valuation(x + 1)
        symbolic_ratio = Fraction(3, 2) * Fraction(3, 2)**length_change
        actual_ratio = Fraction(y, x) * Fraction(3, 2)**length_change
        require(symbolic_ratio == 1 and actual_ratio == Fraction(10, 9) > 1,
                "literal symbolic-zero failure fixture changed")
        report["symbolic_equality_fixture"] = {"seed": x, "next_seed": y,
            "symbolic_ratio": str(symbolic_ratio), "actual_ratio": str(actual_ratio),
            "failure": True, "scope": "one exact finite semantic witness"}
        with tempfile.TemporaryDirectory(prefix="o3-h1-negative-controls-") as temporary:
            base = Path(temporary)
            log_root = (args.report.resolve().parent/(args.report.stem + "-logs")) if args.report else base/"logs"
            log_root.mkdir(parents=True, exist_ok=True)

            def fixture(label):
                root = base/label
                shutil.copytree(HERE, root, ignore=shutil.ignore_patterns(
                    ".lake", "*.olean", "*.ilean", "__pycache__", "*.log"))
                source_gate(root, reference)
                return root

            def run(root, label, command, *, reject=None):
                log = log_root/(f"{len(report['commands']):03d}-" + re.sub(r"[^a-z0-9]+", "-", label.lower()) + ".log")
                with log.open("w") as output:
                    process = subprocess.run(command, cwd=root, env=env, stdout=output, stderr=subprocess.STDOUT, text=True)
                report["commands"].append({"label": label, "command": command,
                    "exit_code": process.returncode, "log": str(log),
                    "expected_failure": reject is not None})
                text = log.read_text()
                if reject is None:
                    require(process.returncode == 0, f"positive prerequisite failed: {label}; see {log}")
                else:
                    expected_code, reason = reject
                    require(process.returncode != 0, f"mutation unexpectedly accepted: {label}")
                    require(expected_code is None or process.returncode == expected_code,
                            f"wrong rejection exit for {label}: {process.returncode}; see {log}")
                    require(reason(text), f"wrong rejection reason for {label}; see {log}")
                    report["commands"][-1]["expected_exit_code"] = expected_code
                    report["commands"][-1]["rejection_reason_confirmed"] = True
                return text

            prepare = None
            if args.mode == "full":
                require(sys.platform.startswith("linux"), "full controls require Linux sandbox support; not executed")
                require(lake is not None, "lake unavailable; full controls not executed")
                module_spec = importlib.util.spec_from_file_location("trusted_o3_positive_verifier", HERE/"verify.py")
                require(module_spec is not None and module_spec.loader is not None, "trusted verifier unavailable")
                verifier = importlib.util.module_from_spec(module_spec)
                sys.modules[module_spec.name] = verifier
                module_spec.loader.exec_module(verifier)
                require(callable(getattr(verifier, "prepare_dependencies", None)), "verifier dependency preparation API unavailable")

                def prepare(root):
                    verifier.prepare_dependencies(root, dependency_cache=args.dependency_cache,
                                                  mathlib_cache=args.mathlib_cache)

                positive = fixture("positive-full")
                # The positive verifier makes its own fresh dependency copy;
                # avoid first duplicating a multi-gigabyte cache into this fixture.
                positive_report = log_root/"positive-full.json"
                command = [sys.executable, str(positive/"verify.py"), "--mode", "full", "--report", str(positive_report)]
                if args.mathlib_cache:
                    command += ["--mathlib-cache", str(args.mathlib_cache.resolve())]
                else:
                    cache = args.dependency_cache or HERE/".lake/packages"
                    command += ["--dependency-cache", str(cache.resolve())]
                if args.toolchain:
                    command += ["--toolchain", str(args.toolchain.resolve())]
                run(positive, "positive full fourteen-target pipeline", command)
                receipt = read_json(positive_report)
                require(receipt.get("mode") == "full" and str(receipt.get("status", "")).startswith("passed"),
                        "positive full verifier did not report completed full assurance")
                exact_targets(target_names(receipt["targets"]), "positive full receipt")
                report["positive_full_report"] = str(positive_report)
                shutil.rmtree(positive)

            def source_rejection(label, mutate, expected):
                root = fixture(label)
                mutate(root)
                try:
                    source_gate(root, reference)
                except ValueError as error:
                    require(expected in str(error), f"wrong source rejection reason for {label}: {error}")
                    report["controls"].append({"name": label, "gate": "original source/hash/coverage",
                        "result": "rejected", "reason": str(error)})
                else:
                    raise ValueError(f"source mutation unexpectedly accepted: {label}")

            source_rejection("failure equality changed to strict", lambda root: replace_once(root/"Definitions.lean",
                "rawPotential φ (stride x) ≥ rawPotential φ x", "rawPotential φ (stride x) > rawPotential φ x"),
                "original frozen source digest mismatch: Definitions.lean")
            source_rejection("odd-seed normalization factor changed", lambda root: replace_once(root/"Definitions.lean",
                "(failureCount φ N : ℝ) / (N : ℝ)", "(failureCount φ N : ℝ) / (2 * (N : ℝ))"),
                "original frozen source digest mismatch: Definitions.lean")
            source_rejection("corrections restricted to bounded functions", lambda root: replace_once(root/"Definitions.lean",
                "abbrev Correction := ℕ → ℝ", "abbrev Correction := { f : ℕ → ℝ // ∃ C : ℝ, ∀ n, |f n| ≤ C }"),
                "original frozen source digest mismatch: Definitions.lean")
            source_rejection("required nonattainment module dropped", lambda root: (root/"DepthOneNonattainment.lean").unlink(),
                "missing required module/config: DepthOneNonattainment.lean")

            def drop_configured_target(root):
                path = root/"comparator.json"; data = read_json(path)
                data["theorem_names"].remove("ExternalO3Challenge.depthOneNotAttained")
                path.write_text(json.dumps(data, indent=2) + "\n")

            def drop_inventory_target(root):
                path = root/"inventory.json"; data = read_json(path)
                rows = data["targets"]
                if isinstance(rows, dict):
                    del rows["ExternalO3Challenge.depthOneNotAttained"]
                else:
                    data["targets"] = [row for row in rows if
                        (row if isinstance(row, str) else row["declaration"]) != "ExternalO3Challenge.depthOneNotAttained"]
                path.write_text(json.dumps(data, indent=2) + "\n")

            source_rejection("configured target silently skipped", drop_configured_target, "configured target coverage mismatch")
            source_rejection("inventory target silently skipped", drop_inventory_target, "inventory target coverage mismatch")

            if args.mode == "full":
                wrong = fixture("wrong-formula-statement")
                prepare(wrong)
                replace_formula_wrapper(wrong, "True", "by trivial")
                run(wrong, "wrong-statement positive compilation", [lake, "build"])
                expected = "Challenge and solution theorem statement do not match: 'ExternalO3Challenge.depthOneFormula'"
                run(wrong, "wrong statement rejected by actual comparator",
                    [lake, "comparator", "--config", "comparator.json", "--paranoid"],
                    reject=(1, lambda text: expected in text))
                report["controls"].append({"name": "formula wrapper weakened to True",
                    "gate": "actual trusted elaborated statement comparator", "result": "rejected",
                    "mutated_solution_sha256": hashlib.sha256((wrong/"Solution.lean").read_bytes()).hexdigest()})
                shutil.rmtree(wrong)

                axiom = fixture("hidden-imported-custom-axiom")
                prepare(axiom)
                (axiom/"BadPremise.lean").write_text(
                    "import ExpectedTypes\nnamespace BadPremise\n"
                    "axiom hiddenFormula : ExternalO3Spec.DepthOneFormula\nend BadPremise\n")
                with (axiom/"lakefile.toml").open("a") as stream:
                    stream.write('\n[[lean_lib]]\nname = "BadPremise"\n')
                replace_formula_wrapper(axiom, "DepthOneFormula", "BadPremise.hiddenFormula")
                solution = axiom/"Solution.lean"
                solution.write_text("import BadPremise\n" + solution.read_text())
                run(axiom, "custom-axiom positive compilation", [lake, "build"])
                run(axiom, "hidden imported custom axiom rejected by all-closure audit",
                    [lake, "env", "lean", "-DwarningAsError=true", "Audit.lean"],
                    reject=(1, lambda text: "forbidden axiom" in text.lower() and "BadPremise.hiddenFormula" in text))
                report["controls"].append({"name": "hidden imported custom axiom",
                    "gate": "actual all-origin transitive axiom closure audit", "result": "rejected",
                    "mutated_solution_sha256": hashlib.sha256((axiom/"Solution.lean").read_bytes()).hexdigest(),
                    "hidden_premise_sha256": hashlib.sha256((axiom/"BadPremise.lean").read_bytes()).hexdigest()})
                shutil.rmtree(axiom)

                arithmetic = fixture("corrupted-floor-certificate")
                prepare(arithmetic)
                run(arithmetic, "numeric prerequisite series compilation", [lake, "build", "DepthOneSeries"])
                original = (arithmetic/"DepthOneNumerics.lean").read_text()
                require(original.count("\ntheorem certificate_upper") == 1, "numeric certificate slice anchor changed")
                # This is the production lower-certificate proof, including its
                # exact 80-case arithmetic, not a Python mirror of the values.
                slice_source = original.split("\ntheorem certificate_upper", 1)[0] + "\n\nend ExternalO3DepthOneNumerics\n"
                positive_floor = arithmetic/"FloorCertificatePositive.lean"
                positive_floor.write_text(slice_source)
                run(arithmetic, "positive production numeric certificate slice",
                    [lake, "env", "lean", "-DwarningAsError=true", "-R", str(arithmetic), str(positive_floor)])
                corrupt_source, changed = re.subn(r"(def floorValues : List ℕ :=\s*\[)1(?=,)", r"\g<1>2", slice_source, count=1)
                require(changed == 1, "r1 numeric floor mutation anchor changed")
                corrupt_floor = arithmetic/"CorruptedFloor.lean"
                corrupt_floor.write_text(corrupt_source)
                run(arithmetic, "corrupted r1 floor rejected by actual Lean arithmetic proof",
                    [lake, "env", "lean", "-DwarningAsError=true", "-R", str(arithmetic), str(corrupt_floor)],
                    reject=(1, lambda text: "unsolved goals" in text and "⊢ False" in text and
                            ("case «1»" in text or "case 1" in text)))
                report["controls"].append({"name": "r1 floor certificate entry changed from 1 to 2",
                    "gate": "actual Lean production arithmetic checker", "result": "rejected",
                    "positive_slice_sha256": hashlib.sha256(slice_source.encode()).hexdigest(),
                    "corrupt_slice_sha256": hashlib.sha256(corrupt_source.encode()).hexdigest()})
                report["status"] = "passed h1 negative controls and positive full fourteen-target pipeline"
            else:
                report["status"] = "partial: portable original-source/hash/coverage controls passed"
                report["not_executed"] = ["positive full fourteen-target pipeline", "trusted statement comparator rejection",
                    "actual custom-axiom closure rejection", "actual corrupted numeric Lean proof rejection",
                    "sandboxed imported-proof replay", "independent kernel replay"]
                report["semantic_note"] = (
                    "Changing literal >= to > is a frozen-source mismatch, not a counterexample to the density formula. "
                    "The separate exact symbolic-zero witness x=3→5 has potential ratio 10/9 and remains a failure.")
        # Ensure no fixture operation changed the production proof/specification.
        source_gate(HERE, reference)
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        raise
    finally:
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(report, indent=2) + "\n")
    print(json.dumps({key: report[key] for key in ("scope", "mode", "status", "controls")}))


if __name__ == "__main__":
    main()
