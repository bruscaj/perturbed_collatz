"""Negative controls for the twenty-two frozen finite-depth density targets.

--mode source is portable and checks original source hashes/module/target
coverage only. It is explicitly partial and does not run a statement comparator.
Full mode requires Linux, pinned Lean 4.35.0 and prepared pinned dependencies.
It first requires the positive full twenty-two-target verifier to pass, then runs
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
TARGETS = ('ExternalO3GeneralChallenge.blocksWellDefined', 'ExternalO3GeneralChallenge.windowValidity', 'ExternalO3GeneralChallenge.windowTransport', 'ExternalO3GeneralChallenge.correctionRestriction', 'ExternalO3GeneralChallenge.fixedPointAndZero', 'ExternalO3GeneralChallenge.refinedCylinderClasses', 'ExternalO3GeneralChallenge.refinedCylinderDensities', 'ExternalO3GeneralChallenge.refinedLabelCell', 'ExternalO3GeneralChallenge.refinedWeightLaw', 'ExternalO3GeneralChallenge.refinementProjectionLaw', 'ExternalO3GeneralChallenge.coarseMarginalLaw', 'ExternalO3GeneralChallenge.weightLaw', 'ExternalO3GeneralChallenge.coordinateLaw', 'ExternalO3GeneralChallenge.labelRealizable', 'ExternalO3GeneralChallenge.literalGainIdentity', 'ExternalO3GeneralChallenge.cellStabilization', 'ExternalO3GeneralChallenge.selectedMassSummable', 'ExternalO3GeneralChallenge.densityExists', 'ExternalO3GeneralChallenge.densityEqualsSymbolic', 'ExternalO3GeneralChallenge.densityUnique', 'ExternalO3GeneralChallenge.sourceDensityEquivalence', 'ExternalO3GeneralChallenge.depthOneCompatibility')
SPEC_PINS = {'Definitions.lean': 'cf29376721942a78328491cd910690497f95d381711f0d2e758998fbba9374bc', 'ExpectedTypes.lean': '5ce898eb70690f6f77e26a95cbafb5ef268fa93617ab7418a0b25f6878c34968', 'GeneralDefinitions.lean': '9d3f21078449309feb93e42b2d2b5fc8c5f0c48c4ff42ac7b62fc5d911c2decc', 'GeneralExpectedTypes.lean': '65087d9a25b910c2875c128d9c477cab9b5e506629d446f5db193450dad3b8fa', 'GeneralChallenge.lean': '149002f98a102ad1a123204781d575ed2acbb6354f655ad66dfde79fa159c1ff'}
OWNED = ('Definitions', 'ExpectedTypes', 'Arithmetic', 'PopulationWeights', 'Progressions', 'Cylinders', 'ExitCylinders', 'Gains', 'CountablePartition', 'PartitionGeneral', 'DensityBounds', 'SourceDensity', 'GeneralDefinitions', 'GeneralExpectedTypes', 'GeneralArithmetic', 'GeneralCompatibility', 'GeneralPreimage', 'GeneralStrideWords', 'GeneralBlockWords', 'GeneralCylinderDensity', 'GeneralRefinementLabels', 'GeneralWeights', 'GeneralMarginal', 'GeneralProjection', 'GeneralGains', 'GeneralSourceDensity', 'GeneralDensity', 'GeneralSolution')
REQUIRED = tuple(name + ".lean" for name in OWNED) + (
    "GeneralChallenge.lean", "Audit.lean", "verify.py", "inventory.json", "specification.json",
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
            f"{label} target coverage mismatch: all twenty-two frozen targets are required")


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


def replace_density_wrapper(root, statement, body):
    path = root/"GeneralSolution.lean"
    pattern = r"(?m)^theorem densityExists : [^\n]+$"
    text, count = re.subn(pattern, f"theorem densityExists : {statement} := {body}", path.read_text())
    require(count == 1, "densityExists wrapper mutation anchor missing")
    path.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("source", "full"), default="full")
    parser.add_argument("--toolchain", type=Path)
    parser.add_argument("--mathlib-cache", type=Path)
    parser.add_argument("--dependency-cache", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = {"scope": "twenty-two frozen fixed finite-depth density targets; no optimization or rate theorem",
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
        with tempfile.TemporaryDirectory(prefix="population-negative-controls-") as temporary:
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
                run(positive, "positive full twenty-two-target pipeline", command)
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

            source_rejection("failure equality changed to strict", lambda root: replace_once(root/"GeneralDefinitions.lean",
                "rawPotential h φ (ExternalO3Spec.stride x) ≥ rawPotential h φ x", "rawPotential h φ (ExternalO3Spec.stride x) > rawPotential h φ x"),
                "original frozen source digest mismatch: GeneralDefinitions.lean")
            source_rejection("odd-seed normalization factor changed", lambda root: replace_once(root/"GeneralDefinitions.lean",
                "(failureCount h φ N : ℝ) / (N : ℝ)", "(failureCount h φ N : ℝ) / (2 * (N : ℝ))"),
                "original frozen source digest mismatch: GeneralDefinitions.lean")
            source_rejection("corrections restricted to bounded functions", lambda root: replace_once(root/"GeneralDefinitions.lean",
                "abbrev Correction (h : Depth) := Window h → ℝ", "abbrev Correction (h : Depth) := { f : Window h → ℝ // ∃ C : ℝ, ∀ w, |f w| ≤ C }"),
                "original frozen source digest mismatch: GeneralDefinitions.lean")
            source_rejection("required marginal module dropped", lambda root: (root/"GeneralMarginal.lean").unlink(),
                "missing required module/config: GeneralMarginal.lean")

            def drop_configured_target(root):
                path = root/"comparator.json"; data = read_json(path)
                data["theorem_names"].remove("ExternalO3GeneralChallenge.depthOneCompatibility")
                path.write_text(json.dumps(data, indent=2) + "\n")

            def drop_inventory_target(root):
                path = root/"inventory.json"; data = read_json(path)
                rows = data["targets"]
                if isinstance(rows, dict):
                    del rows["ExternalO3GeneralChallenge.depthOneCompatibility"]
                else:
                    data["targets"] = [row for row in rows if
                        (row if isinstance(row, str) else row["declaration"]) != "ExternalO3GeneralChallenge.depthOneCompatibility"]
                path.write_text(json.dumps(data, indent=2) + "\n")

            source_rejection("configured target silently skipped", drop_configured_target, "configured target coverage mismatch")
            source_rejection("inventory target silently skipped", drop_inventory_target, "inventory target coverage mismatch")

            if args.mode == "full":
                wrong = fixture("wrong-density-statement")
                prepare(wrong)
                replace_density_wrapper(wrong, "True", "by trivial")
                run(wrong, "wrong-statement positive compilation", [lake, "build"])
                expected = "Challenge and solution theorem statement do not match: 'ExternalO3GeneralChallenge.densityExists'"
                run(wrong, "wrong statement rejected by actual comparator",
                    [lake, "comparator", "--config", "comparator.json", "--paranoid"],
                    reject=(1, lambda text: expected in text))
                report["controls"].append({"name": "density wrapper weakened to True",
                    "gate": "actual trusted elaborated statement comparator", "result": "rejected",
                    "mutated_solution_sha256": hashlib.sha256((wrong/"GeneralSolution.lean").read_bytes()).hexdigest()})
                shutil.rmtree(wrong)

                axiom = fixture("hidden-imported-custom-axiom")
                prepare(axiom)
                (axiom/"BadPremise.lean").write_text(
                    "import GeneralExpectedTypes\nnamespace BadPremise\n"
                    "axiom hiddenFormula : ExternalO3GeneralDraft.DensityExists\nend BadPremise\n")
                with (axiom/"lakefile.toml").open("a") as stream:
                    stream.write('\n[[lean_lib]]\nname = "BadPremise"\n')
                replace_density_wrapper(axiom, "DensityExists", "BadPremise.hiddenFormula")
                solution = axiom/"GeneralSolution.lean"
                solution.write_text("import BadPremise\n" + solution.read_text())
                run(axiom, "custom-axiom positive compilation", [lake, "build"])
                run(axiom, "hidden imported custom axiom rejected by all-closure audit",
                    [lake, "env", "lean", "-DwarningAsError=true", "Audit.lean"],
                    reject=(1, lambda text: "forbidden axiom" in text.lower() and "BadPremise.hiddenFormula" in text))
                report["controls"].append({"name": "hidden imported custom axiom",
                    "gate": "actual all-origin transitive axiom closure audit", "result": "rejected",
                    "mutated_solution_sha256": hashlib.sha256((axiom/"GeneralSolution.lean").read_bytes()).hexdigest(),
                    "hidden_premise_sha256": hashlib.sha256((axiom/"BadPremise.lean").read_bytes()).hexdigest()})
                shutil.rmtree(axiom)

                arithmetic = fixture("corrupted-block-exponent")
                prepare(arithmetic)
                run(arithmetic, "block-word prerequisites", [lake, "build", "GeneralArithmetic", "GeneralStrideWords"])
                original = (arithmetic/"GeneralBlockWords.lean").read_text()
                positive = arithmetic/"BlockWordPositive.lean"
                positive.write_text(original)
                run(arithmetic, "positive production block-word proof",
                    [lake, "env", "lean", "-DwarningAsError=true", "-R", str(arithmetic), str(positive)])
                anchor = "∑ i : Fin m, (lengths i.castSucc - 1 + exits i)"
                require(original.count(anchor) == 1, "block exponent mutation anchor changed")
                corrupt = original.replace(anchor, "∑ i : Fin m, (lengths i.castSucc + exits i)", 1)
                wrong_word = arithmetic/"CorruptedBlockWord.lean"
                wrong_word.write_text(corrupt)
                run(arithmetic, "wrong block exponent rejected by actual Lean production proof",
                    [lake, "env", "lean", "-DwarningAsError=true", "-R", str(arithmetic), str(wrong_word)],
                    reject=(1, lambda text: "unsolved goals" in text))
                report["controls"].append({"name": "completed-block exponent omits subtraction of one",
                    "gate": "actual Lean production block-word proof", "result": "rejected",
                    "positive_source_sha256": hashlib.sha256(original.encode()).hexdigest(),
                    "corrupt_source_sha256": hashlib.sha256(corrupt.encode()).hexdigest()})
                report["status"] = "passed population negative controls and positive full twenty-two-target pipeline"
            else:
                report["status"] = "partial: portable original-source/hash/coverage controls passed"
                report["not_executed"] = ["positive full twenty-two-target pipeline", "trusted statement comparator rejection",
                    "actual custom-axiom closure rejection", "actual corrupted block-exponent Lean proof rejection",
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
