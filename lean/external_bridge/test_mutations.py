"""Negative controls for the twenty-five frozen finite source-word bridge targets.

--mode source is portable and checks original source hashes/module/target
coverage only. It is explicitly partial and does not run a statement comparator.
Full mode requires Linux, pinned Lean 4.35.0 and prepared pinned dependencies.
It first requires the positive full twenty-five-target verifier to pass, then runs
actual comparator, axiom-closure and production numeric rejection fixtures.
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
TARGETS = ('ExternalFiniteBridgeChallenge.finiteWordPrefixEncoding', 'ExternalFiniteBridgeChallenge.abstractPrefixCompatibility', 'ExternalFiniteBridgeChallenge.defectBounds', 'ExternalFiniteBridgeChallenge.nonintegralEndpoint', 'ExternalFiniteBridgeChallenge.strictRungCaps', 'ExternalFiniteBridgeChallenge.unitFloorIncrements', 'ExternalFiniteBridgeChallenge.floorIncrementAlphabet', 'ExternalFiniteBridgeChallenge.sourceSlopeFacts', 'ExternalFiniteBridgeChallenge.sourceSlopeNonintegral', 'ExternalFiniteBridgeChallenge.sourceRungsUnbounded', 'ExternalFiniteBridgeChallenge.literalClosingDepth', 'ExternalFiniteBridgeChallenge.sourceLastLetterLowerable', 'ExternalFiniteBridgeChallenge.lowerRaiseTransport', 'ExternalFiniteBridgeChallenge.finitePopulations', 'ExternalFiniteBridgeChallenge.sourceFloorBijection', 'ExternalFiniteBridgeChallenge.sourceDepthBijection', 'ExternalFiniteBridgeChallenge.rewardEndpointInvariant', 'ExternalFiniteBridgeChallenge.rewardRealPower', 'ExternalFiniteBridgeChallenge.sourceDepthReward', 'ExternalFiniteBridgeChallenge.referenceAtRungs', 'ExternalFiniteBridgeChallenge.phaseZeroExtremizer', 'ExternalFiniteBridgeChallenge.uniqueExtremizer', 'ExternalFiniteBridgeChallenge.thresholdCountPreservation', 'ExternalFiniteBridgeChallenge.lengthOneBoundary', 'ExternalFiniteBridgeChallenge.zeroLengthConvention')
SPEC_PINS = {'Definitions.lean': 'cf29376721942a78328491cd910690497f95d381711f0d2e758998fbba9374bc', 'ExpectedTypes.lean': '5ce898eb70690f6f77e26a95cbafb5ef268fa93617ab7418a0b25f6878c34968', 'PrefixDefinitions.lean': 'd7b5cd8b624dae007e3c3dc7f3620260dbfcf2169d0211b0859e18ed58180069', 'BridgeDefinitions.lean': '7a36ebc1e9ff89fcec7ad1fdae1c2d5ae9ee011b06ae110fd4f34999e7df19a7', 'BridgeExpectedTypes.lean': '850dcdd0d75479edaeab1c8d6d336b9099f56511e0b6f5a5125bedfca05838aa', 'BridgeChallenge.lean': '844ac679b7b645ee05e8f4d094abb8ae345373f901799e733a4164d51d75b164'}
OWNED = ('Definitions', 'ExpectedTypes', 'Arithmetic', 'PopulationWeights', 'DepthOneSeries', 'LogRatioIrrational', 'PositiveCeilReturns', 'RungDefinitions', 'RungTransfer', 'SyracuseSlope', 'PrefixDefinitions', 'BridgeDefinitions', 'BridgeExpectedTypes', 'BridgeArithmetic', 'BridgeEncoding', 'BridgeRungs', 'BridgeRewards', 'BridgeTransport', 'BridgeFinite', 'BridgeExtremal', 'BridgeBoundary', 'BridgeSolution')
REQUIRED = tuple(name + ".lean" for name in OWNED) + (
    "BridgeChallenge.lean", "Audit.lean", "verify.py", "inventory.json", "specification.json",
    "owned_modules.json", "comparator.json", "lakefile.toml", "lake-manifest.json",
    "lean-toolchain", "frozen_propositions.json")


FROZEN_RAW_SHA = '3ebd38414d2c39b56178874742869df8768d0495b848341d1cdf3f587de7dd59'
CHECKERS = ("Lean default", "Lean paranoid", "lean4lean", "nanoda", "con-leche", "con-ron")


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
            f"{label} target coverage mismatch: all twenty-five frozen targets are required")


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
    require(specification["frozen_propositions_sha256"] == FROZEN_RAW_SHA,
            "trusted frozen proposition pin changed")
    require(hashlib.sha256((root/"frozen_propositions.json").read_bytes()).hexdigest() == FROZEN_RAW_SHA,
            "original frozen proposition digest mismatch")
    comparator = read_json(root/"comparator.json")
    exact_targets(tuple(comparator["theorem_names"]), "configured")
    require(set(comparator["permitted_axioms"]) == {"propext", "Quot.sound", "Classical.choice"},
            "configured axiom whitelist mismatch")
    owned = tuple(read_json(root/"owned_modules.json"))
    require(len(owned) == len(OWNED) and set(owned) == set(OWNED),
            "owned module coverage mismatch")
    inventory = read_json(root/"inventory.json")
    exact_targets(target_names(inventory["targets"]), "inventory")
    require("test_mutations.py" in inventory["sources_sha256"],
            "negative-control script missing from source inventory")
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


def replace_bridge_wrapper(root, statement, body):
    path = root/"BridgeSolution.lean"
    pattern = (r"(?m)^theorem phaseZeroExtremizer : PhaseZeroExtremizer :=\n"
               r"  ExternalFiniteBridgeExtremal\.phase_zero_extremizer$")
    text, count = re.subn(pattern, f"theorem phaseZeroExtremizer : {statement} := {body}", path.read_text())
    require(count == 1, "phaseZeroExtremizer wrapper mutation anchor missing")
    path.write_text(text)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--mode", choices=("source", "full"), default="full")
    parser.add_argument("--toolchain", type=Path)
    parser.add_argument("--mathlib-cache", type=Path)
    parser.add_argument("--dependency-cache", type=Path)
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = {"scope": "twenty-five frozen finite-word bridge, reward, bijection, maximum and count targets; no pressure or asymptotic claim",
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
        # Exact finite semantic witnesses; no floating logarithms or imported proof code.
        def floor_log2(value):
            require(value > 0, "positive rational needed for floor-log witness")
            exponent = value.numerator.bit_length() - value.denominator.bit_length()
            scale = Fraction(2)**exponent
            while value < scale:
                exponent -= 1; scale /= 2
            while 2*scale <= value:
                exponent += 1; scale *= 2
            return exponent

        def floor_at(t):
            return (3**t).bit_length() - 1

        def ceil_at(t):
            return 0 if t == 0 else floor_at(t) + 1

        def cap(r, t):
            return floor_log2(Fraction(2**ceil_at(r), 3**(r-t)))

        def prefixes(word):
            values = [0]
            for letter in word:
                values.append(values[-1] + letter)
            return values

        def reward(word):
            values = prefixes(word)
            return sum((Fraction(2**values[t], 3**t) for t in range(len(word))), Fraction(0))

        def source_word(word):
            r = len(word); values = prefixes(word)
            return r > 0 and all(k >= 1 for k in word) and values[-1] == ceil_at(r) and all(
                values[t] <= cap(r, t) for t in range(r))

        def rung(r, include_zero=False):
            closing = Fraction(2**ceil_at(r), 3**r)
            return r > 0 and all(closing < Fraction(2**ceil_at(t), 3**t)
                for t in range(0 if include_zero else 1, r))

        source, lowered = (2,), (1,)
        require(source_word(source) and not source_word(lowered), "literal source closing endpoint changed")
        require(reward(source) == reward(lowered) == 1, "endpoint reward invariance witness changed")
        require(floor_at(1)-prefixes(source)[-1] == -1 and
                floor_at(1)-prefixes(lowered)[-1] == 0, "literal/lowered depth witness changed")
        require(rung(1) and not rung(1, include_zero=True), "rung zero-index exclusion witness changed")
        require(not source_word(()) and reward(()) == 0, "zero-length source/reward witness changed")
        require(source_word((1, 3)) and source_word((2, 2)) and not rung(2), "off-rung source witness changed")
        phase_zero = sum((Fraction(2**floor_at(t), 3**t) for t in range(2)), Fraction(0))
        require(phase_zero == reward((1, 3)) == Fraction(5, 3) and reward((2, 2)) == Fraction(7, 3),
                "off-rung reference witness changed")
        # Generic transport's theta>=1 cannot be silently dropped: theta=1/2,r=1 gives word(1).
        theta_half = Fraction(1, 2)
        half_word, half_lowered = (1,), (0,)
        half_ceiling = -(-theta_half.numerator // theta_half.denominator)
        half_defect = Fraction(half_ceiling) - theta_half
        half_prefix = prefixes(half_word)
        require(0 < theta_half < 1 and theta_half.denominator != 1 and
                all(k >= 1 for k in half_word) and half_prefix[-1] == half_ceiling and
                half_prefix[0] <= half_defect.numerator // half_defect.denominator and
                not all(k >= 1 for k in half_lowered), "generic lowerability-domain witness changed")
        report["finite_model_witnesses"] = {
            "length_one": {"source": source, "floor": lowered, "reward": "1",
                "literal_closing_depth": -1, "lowered_closing_depth": 0},
            "rung_one": {"positive_earlier_indices": True, "including_zero": False},
            "zero_length": {"source_admissible": False, "reward": "0"},
            "off_rung_two": {"words": [(1, 3), (2, 2)], "rewards": ["5/3", "7/3"],
                "phase_zero_reference": "5/3", "rung": False},
            "generic_half_slope": {"theta": "1/2", "length": 1, "source_word": [1],
                "lowered_word": [0], "positive_after_lowering": False},
            "scope": "exact finite semantic witnesses, not infinite proofs or comparator controls"}
        with tempfile.TemporaryDirectory(prefix="bridge-negative-controls-") as temporary:
            base = Path(temporary)
            log_root = (args.report.resolve().parent/(args.report.stem + "-logs")) if args.report else Path(tempfile.mkdtemp(prefix="bridge-negative-logs-"))
            log_root.mkdir(parents=True, exist_ok=True)
            report["logs_directory"] = str(log_root)

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
                module_spec = importlib.util.spec_from_file_location("trusted_bridge_positive_verifier", HERE/"verify.py")
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
                run(positive, "positive full twenty-five-target pipeline", command)
                receipt = read_json(positive_report)
                require(receipt.get("mode") == "full" and receipt.get("status") == "passed bridge full assurance gates",
                        "positive full verifier did not report completed full assurance")
                exact_targets(target_names(receipt["targets"]), "positive full receipt")
                for label in ("complete proof closure", "frozen statement comparison"):
                    require(receipt.get("checker_coverage", {}).get(label) == list(CHECKERS),
                            f"positive full receipt lacks six-checker coverage: {label}")
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

            source_rejection("positive letters weakened to allow zero", lambda root: replace_once(root/"BridgeDefinitions.lean",
                "def PositiveWord (r : ℕ) (w : Word r) : Prop := ∀ i, 1 ≤ w i",
                "def PositiveWord (r : ℕ) (w : Word r) : Prop := ∀ i, 0 ≤ w i"),
                "original frozen source digest mismatch: BridgeDefinitions.lean")
            source_rejection("source ceiling endpoint replaced by floor", lambda root: replace_once(root/"BridgeDefinitions.lean",
                "wordPrefix r w (Fin.last r) = Int.ceil ((r : ℝ) * θ)",
                "wordPrefix r w (Fin.last r) = floorAt θ r"),
                "original frozen source digest mismatch: BridgeDefinitions.lean")
            source_rejection("zero index inserted into strict rung records", lambda root: replace_once(root/"BridgeDefinitions.lean",
                "∀ t : ℕ, 0 < t → t < r → defect θ r < defect θ t",
                "∀ t : ℕ, t < r → defect θ r < defect θ t"),
                "original frozen source digest mismatch: BridgeDefinitions.lean")
            source_rejection("source depth omits required last-letter lowering", lambda root: replace_once(root/"BridgeDefinitions.lean",
                "wordDepth θ r (lowerLast r w)", "wordDepth θ r w"),
                "original frozen source digest mismatch: BridgeDefinitions.lean")
            source_rejection("literal reward rescaled by factor two", lambda root: replace_once(root/"BridgeDefinitions.lean",
                "∑ t : Fin r, (2 : ℝ) ^ wordPrefix r w t.castSucc / (3 : ℝ) ^ t.val",
                "2 * (∑ t : Fin r, (2 : ℝ) ^ wordPrefix r w t.castSucc / (3 : ℝ) ^ t.val)"),
                "original frozen source digest mismatch: BridgeDefinitions.lean")
            source_rejection("generic last-letter domain bound dropped", lambda root: replace_once(root/"BridgeExpectedTypes.lean",
                "def SourceLastLetterLowerable : Prop := ∀ θ r (w : Word r), 1 ≤ θ →",
                "def SourceLastLetterLowerable : Prop := ∀ θ r (w : Word r),"),
                "original frozen source digest mismatch: BridgeExpectedTypes.lean")
            source_rejection("required finite population module dropped", lambda root: (root/"BridgeFinite.lean").unlink(),
                "missing required module/config: BridgeFinite.lean")

            def drop_configured_target(root):
                path = root/"comparator.json"; data = read_json(path)
                data["theorem_names"].remove("ExternalFiniteBridgeChallenge.zeroLengthConvention")
                path.write_text(json.dumps(data, indent=2) + "\n")

            def drop_inventory_target(root):
                path = root/"inventory.json"; data = read_json(path)
                rows = data["targets"]
                if isinstance(rows, dict):
                    del rows["ExternalFiniteBridgeChallenge.zeroLengthConvention"]
                else:
                    data["targets"] = [row for row in rows if
                        (row if isinstance(row, str) else row["declaration"]) != "ExternalFiniteBridgeChallenge.zeroLengthConvention"]
                path.write_text(json.dumps(data, indent=2) + "\n")

            source_rejection("configured target silently skipped", drop_configured_target, "configured target coverage mismatch")
            source_rejection("inventory target silently skipped", drop_inventory_target, "inventory target coverage mismatch")

            def drop_raw_proposition(root):
                path = root/"frozen_propositions.json"; data = read_json(path)
                require(isinstance(data, list) and len(data) == 25, "frozen raw register shape changed")
                path.write_text(json.dumps(data[:-1], indent=2) + "\n")
            source_rejection("frozen proposition silently skipped", drop_raw_proposition,
                "original frozen proposition digest mismatch")

            if args.mode == "full":
                wrong = fixture("wrong-bridge-statement")
                prepare(wrong)
                replace_bridge_wrapper(wrong, "True", "by trivial")
                run(wrong, "wrong-statement positive compilation", [lake, "build"])
                expected = "Challenge and solution theorem statement do not match: 'ExternalFiniteBridgeChallenge.phaseZeroExtremizer'"
                run(wrong, "wrong statement rejected by actual comparator",
                    [lake, "comparator", "--config", "comparator.json", "--paranoid"],
                    reject=(1, lambda text: expected in text))
                report["controls"].append({"name": "finite extremizer wrapper weakened to True",
                    "gate": "actual trusted elaborated statement comparator", "result": "rejected",
                    "mutated_solution_sha256": hashlib.sha256((wrong/"BridgeSolution.lean").read_bytes()).hexdigest()})
                shutil.rmtree(wrong)

                axiom = fixture("hidden-imported-custom-axiom")
                prepare(axiom)
                (axiom/"BadPremise.lean").write_text(
                    "import BridgeExpectedTypes\nnamespace BadPremise\n"
                    "axiom hiddenMaximum : ExternalFiniteBridgeDraft.PhaseZeroExtremizer\nend BadPremise\n")
                with (axiom/"lakefile.toml").open("a") as stream:
                    stream.write('\n[[lean_lib]]\nname = "BadPremise"\n')
                replace_bridge_wrapper(axiom, "PhaseZeroExtremizer", "BadPremise.hiddenMaximum")
                solution = axiom/"BridgeSolution.lean"
                solution.write_text("import BadPremise\n" + solution.read_text())
                run(axiom, "custom-axiom positive compilation", [lake, "build"])
                run(axiom, "hidden imported custom axiom rejected by all-closure audit",
                    [lake, "env", "lean", "-DwarningAsError=true", "Audit.lean"],
                    reject=(1, lambda text: "forbidden axiom" in text.lower() and "BadPremise.hiddenMaximum" in text))
                report["controls"].append({"name": "hidden imported custom axiom",
                    "gate": "actual all-origin transitive axiom closure audit", "result": "rejected",
                    "mutated_solution_sha256": hashlib.sha256((axiom/"BridgeSolution.lean").read_bytes()).hexdigest(),
                    "hidden_premise_sha256": hashlib.sha256((axiom/"BadPremise.lean").read_bytes()).hexdigest()})
                shutil.rmtree(axiom)

                arithmetic = fixture("corrupted-source-slope")
                prepare(arithmetic)
                run(arithmetic, "numeric source-slope prerequisites", [lake, "build", "RungTransfer", "LogRatioIrrational"])
                original = (arithmetic/"SyracuseSlope.lean").read_text()
                boundary = "theorem source_closing"
                require(original.count(boundary) == 1, "production slope slice boundary changed")
                proof_slice = original[:original.index(boundary)] + "\nend ExternalSyracuseSlope\n"
                anchor = "((2 : ℝ) ^ 2)"
                require(proof_slice.count(anchor) == 1, "production slope inequality anchor changed")
                require(2**1 < 3 < 2**2, "original/corrupt exact integer inequality changed")
                positive = arithmetic/"SlopePositive.lean"
                positive.write_text(proof_slice)
                run(arithmetic, "positive production source-slope proof",
                    [lake, "env", "lean", "-DwarningAsError=true", "-R", str(arithmetic), str(positive)])
                corrupt = proof_slice.replace(anchor, "((2 : ℝ) ^ 1)", 1)
                negative = arithmetic/"SlopeCorrupt.lean"
                negative.write_text(corrupt)
                run(arithmetic, "corrupt slope bound rejected by actual production Lean proof",
                    [lake, "env", "lean", "-DwarningAsError=true", "-R", str(arithmetic), str(negative)],
                    reject=(1, lambda text: "unsolved goals" in text and "False" in text))
                report["controls"].append({"name": "production slope exponent two changed to one",
                    "gate": "actual Lean production theta_lt_two proof slice", "result": "rejected",
                    "positive_source_sha256": hashlib.sha256(proof_slice.encode()).hexdigest(),
                    "corrupt_source_sha256": hashlib.sha256(corrupt.encode()).hexdigest(),
                    "exact_inequalities": "2^1 < 3 < 2^2"})
                report["status"] = "passed bridge negative controls and positive full twenty-five-target pipeline"
            else:
                report["status"] = "partial: portable original-source/hash/coverage controls passed"
                report["not_executed"] = ["positive full twenty-five-target pipeline", "trusted statement comparator rejection",
                    "actual custom-axiom closure rejection", "actual corrupted source-slope Lean proof rejection",
                    "sandboxed imported-proof replay", "independent kernel replay"]
                report["semantic_note"] = (
                    "Portable controls reject original-source/hash/coverage changes only; they are not statement comparisons. "
                    "The exact finite model witnesses separately exercise endpoint, depth, reward, rung and domain conventions.")
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
    print(json.dumps({key: report[key] for key in ("scope", "mode", "status", "controls", "logs_directory")}))


if __name__ == "__main__":
    main()
