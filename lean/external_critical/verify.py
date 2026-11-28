"""Clean public critical-space supporting build; full mode requires every replay/comparator/checker gate.

Fetch public dependencies before running this verifier. This program never runs
lake update or the cache downloader. Build mode is explicitly lower assurance.
"""
from __future__ import annotations
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import time
import sys

HERE = Path(__file__).resolve().parent
MATHLIB_COMMIT = "56a005855ea17e0b0958f73ec801ae140b0a1679"
OWNED_MODULES = ('PrefixDefinitions', 'BridgeDefinitions', 'BridgeExpectedTypes', 'PressureDefinitions', 'PressureExpectedTypes', 'CriticalSpaceDefinitions', 'CriticalSpaceExpectedTypes', 'SpaceTopology', 'SpaceArithmetic', 'SpaceReward', 'PhaseCocycle', 'RootedLaw', 'WeakReward', 'RootedShift', 'RootedStationary', 'StationaryEvents', 'FiniteInfinity', 'GapPacking', 'ExcursionMoment', 'PolynomialContradiction', 'CriticalSolution')
TARGETS = ('ExternalCriticalSupportChallenge.space_topology', 'ExternalCriticalSupportChallenge.phase_representative_law', 'ExternalCriticalSupportChallenge.shift_group_and_continuity', 'ExternalCriticalSupportChallenge.reward_roof_and_regularity', 'ExternalCriticalSupportChallenge.weak_reward_passage', 'ExternalCriticalSupportChallenge.rooted_normalization', 'ExternalCriticalSupportChallenge.root_shift_error', 'ExternalCriticalSupportChallenge.rooted_stationary_subsequence', 'ExternalCriticalSupportChallenge.finite_infinity_exclusion', 'ExternalCriticalSupportChallenge.gap_packing', 'ExternalCriticalSupportChallenge.excursion_first_moment', 'ExternalCriticalSupportChallenge.polynomial_excursion_contradiction')
FROZEN_SOURCES = {'PrefixDefinitions.lean': 'd7b5cd8b624dae007e3c3dc7f3620260dbfcf2169d0211b0859e18ed58180069', 'BridgeDefinitions.lean': '7a36ebc1e9ff89fcec7ad1fdae1c2d5ae9ee011b06ae110fd4f34999e7df19a7', 'BridgeExpectedTypes.lean': '850dcdd0d75479edaeab1c8d6d336b9099f56511e0b6f5a5125bedfca05838aa', 'PressureDefinitions.lean': '07d60f44e7aaa3107518678bb1780b4867a37f07c3db9b49e89f9402c8b45cd4', 'PressureExpectedTypes.lean': '9aa83c42cf2ccb23490ce84da1b21b9d6de0fb26dbf435d21b4d27bcc215f015', 'CriticalSpaceDefinitions.lean': 'f9316997df40811d6ce24d9aec17a8315ad5db8dce318c8373803e62a7fec1a5', 'CriticalSpaceExpectedTypes.lean': 'a5c9be218477466352bd567e073702529e40d00e0b28b17811ea1b1a99a86df0', 'CriticalChallenge.lean': 'c05082f91b7b98b292331482ab0cc2f109b4fb674a46bbc0981c658ce2b977fd'}
AXIOMS = ("propext", "Quot.sound", "Classical.choice")
CHECKERS = ("Lean default", "Lean paranoid", "lean4lean", "nanoda", "con-leche", "con-ron")


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


EXPECTED_HELPER_COUNT = 379
MODEL_NAMES = ('ExternalCriticalSpaceDraft.Config', 'ExternalCriticalSpaceDraft.HasUniformPhase', 'ExternalCriticalSpaceDraft.Height', 'ExternalCriticalSpaceDraft.IsStationary', 'ExternalCriticalSpaceDraft.Phase', 'ExternalCriticalSpaceDraft.allFinite', 'ExternalCriticalSpaceDraft.allInfinite', 'ExternalCriticalSpaceDraft.configBorelSpace', 'ExternalCriticalSpaceDraft.configMeasurableSpace', 'ExternalCriticalSpaceDraft.finiteHeightSet', 'ExternalCriticalSpaceDraft.forbiddenUpwardCylinder', 'ExternalCriticalSpaceDraft.heightBorelSpace', 'ExternalCriticalSpaceDraft.heightMeasurableSpace', 'ExternalCriticalSpaceDraft.heightWeight', 'ExternalCriticalSpaceDraft.heightWeight._proof_1', 'ExternalCriticalSpaceDraft.instDecidable_criticalSpaceDefinitions', 'ExternalCriticalSpaceDraft.localReward', 'ExternalCriticalSpaceDraft.longExcursion', 'ExternalCriticalSpaceDraft.lowEvent', 'ExternalCriticalSpaceDraft.phaseRepresentative', 'ExternalCriticalSpaceDraft.phaseRepresentative._proof_1', 'ExternalCriticalSpaceDraft.phaseRotation', 'ExternalCriticalSpaceDraft.rootedConfig', 'ExternalCriticalSpaceDraft.rootedConfig._proof_1', 'ExternalCriticalSpaceDraft.rootedConfig._proof_2', 'ExternalCriticalSpaceDraft.rootedMeasure', 'ExternalCriticalSpaceDraft.rootedMeasure._proof_1', 'ExternalCriticalSpaceDraft.shiftedGap', 'ExternalCriticalSpaceDraft.successiveGap', 'ExternalCriticalSpaceDraft.timeShift', 'ExternalCriticalSpaceDraft.uniformPhase', 'ExternalCriticalSpaceDraft.uniformPhase._proof_1')
FROZEN_PROPOSITIONS_SHA256 = '1abfed9de8a7ddd7db4024042da50c1d7f2197bd5fdf9895daed7f0b4220926d'
FROZEN_MODELS_SHA256 = '83384e950c217fe0f6ffd1f3e4b736f82ff371160453c4665003fe143a7626da'


def source_gate(root, inventory=None):
    """Fail closed on exact meanings and complete owned/target/helper/model coverage."""
    root = Path(root)
    inventory = inventory or json.loads((root/"inventory.json").read_text())
    expected = {m+".lean" for m in OWNED_MODULES} | {"CriticalChallenge.lean", "Audit.lean"}
    require(inventory.get("owned_modules") == list(OWNED_MODULES), "inventory owned module coverage mismatch")
    require(len(inventory["targets"]) == 12 and sorted(x["declaration"] for x in inventory["targets"]) == sorted(TARGETS), "inventory target coverage mismatch")
    helpers = [x["declaration"] for x in inventory["helpers"]]
    require(len(helpers) == EXPECTED_HELPER_COUNT and len(set(helpers)) == EXPECTED_HELPER_COUNT and not set(helpers)&set(TARGETS), "inventory helper coverage mismatch")
    require(all(x["module"] in OWNED_MODULES for x in inventory["targets"]+inventory["helpers"]), "inventory declaration module mismatch")
    require(len(inventory["models"]) == 32 and sorted(x["declaration"] for x in inventory["models"]) == sorted(MODEL_NAMES), "inventory model coverage mismatch")
    required = expected | {"verify.py", "README.md", "ARGUMENT.md", "comparator.json", "owned_modules.json", "specification.json", "frozen_propositions.json", "frozen_models.json", "lake-manifest.json", "lakefile.toml", "lean-toolchain", "cache-imports.txt", "test_mutations.py", "provenance.json"}
    require(required <= set(inventory["sources_sha256"]), "source inventory coverage mismatch")
    actual = {p.name for p in root.glob("*.lean")}
    require(actual == expected, f"owned Lean module coverage mismatch: {sorted(actual ^ expected)}")
    for name, pin in FROZEN_SOURCES.items():
        require(digest(root/name) == pin, f"frozen source digest mismatch: {name}")
    require(json.loads((root/"owned_modules.json").read_text()) == list(OWNED_MODULES), "owned module register mismatch")
    config = json.loads((root/"comparator.json").read_text())
    require(config["theorem_names"] == list(TARGETS), "frozen target register mismatch")
    require(config["challenge_module"] == "CriticalChallenge" and config["solution_module"] == "CriticalSolution", "comparator module mismatch")
    require(config["permitted_axioms"] == list(AXIOMS), "axiom policy mismatch")
    require(config.get("external_kernels") == {"nanoda": ["nanoda_bin"]}, "independent checker configuration mismatch")
    require(config.get("definition_names") == [], "unexpected definition holes")
    specification = json.loads((root/"specification.json").read_text())
    require(specification["frozen_propositions_sha256"] == FROZEN_PROPOSITIONS_SHA256 and digest(root/"frozen_propositions.json") == FROZEN_PROPOSITIONS_SHA256, "frozen raw proposition register mismatch")
    require(specification["frozen_model_definitions_sha256"] == FROZEN_MODELS_SHA256 and digest(root/"frozen_models.json") == FROZEN_MODELS_SHA256, "frozen raw model register mismatch")
    require(set(specification["files"]) == set(FROZEN_SOURCES) and all(specification["files"][n]["sha256"] == pin for n,pin in FROZEN_SOURCES.items()), "original frozen specification pin mismatch")
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
    report = {"scope": "all12 compact critical-space supporting targets; no full critical law",
              "mode": args.mode, "status": "running", "steps": []}
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "PYTHONOPTIMIZE"):
        env.pop(key, None)
    if args.toolchain:
        env["PATH"] = str(args.toolchain.resolve()/"bin")+os.pathsep+env.get("PATH", "")
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    lake = shutil.which("lake", path=env.get("PATH"))
    log_directory = Path(tempfile.mkdtemp(prefix="critical-verifier-logs-")) if args.report is None else None

    def save():
        if args.report:
            args.report.parent.mkdir(parents=True, exist_ok=True)
            args.report.write_text(json.dumps(report, indent=2)+"\n")

    try:
        source_gate(HERE)
        if args.mode == "full":
            require(sys.platform.startswith("linux"), "full assurance requires Linux sandbox support; no full gate passed")
        require(lake is not None, "lake unavailable; install pinned Lean or pass --toolchain")
        inventory = json.loads((HERE/"inventory.json").read_text())
        with tempfile.TemporaryDirectory(prefix="collatz-public-critical-") as temporary:
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
                            "status": "passed" if result.returncode == 0 else "failed"})
                evidence_dir = (args.report.parent/(args.report.stem+".logs")) if args.report else log_directory
                evidence_dir.mkdir(parents=True, exist_ok=True)
                for stream_name, value in (("stdout", result.stdout), ("stderr", result.stderr)):
                    data = value.encode()
                    row[stream_name+"_sha256"] = hashlib.sha256(data).hexdigest()
                    row[stream_name+"_bytes"] = len(data)
                    row[stream_name] = value[:4000]
                    if data:
                        name = f"{len(report['steps'])-1:02d}-" + re.sub(r"[^a-z0-9]+", "-", label.lower()).strip("-") + "."+stream_name+".txt.gz"
                        evidence = evidence_dir/name
                        evidence.write_bytes(gzip.compress(data, mtime=0))
                        row[stream_name+"_gzip"] = str(evidence)
                        row[stream_name+"_gzip_sha256"] = digest(evidence)
                save()
                require(result.returncode == 0, f"required gate failed: {label}")
                print(f"PASS {label} ({row['seconds']}s)", flush=True)
                return result.stdout

            version = run("pinned toolchain", [lake, "env", "lean", "--version"])
            require("version 4.35.0," in version, "wrong critical toolchain")
            build = run("all own source clean build", [lake, "build"])
            require("warning:" not in build + report["steps"][-1]["stderr"], "own build emitted a warning")
            missing = [m for m in OWNED_MODULES if not (root/f".lake/build/lib/lean/{m}.olean").is_file()]
            require(not missing, f"own modules omitted from build: {missing}")
            source_gate(root, inventory)
            audit = run("all own theorem closures and raw frozen target types",
                        [lake, "env", "lean", "-DwarningAsError=true", "-R", str(root), "-o", str(root/".lake/build/lib/lean/Audit.olean"), "Audit.lean"])
            meta = [json.loads(x.removeprefix("CRITICAL_TARGET ")) for x in audit.splitlines()
                    if x.startswith("CRITICAL_TARGET ")]
            closures = [json.loads(x.removeprefix("CRITICAL_SUPPORT ")) for x in audit.splitlines()
                        if x.startswith("CRITICAL_SUPPORT ")]
            model_rows = [json.loads(x.removeprefix("CRITICAL_MODEL ")) for x in audit.splitlines() if x.startswith("CRITICAL_MODEL ")]
            frozen_models = json.loads((root/"frozen_models.json").read_text())
            require(len(model_rows) == 32 and sorted(model_rows,key=lambda x:x["declaration"]) == sorted(frozen_models,key=lambda x:x["declaration"]), "canonical frozen model body/type mismatch")
            require(sorted(model_rows,key=lambda x:x["declaration"]) == inventory["models"], "model body inventory mismatch")
            by_name = {x["declaration"]: x for x in closures}
            targets = [by_name[x["declaration"]] | x for x in meta]
            helpers = [x for x in closures if x["declaration"] not in TARGETS]
            frozen = {row["declaration"]: row for row in json.loads((root/"frozen_propositions.json").read_text())}
            require(all(row["raw_expected_proposition"] == frozen[row["expected"]]["raw_proposition"] for row in targets),
                    "canonical frozen proposition body mismatch")
            targets.sort(key=lambda x:x["declaration"])
            helpers.sort(key=lambda x:x["declaration"])
            require([x["declaration"] for x in targets] == sorted(TARGETS), "missing frozen target implementation")
            require(targets == inventory["targets"], "elaborated frozen target inventory mismatch")
            require(helpers == inventory["helpers"], "own generated-helper inventory mismatch")
            report.update({"targets": targets, "helpers": helpers, "models": model_rows, "own_module_count": len(OWNED_MODULES),
                           "own_declaration_count": len(targets)+len(helpers)})
            if args.mode == "full":
                roots = sorted({x["declaration"] for x in targets+helpers})
                export = root/".lake/critical-complete-proof-closure.ndjson"
                command = [lake, "env", "leanexport", "Audit", "--", *roots]
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
                replay = run("fresh complete proof-closure replay and all bundled checkers",
                    [lake, "check", "--from-export", export, "--paranoid"])
                comparison = run("all12 frozen statements and independent checker",
                    [lake, "comparator", "--config", "comparator.json", "--paranoid"])
                coverage = {}
                for label, output in (("complete proof closure", replay), ("frozen statement comparison", comparison)):
                    accepted = [name for name in CHECKERS if f"{name} kernel accepts the solution" in output]
                    require(accepted == list(CHECKERS), f"missing required six-checker coverage: {label}")
                    coverage[label] = accepted
                report["checker_coverage"] = coverage
                report["status"] = "passed critical full assurance gates"
            else:
                report["status"] = "partial: clean critical build and axiom audit only"
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
