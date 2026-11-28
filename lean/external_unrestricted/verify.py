"""Clean public all-length fixed-reference count build; full mode requires every replay/comparator/checker gate.

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
OWNED_MODULES = ('Definitions', 'ExpectedTypes', 'Arithmetic', 'PopulationWeights', 'DepthOneSeries', 'LogRatioIrrational', 'PositiveCeilReturns', 'PrefixDefinitions', 'RungDefinitions', 'RungTransfer', 'SyracuseSlope', 'BridgeDefinitions', 'BridgeExpectedTypes', 'BridgeArithmetic', 'BridgeEncoding', 'BridgeRungs', 'BridgeRewards', 'BridgeTransport', 'BridgeFinite', 'BridgeExtremal', 'BridgeBoundary', 'BridgeSolution', 'UnrestrictedDefinitions', 'UnrestrictedExpectedTypes', 'UnrestrictedCounts', 'UnrestrictedCountBound', 'UnrestrictedRotation', 'UnrestrictedSwaps', 'UnrestrictedCanonical', 'UnrestrictedInjection', 'UnrestrictedLimits', 'UnrestrictedSolution')
TARGETS = ('ExternalM4UnrestrictedChallenge.slopeBounds', 'ExternalM4UnrestrictedChallenge.tripleRotationHighLow', 'ExternalM4UnrestrictedChallenge.highPhaseCountLower', 'ExternalM4UnrestrictedChallenge.largeDefectsUnbounded', 'ExternalM4UnrestrictedChallenge.canonicalPrefixLaw', 'ExternalM4UnrestrictedChallenge.canonicalAllLengthWord', 'ExternalM4UnrestrictedChallenge.canonicalAlphabetAndSites', 'ExternalM4UnrestrictedChallenge.manyDisjointCanonicalSites', 'ExternalM4UnrestrictedChallenge.swapPrefixLaw', 'ExternalM4UnrestrictedChallenge.swapPreservesSource', 'ExternalM4UnrestrictedChallenge.swapFamilyInjective', 'ExternalM4UnrestrictedChallenge.swapCubeCard', 'ExternalM4UnrestrictedChallenge.swapRewardIdentity', 'ExternalM4UnrestrictedChallenge.canonicalRewardBudget', 'ExternalM4UnrestrictedChallenge.canonicalSwapLossBound', 'ExternalM4UnrestrictedChallenge.largeDefectWitnessInjection', 'ExternalM4UnrestrictedChallenge.exponentialCountLower', 'ExternalM4UnrestrictedChallenge.rungCountOne', 'ExternalM4UnrestrictedChallenge.allLengthCountBounds', 'ExternalM4UnrestrictedChallenge.normalizedLogBounds', 'ExternalM4UnrestrictedChallenge.normalizedLogLiminf', 'ExternalM4UnrestrictedChallenge.normalizedLogLimsup', 'ExternalM4UnrestrictedChallenge.noAllLengthLimit')
FROZEN_SOURCES = {'Definitions.lean': 'cf29376721942a78328491cd910690497f95d381711f0d2e758998fbba9374bc', 'ExpectedTypes.lean': '5ce898eb70690f6f77e26a95cbafb5ef268fa93617ab7418a0b25f6878c34968', 'PrefixDefinitions.lean': 'd7b5cd8b624dae007e3c3dc7f3620260dbfcf2169d0211b0859e18ed58180069', 'BridgeDefinitions.lean': '7a36ebc1e9ff89fcec7ad1fdae1c2d5ae9ee011b06ae110fd4f34999e7df19a7', 'BridgeExpectedTypes.lean': '850dcdd0d75479edaeab1c8d6d336b9099f56511e0b6f5a5125bedfca05838aa', 'UnrestrictedDefinitions.lean': 'b22796b599134a98ebcf10002bac7e46d9a463d0e983099353ad524312ac5307', 'UnrestrictedExpectedTypes.lean': '4ce322ba8fcd87a5bdf18244c55df92b27b05a293eab201aa15ee8fa24146670', 'UnrestrictedChallenge.lean': '639af946ad44a5696e625e41276144cc2267cc370fd62c98291af04cbbb99a4e'}
AXIOMS = ("propext", "Quot.sound", "Classical.choice")
CHECKERS = ("Lean default", "Lean paranoid", "lean4lean", "nanoda", "con-leche", "con-ron")


def require(ok, message):
    if not ok:
        raise ValueError(message)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


EXPECTED_HELPER_COUNT = 481  # Exact exhaustive public Audit inventory.
MODEL_NAMES = ('ExternalM4UnrestrictedDraft.beta', 'ExternalM4UnrestrictedDraft.canonicalPrefix', 'ExternalM4UnrestrictedDraft.canonicalWord', 'ExternalM4UnrestrictedDraft.count', 'ExternalM4UnrestrictedDraft.highPhaseCount', 'ExternalM4UnrestrictedDraft.TwentyOneSite', 'ExternalM4UnrestrictedDraft.DisjointSites', 'ExternalM4UnrestrictedDraft.AdmissibleSites', 'ExternalM4UnrestrictedDraft.applySwaps', 'ExternalM4UnrestrictedDraft.SwapCube', 'ExternalM4UnrestrictedDraft.swapFamily', 'ExternalM4UnrestrictedDraft.swapLoss', 'ExternalM4UnrestrictedDraft.normalizedLogCount')
FROZEN_PROPOSITIONS_SHA256 = '35d68ca025ccd4e4ac5488e3d0fff432b86c9814be375d7950ab06587f036bca'
FROZEN_MODELS_SHA256 = '2289d1102f9780189687d7cc0e1f31a100c60a3baccfc9e6daa74f440b603541'


def source_gate(root, inventory=None):
    """Fail closed on exact meanings and complete owned/target/helper/model coverage."""
    root = Path(root)
    inventory = inventory or json.loads((root/"inventory.json").read_text())
    expected = {m+".lean" for m in OWNED_MODULES} | {"UnrestrictedChallenge.lean", "Audit.lean"}
    require(inventory.get("owned_modules") == list(OWNED_MODULES), "inventory owned module coverage mismatch")
    require(len(inventory["targets"]) == 23 and sorted(x["declaration"] for x in inventory["targets"]) == sorted(TARGETS), "inventory target coverage mismatch")
    helpers = [x["declaration"] for x in inventory["helpers"]]
    require(len(helpers) == EXPECTED_HELPER_COUNT and len(set(helpers)) == EXPECTED_HELPER_COUNT and not set(helpers)&set(TARGETS), "inventory helper coverage mismatch")
    require(all(x["module"] in OWNED_MODULES for x in inventory["targets"]+inventory["helpers"]), "inventory declaration module mismatch")
    require(len(inventory["models"]) == 13 and sorted(x["declaration"] for x in inventory["models"]) == sorted(MODEL_NAMES), "inventory model coverage mismatch")
    required = expected | {"verify.py", "README.md", "ARGUMENT.md", "comparator.json", "owned_modules.json", "specification.json", "frozen_propositions.json", "frozen_models.json", "lake-manifest.json", "lakefile.toml", "lean-toolchain", "cache-imports.txt", "test_mutations.py"}
    require(required <= set(inventory["sources_sha256"]), "source inventory coverage mismatch")
    actual = {p.name for p in root.glob("*.lean")}
    require(actual == expected, f"owned Lean module coverage mismatch: {sorted(actual ^ expected)}")
    for name, pin in FROZEN_SOURCES.items():
        require(digest(root/name) == pin, f"frozen source digest mismatch: {name}")
    require(json.loads((root/"owned_modules.json").read_text()) == list(OWNED_MODULES), "owned module register mismatch")
    config = json.loads((root/"comparator.json").read_text())
    require(config["theorem_names"] == list(TARGETS), "frozen target register mismatch")
    require(config["challenge_module"] == "UnrestrictedChallenge" and config["solution_module"] == "UnrestrictedSolution", "comparator module mismatch")
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
    report = {"scope": "all23 actual-slope all-length ordered source-word fixedB_r,c1 targets",
              "mode": args.mode, "status": "running", "steps": []}
    env = dict(os.environ)
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "PYTHONOPTIMIZE"):
        env.pop(key, None)
    if args.toolchain:
        env["PATH"] = str(args.toolchain.resolve()/"bin")+os.pathsep+env.get("PATH", "")
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    lake = shutil.which("lake", path=env.get("PATH"))
    log_directory = Path(tempfile.mkdtemp(prefix="unrestricted-verifier-logs-")) if args.report is None else None

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
        with tempfile.TemporaryDirectory(prefix="collatz-public-unrestricted-") as temporary:
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
            require("version 4.35.0," in version, "wrong unrestricted toolchain")
            build = run("all own source clean build", [lake, "build"])
            require("warning:" not in build + report["steps"][-1]["stderr"], "own build emitted a warning")
            missing = [m for m in OWNED_MODULES if not (root/f".lake/build/lib/lean/{m}.olean").is_file()]
            require(not missing, f"own modules omitted from build: {missing}")
            source_gate(root, inventory)
            audit = run("all own theorem closures and raw frozen target types",
                        [lake, "env", "lean", "-DwarningAsError=true", "-R", str(root), "-o", str(root/".lake/build/lib/lean/Audit.olean"), "Audit.lean"])
            meta = [json.loads(x.removeprefix("UNRESTRICTED_TARGET ")) for x in audit.splitlines()
                    if x.startswith("UNRESTRICTED_TARGET ")]
            closures = [json.loads(x.removeprefix("UNRESTRICTED_SUPPORT ")) for x in audit.splitlines()
                        if x.startswith("UNRESTRICTED_SUPPORT ")]
            model_rows = [json.loads(x.removeprefix("UNRESTRICTED_MODEL ")) for x in audit.splitlines() if x.startswith("UNRESTRICTED_MODEL ")]
            frozen_models = json.loads((root/"frozen_models.json").read_text())
            require(len(model_rows) == 13 and sorted(model_rows,key=lambda x:x["declaration"]) == sorted(frozen_models,key=lambda x:x["declaration"]), "canonical frozen model body/type mismatch")
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
                           "own_theorem_count": len(targets)+len(helpers)})
            if args.mode == "full":
                roots = sorted({x["declaration"] for x in targets+helpers})
                export = root/".lake/unrestricted-complete-proof-closure.ndjson"
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
                comparison = run("all23 frozen statements and independent checker",
                    [lake, "comparator", "--config", "comparator.json", "--paranoid"])
                coverage = {}
                for label, output in (("complete proof closure", replay), ("frozen statement comparison", comparison)):
                    accepted = [name for name in CHECKERS if f"{name} kernel accepts the solution" in output]
                    require(accepted == list(CHECKERS), f"missing required six-checker coverage: {label}")
                    coverage[label] = accepted
                report["checker_coverage"] = coverage
                report["status"] = "passed unrestricted full assurance gates"
            else:
                report["status"] = "partial: clean unrestricted build and axiom audit only"
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
