"""Clean supporting build/audit; full mode additionally requires sandboxed replay."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile
import time

HERE = Path(__file__).resolve().parent


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--toolchain", type=Path)
    parser.add_argument("--mode", choices=("build", "full"), default="full")
    parser.add_argument("--report", type=Path)
    args = parser.parse_args()
    report = {"scope": "five abstract integer supporting theorems; no headline theorem",
              "status": "running", "mode": args.mode, "steps": []}
    env = dict(os.environ)
    for name in ("LEAN_PATH", "LEAN_SRC_PATH"):
        env.pop(name, None)
    if args.toolchain:
        env["PATH"] = str(args.toolchain.resolve()/"bin")+os.pathsep+env.get("PATH", "")
    lake = shutil.which("lake", path=env.get("PATH"))
    try:
        if not lake:
            raise RuntimeError("lake unavailable; install pinned Lean or pass --toolchain")
        with tempfile.TemporaryDirectory(prefix="external-prefix-") as temporary:
            root = Path(temporary)/"project"
            shutil.copytree(HERE, root, ignore=shutil.ignore_patterns(".lake", "*.olean", "*.ilean", "__pycache__"))

            def run(label, command):
                started = time.monotonic()
                row = {"label": label, "command": command, "status": "running"}
                report["steps"].append(row)
                if args.report:
                    args.report.write_text(json.dumps(report, indent=2)+"\n")
                print(f"RUN {label}", flush=True)
                result = subprocess.run(command, cwd=root, env=env, capture_output=True, text=True)
                row.update({"exit_code": result.returncode, "seconds": round(time.monotonic()-started, 3),
                            "status": "passed" if result.returncode == 0 else "failed",
                            "stdout": result.stdout, "stderr": result.stderr})
                if args.report:
                    args.report.write_text(json.dumps(report, indent=2)+"\n")
                if result.returncode:
                    raise RuntimeError(f"{label} failed: {result.stdout}\n{result.stderr}")
                print(f"PASS {label} ({row['seconds']}s)", flush=True)
                return result.stdout

            version = run("version", [lake, "env", "lean", "--version"])
            if "version 4.35.0," not in version:
                raise ValueError("supporting toolchain version mismatch")
            build = run("clean build", [lake, "build"])
            if "warning:" in build or "warning:" in report["steps"][-1]["stderr"]:
                raise RuntimeError("supporting build emitted a warning")
            audit = run("all supporting theorem closures and raw types",
                        [lake, "env", "lean", "-DwarningAsError=true", "Audit.lean"])
            rows = [json.loads(x.removeprefix("EXTERNAL_THEOREM "))
                    for x in audit.splitlines() if x.startswith("EXTERNAL_THEOREM ")]
            if len(rows) != 5:
                raise ValueError("missing supporting theorem inventory")
            recorded = json.loads((HERE/"inventory.json").read_text())
            if sorted(rows, key=lambda r:r["declaration"]) != recorded["declarations"]:
                raise ValueError("supporting elaborated inventory mismatch")
            helpers = [json.loads(x.removeprefix("EXTERNAL_HELPER "))
                       for x in audit.splitlines() if x.startswith("EXTERNAL_HELPER ")]
            if sorted(helpers, key=lambda r:r["declaration"]) != recorded["generated_helpers"]:
                raise ValueError("supporting generated helper inventory mismatch")
            for name, digest in recorded["sources_sha256"].items():
                if hashlib.sha256((HERE/name).read_bytes()).hexdigest() != digest:
                    raise ValueError(f"supporting source inventory mismatch: {name}")
            if args.mode == "full":
                run("fresh export and all bundled checkers", [lake, "check", "--paranoid"])
                run("frozen statement comparison and independent checker",
                    [lake, "comparator", "--config", "comparator.json", "--paranoid"])
                report["status"] = "passed supporting full assurance gates"
            else:
                report["status"] = "partial: clean build and audit only"
                report["missing_gates"] = ["sandboxed fresh replay", "statement comparator", "independent checker"]
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        raise
    finally:
        if args.report:
            args.report.write_text(json.dumps(report, indent=2)+"\n")
    print(report["status"])


if __name__ == "__main__":
    main()
