#!/usr/bin/env python3
"""Clean deterministic TeX builds for the two external-problem manuscripts.

Requires latexmk and pdflatex. Builds only the two standalone paper.tex files;
does not change the repository's core manuscript. Use --check to compare clean
rebuilds byte-for-byte with the recorded PDFs, or --output-dir for build logs,
rebuilt PDFs and a machine-readable report outside the source directories.
"""
from __future__ import annotations

import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
PAPERS = ("finite_information_lyapunov", "arithmetic_bridge_pressure")
EPOCH = str(int(datetime(2026, 11, 27, tzinfo=timezone.utc).timestamp()))
FORBIDDEN_LOG = (
    r"Overfull \\[hv]box",
    r"LaTeX Warning: (?:Citation|Reference)[^\n]*undefined",
    r"There were undefined (?:references|citations)",
    r"Rerun to get cross-references right",
    r"Missing character:",
    r"LaTeX Error:",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path)
    parser.add_argument("--check", action="store_true",
                        help="rebuild and require byte equality with each stored paper.pdf")
    args = parser.parse_args()
    if shutil.which("latexmk") is None or shutil.which("pdflatex") is None:
        raise SystemExit("Both latexmk and pdflatex are required.")
    destination = args.output_dir.resolve() if args.output_dir else None
    if destination:
        destination.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env.update(SOURCE_DATE_EPOCH=EPOCH, FORCE_SOURCE_DATE="1", TZ="UTC")
    report = {"status": "running", "source_date_epoch": EPOCH,
              "mode": "check" if args.check else "build", "papers": []}
    for tool in ("latexmk", "pdflatex"):
        version = subprocess.run([tool, "-version"], capture_output=True, text=True, check=True)
        report[tool] = version.stdout.splitlines()[0]
    try:
        for name in PAPERS:
            original = HERE / name
            with tempfile.TemporaryDirectory(prefix=f"paper-{name}-") as temporary:
                root = Path(temporary)
                shutil.copyfile(original / "paper.tex", root / "paper.tex")
                command = [
                    "latexmk", "-norc", "-pdf", "-interaction=nonstopmode",
                    "-halt-on-error", "-file-line-error",
                    "-pdflatex=pdflatex -no-shell-escape %O %S", "paper.tex",
                ]
                result = subprocess.run(command, cwd=root, env=env,
                                        capture_output=True, text=True)
                tex_log = (root / "paper.log").read_text(errors="replace") if (root / "paper.log").exists() else ""
                matches = [pattern for pattern in FORBIDDEN_LOG if re.search(pattern, tex_log)]
                row = {"paper": name, "command": command, "exit_code": result.returncode,
                       "source_sha256": digest(original / "paper.tex"),
                       "forbidden_log_patterns": matches}
                report["papers"].append(row)
                if destination:
                    artifact = destination / name
                    artifact.mkdir(parents=True, exist_ok=True)
                    (artifact / "build.log").write_text(result.stdout + result.stderr)
                    (artifact / "paper.log").write_text(tex_log)
                if result.returncode or matches or not (root / "paper.pdf").is_file():
                    if not destination:
                        print(result.stdout + result.stderr)
                    raise RuntimeError(f"{name}: clean build failed or layout/reference diagnostic found: {matches}")
                row.update(pdf_sha256=digest(root / "paper.pdf"),
                           pdf_bytes=(root / "paper.pdf").stat().st_size)
                if args.check:
                    expected = original / "paper.pdf"
                    if not expected.is_file() or digest(expected) != row["pdf_sha256"]:
                        raise RuntimeError(f"{name}: recorded PDF differs from the clean rebuild")
                    row["recorded_pdf_matches"] = True
                elif destination is None:
                    shutil.copyfile(root / "paper.pdf", original / "paper.pdf")
                if destination:
                    shutil.copyfile(root / "paper.pdf", destination / name / "paper.pdf")
        report["status"] = "passed"
    except Exception as error:
        report["status"] = "failed"
        report["error"] = str(error)
        raise
    finally:
        if destination:
            (destination / "papers-build-report.json").write_text(json.dumps(report, indent=2) + "\n")
        print(json.dumps(report, indent=2))


if __name__ == "__main__":
    main()
