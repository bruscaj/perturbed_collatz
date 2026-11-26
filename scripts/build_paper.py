#!/usr/bin/env python3
"""Compile the complete manuscript in a clean temporary directory."""
import argparse
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "paper.pdf")
    args = parser.parse_args()
    with tempfile.TemporaryDirectory(prefix="collatz-paper-") as directory:
        tmp = Path(directory)
        shutil.copy2(ROOT / "paper.tex", tmp / "paper.tex")
        shutil.copytree(ROOT / "tex", tmp / "tex")
        shutil.copytree(ROOT / "figures", tmp / "figures")
        env = dict(os.environ)
        env.setdefault("SOURCE_DATE_EPOCH", "1795651200")
        env.setdefault("FORCE_SOURCE_DATE", "1")
        command = ["latexmk", "-pdf", "-interaction=nonstopmode", "-halt-on-error",
                   "-file-line-error", "-latexoption=-no-shell-escape", "paper.tex"]
        result = subprocess.run(command, cwd=tmp, env=env, text=True,
                                stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode:
            print(result.stdout)
            raise SystemExit(result.returncode)
        log = (tmp / "paper.log").read_text(errors="replace")
        forbidden = ["There were undefined references", "There were undefined citations",
                     "multiply defined", "Overfull \\hbox", "Overfull \\vbox"]
        problems = [line for line in log.splitlines() if any(x in line for x in forbidden)]
        if problems:
            print("\n".join(problems))
            raise SystemExit("Resolve manuscript references and overflowing boxes before release.")
        target = args.output.resolve()
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(tmp / "paper.pdf", target)
        print(f"Compiled {target.name}: {target.stat().st_size:,} bytes; references and overflow checks passed.")


if __name__ == "__main__":
    main()
