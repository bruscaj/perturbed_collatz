"""Regenerate the public payload manifest from its explicit root allowlist."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ALLOWED = {".github", ".gitignore", "CHANGELOG.md", "Makefile", "README.md",
           "certificates", "claims.json", "figures", "lean", "paper.pdf",
           "paper.tex", "requirements-figures.txt", "scripts", "tex", "papers", "verification"}
IGNORED = {".git", ".lake", "__pycache__", "build"}
GENERATED = {".pyc", ".olean", ".ilean", ".trace", ".aux", ".log", ".out",
             ".toc", ".fls", ".fdb_latexmk"}


def payload_paths():
    for path in sorted(ROOT.rglob("*")):
        relative = path.relative_to(ROOT)
        if any(part in IGNORED for part in relative.parts):
            continue
        if path.is_symlink():
            raise ValueError(f"Symlink in release payload: {relative}")
        if not path.is_file() or path.name == "MANIFEST.json" or path.suffix in GENERATED:
            continue
        if relative.parts[0] not in ALLOWED:
            raise ValueError(f"Unexpected public payload root: {relative}")
        yield path


def main():
    files = []
    for path in payload_paths():
        data = path.read_bytes()
        files.append({"path": path.relative_to(ROOT).as_posix(), "bytes": len(data),
                      "sha256": hashlib.sha256(data).hexdigest()})
    value = {"schema": 1, "scope": "Exact public payload; excludes this manifest and generated build files.",
             "files": files}
    (ROOT/"MANIFEST.json").write_text(json.dumps(value, indent=2)+"\n")
    print(f"Manifest refreshed: {len(files)} files")


if __name__ == "__main__":
    main()
