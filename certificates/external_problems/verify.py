"""Replay exact finite external-problem evidence and integrity checks."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]


def main():
    output = {}
    for name in ("bridge", "o3"):
        command = [sys.executable, str(HERE / f"{name}.py")]
        normal = subprocess.run(command, check=True, capture_output=True, text=True)
        optimized = subprocess.run([command[0], "-O", command[1]], check=True,
                                   capture_output=True, text=True)
        actual = json.loads(normal.stdout)
        if actual != json.loads(optimized.stdout):
            raise ValueError(f"{name}: optimized behavior differs")
        expected = json.loads((HERE / f"{name}.json").read_text())
        if actual != expected:
            raise ValueError(f"{name}: committed finite evidence differs")
        output[name] = actual
    project = ROOT / "lean/external_problems"
    freeze = json.loads((project / "freeze.json").read_text())
    for name in ("Definitions.lean", "ExpectedTypes.lean", "Challenge.lean"):
        data = (project / name).read_bytes()
        pin = freeze["files"][name]
        if len(data) != pin["bytes"] or hashlib.sha256(data).hexdigest() != pin["sha256"]:
            raise ValueError(f"frozen supporting statement changed: {name}")
    register = json.loads((ROOT / "papers/external_problems/status.json").read_text())
    if len(register["claims"]) != 4 or {c["problem"] for c in register["claims"]} != {"M4", "R8", "R9", "O3′"}:
        raise ValueError("incomplete four-problem register")
    for claim in register["claims"]:
        if claim["headline_formal_declarations"] or claim["status"] != "draft candidate":
            raise ValueError("headline status changed; requires a fresh release audit")
    output["frozen_supporting_spec_hashes"] = "match"
    output["limits"] = "No headline infinite theorem, novelty or human review certified."
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
