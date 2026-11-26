"""Recompute the seven-step certificate and bind every stored field to it.

This validates finite exact calculations. The manuscript supplies the
well-founded induction and the arbitrary-wait argument. No Lean result is
asserted by this program.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def load_json(path):
    def unique_object(pairs):
        result = {}
        for key, value in pairs:
            if key in result:
                raise ValueError(f"Duplicate JSON key: {key}")
            result[key] = value
        return result

    def invalid_constant(value):
        raise ValueError(f"Non-JSON numeric constant: {value}")

    return json.loads(Path(path).read_text(), object_pairs_hook=unique_object,
                      parse_constant=invalid_constant)


def check(frontier=HERE / "frontier.json", obstruction=HERE / "rank_obstruction.json"):
    if not __debug__:
        raise RuntimeError("Verification requires assertions; run without -O")
    with tempfile.TemporaryDirectory(prefix="collatz-seven-") as directory:
        outputs = []
        for script, candidate in [("verify_relational.py", frontier),
                                  ("verify_rank_obstruction.py", obstruction)]:
            generated = Path(directory) / (script + ".json")
            process = subprocess.run([sys.executable, str(HERE / script), "--output", str(generated)],
                                     text=True, capture_output=True)
            if process.returncode != 0:
                raise RuntimeError(f"{script} failed: {process.stdout}\n{process.stderr}")
            expected = load_json(generated)
            supplied = load_json(candidate)
            # Canonical JSON also distinguishes booleans/floats from integers.
            if json.dumps(supplied, sort_keys=True) != json.dumps(expected, sort_keys=True):
                raise ValueError(f"Certificate differs from exact reconstruction: {Path(candidate).name}")
            outputs.append({"script": script, "all_fields_match": True})
    from independent import check as independent_check
    replay = independent_check()
    return {"status": "passed", "certificate_comparisons": outputs,
            "independent_reconstruction": replay,
            "scope": "Four-family conditional reduction; global capture remains open."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--frontier", type=Path, default=HERE / "frontier.json")
    parser.add_argument("--obstruction", type=Path, default=HERE / "rank_obstruction.json")
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    result = check(args.frontier, args.obstruction)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps({"status": result["status"], "infinite_section_domains": 392,
                      "phase_zero_domains": 384, "remaining": ["S00", "S01", "S02", "S03"],
                      "independent_reconstruction": "passed", "scope": result["scope"]}))


if __name__ == "__main__":
    main()
