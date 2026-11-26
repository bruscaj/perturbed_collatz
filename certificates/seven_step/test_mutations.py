"""Reject corrupted data and disabled-assertion invocation of the checkers."""
from copy import deepcopy
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def main():
    if not __debug__:
        raise RuntimeError("Run mutation tests without -O")
    original = json.loads((HERE / "frontier.json").read_text())
    obstruction = json.loads((HERE / "rank_obstruction.json").read_text())
    mutations = []

    def add(name, change, flag="--frontier"):
        data = deepcopy(original if flag == "--frontier" else obstruction)
        change(data)
        mutations.append((name, flag, data))

    add("rank", lambda x: x.update(rank="m at every phase"))
    add("scope", lambda x: x.update(scope="All positive seeds converge"))
    add("return_convention", lambda x: x.update(return_convention="Ignore shrinking-step visits"))
    add("forcing", lambda x: x["physical_forcing"].__setitem__(2, -1))
    add("missing_family", lambda x: x["complete_frontier"]["remaining_families"].pop())
    add("duplicate_family", lambda x: x["complete_frontier"]["remaining_families"].append(x["complete_frontier"]["remaining_families"][0]))
    add("wrong_phase", lambda x: x["complete_frontier"]["remaining_families"][0].update(phase=5))
    add("wrong_coefficient", lambda x: x["complete_frontier"]["remaining_families"][0].update(A=8))
    add("wrong_domain", lambda x: x["complete_frontier"]["remaining_families"][1].update(t_min=0))
    add("wrong_time", lambda x: x["complete_frontier"]["remaining_families"][0].update(steps=3))
    add("missing_exception", lambda x: x["complete_frontier"]["finite_base_exceptions"].pop())
    add("false_strict_gap", lambda x: x["merger"].update(refined_rank_gap=0))
    add("boolean_for_integer", lambda x: x["merger"].update(refined_rank_gap=True))
    add("wrong_envelope", lambda x: x["long_returns"].update(avoiding_envelope="z_next <= z"))
    add("obstruction_scope", lambda x: x.update(rank_class="Every well-founded rank"), "--obstruction")
    add("obstruction_coefficient", lambda x: x["witness_rows"]["D65"].update(output_multiplier=6560), "--obstruction")
    mutations.append(("empty", "--frontier", {}))
    with tempfile.TemporaryDirectory(prefix="collatz-seven-hostile-") as directory:
        valid = subprocess.run([sys.executable, str(HERE / "verify.py")], capture_output=True, text=True)
        if valid.returncode:
            raise RuntimeError("Authentic control failed: " + valid.stderr)
        for name, flag, data in mutations:
            path = Path(directory) / f"{name}.json"
            path.write_text(json.dumps(data))
            run = subprocess.run([sys.executable, str(HERE / "verify.py"), flag, str(path)],
                                 capture_output=True, text=True)
            if run.returncode == 0:
                raise RuntimeError(f"Invalid certificate accepted: {name}")
        truncated = Path(directory) / "truncated.json"
        truncated.write_text('{"status":')
        run = subprocess.run([sys.executable, str(HERE / "verify.py"), "--frontier", str(truncated)],
                             capture_output=True, text=True)
        if run.returncode == 0:
            raise RuntimeError("Truncated JSON accepted")
        duplicate = Path(directory) / "duplicate_key.json"
        raw = (HERE / "frontier.json").read_text()
        duplicate.write_text(raw.replace('"status": "passed",', '"status": "failed", "status": "passed",', 1))
        run = subprocess.run([sys.executable, str(HERE / "verify.py"), "--frontier", str(duplicate)],
                             capture_output=True, text=True)
        if run.returncode == 0:
            raise RuntimeError("Duplicate JSON keys accepted")
        for script in ["verify.py", "verify_relational.py", "verify_rank_obstruction.py"]:
            output = Path(directory) / (script + ".json")
            run = subprocess.run([sys.executable, "-O", str(HERE / script), "--output", str(output)],
                                 capture_output=True, text=True)
            if run.returncode == 0 or output.exists():
                raise RuntimeError(f"Disabled assertions produced success: {script}")
    print(json.dumps({"status": "passed", "authentic_control": "accepted",
                      "corrupted_certificates_rejected": len(mutations) + 2,
                      "optimized_entrypoints_rejected": 3}))


if __name__ == "__main__":
    main()
