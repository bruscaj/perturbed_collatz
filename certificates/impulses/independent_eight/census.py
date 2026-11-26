"""Run the complete escaping-root scan and independently replay every winning word."""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
import json
from pathlib import Path
import subprocess


def inspect(word):
    forcing = [d for b, a in word for d in [1] + [0]*b + [-1] + [0]*a]
    p = len(forcing)
    fundamental = next(q for q in range(1, p+1)
                       if p % q == 0 and all(d == forcing[i % q] for i, d in enumerate(forcing)))
    n = 1
    seen = {}
    values = []
    while (len(values) % p, n) not in seen:
        t = len(values)
        seen[t % p, n] = t
        values.append(n)
        n = ((3*n+1)//2 if n % 2 else n//2) + forcing[t % p]
        if n < 0 or len(values) > 2_000_000:
            raise RuntimeError("literal witness failed to close safely")
    onset = seen[len(values) % p, n]
    cycle = values[onset:]
    scalar = next(q for q in range(1, len(cycle)+1) if len(cycle) % q == 0
                  and all(n == cycle[i % q] for i,n in enumerate(cycle)))
    lap_starts = values[::p]
    next_lap = len(lap_starts)*p
    repeated = values[onset + (next_lap-onset) % len(cycle)]
    lap_onset = lap_starts.index(repeated)
    return dict(word=word, supplied_period=p, fundamental_period=fundamental,
                physical_onset=onset, physical_scalar_period=scalar,
                peak=max(values), first_peak_step=values.index(max(values)),
                recurrent=max(cycle), first_recurrent_peak_step=onset+cycle.index(max(cycle)),
                ratio=len(cycle)//p, transient=lap_onset, boundary_values=lap_starts+[repeated])


def aggregate(rows):
    out = {}
    for key in ("words", "laps"):
        out[key] = sum(row[key] for row in rows)
    for key in ("peak", "recurrent", "ratio", "transient"):
        best = min((row[key] for row in rows), key=lambda r: (-r["value"], r["word"]))
        replay = inspect(best["word"])
        if replay[key] != best["value"]:
            raise AssertionError((key, best, replay))
        out[key] = best
    for name in ("cycle_hist", "transient_hist"):
        counts = Counter()
        for row in rows:
            counts.update({int(k):v for k,v in row[name].items()})
        if sum(counts.values()) != out["words"]:
            raise AssertionError("histogram count mismatch")
        out[name] = dict(sorted(counts.items()))
    return out


def generate(binary, workers):
    if workers < 1:
        raise ValueError("worker count must be positive")
    # One first pair accounts for 94% of the words. Independent partitions of
    # its three-pair prefix ordinal allow it to share all available workers.
    tasks = [(root, i, parts) for root in (3,5,0,1,2,4,6,7,8,9,10,11,12,13,14)
             for parts in [24 if root == 3 else 1] for i in range(parts)]
    def run(task):
        output = subprocess.check_output([str(binary), *map(str, task)], text=True)
        row = json.loads(output)
        if (row["first"],row["shard"],row["parts"]) != task:
            raise AssertionError("shard identity mismatch")
        return row
    with ThreadPoolExecutor(max_workers=workers) as pool:
        rows = list(pool.map(run, tasks))
    first_pairs = [(0,0)] + [(1,a) for a in range(10)] + [(2,a) for a in range(4)]
    grouped = [dict(first_pair=p, **aggregate([r for r in rows if r["first"] == i]))
               for i,p in enumerate(first_pairs)]
    summary = aggregate(grouped)
    if summary["words"] != 2_383_451_629:
        raise AssertionError("root population differs from the independent signed frontier")
    return {"summary":summary,
            "literal_witnesses":{key:inspect(summary[key]["word"]) for key in ("peak","recurrent","ratio","transient")},
            "by_first_pair":grouped}


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("binary", type=Path)
    parser.add_argument("--workers", default=3, type=int)
    args = parser.parse_args()
    print(json.dumps(generate(args.binary.resolve(),args.workers), indent=2))
