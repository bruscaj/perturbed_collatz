"""Reproduce, combine and verify the 15 disjoint four-pair excursion shards."""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor
from functools import lru_cache
import json
from pathlib import Path
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
RESEARCH = HERE.parent
sys.path.insert(0, str(RESEARCH / "six_impulses"))
from certify import outside_endpoints

# Third-prefix interleaving is used only to balance work within the largest logical shard.
JOBS = ([(3, i, 12) for i in range(12)] +
        [(i, 0, 1) for i in (5,2,4,6,8,12,0,1,7,9,10,11,13,14)])


def scan(workers):
    with tempfile.TemporaryDirectory(prefix="collatz-eight-") as tmp:
        binary = Path(tmp) / "census"
        subprocess.run(["c++", "-O3", "-std=c++17", "-Wall", "-Wextra", "-Wpedantic",
                        str(HERE / "census.cpp"), "-o", str(binary)], check=True)
        def task(job):
            return json.loads(subprocess.check_output([str(binary), *map(str, job)]))
        with ThreadPoolExecutor(max_workers=workers) as pool:
            return list(pool.map(task, JOBS))


@lru_cache(maxsize=None)
def prefix_count(n, remaining):
    if remaining == 1:
        return sum(1 for _ in outside_endpoints(n))
    return sum(prefix_count(out, remaining-1) for _, out in outside_endpoints(n))


def literal(pairs):
    impulses = []
    ends = []
    for b,a in pairs:
        impulses.extend((1, *([0]*b), -1, *([0]*a)))
        ends.append(len(impulses))
    p = len(impulses)
    fundamental = next(q for q in range(1,p+1) if p%q==0 and impulses==impulses[:q]*(p//q))
    states, times = [], {}
    k,n=0,1
    while (n,k%p) not in times:
        times[n,k%p] = k
        states.append(n)
        n = (n//2 if n%2==0 else (3*n+1)//2) + impulses[k%p]
        k += 1
        if n < 0 or k > 1_000_000:
            raise ArithmeticError("unresolved literal witness")
    mu=times[n,k%p]
    cycle=states[mu:]
    augmented=len(cycle)
    scalar=next(q for q in range(1,augmented+1)
                if augmented%q==0 and cycle==cycle[:q]*(augmented//q))
    # A microstep first-repeat can happen before the first complete lap finishes.
    def at(t):
        return states[t] if t<len(states) else cycle[(t-mu)%augmented]
    boundaries=[at(t) for t in ends]
    if min(boundaries)<=2 or augmented%p:
        raise ArithmeticError("witness failed the excursion or strobe conditions")
    recurrent=max(cycle)
    return dict(pairs=pairs, primitive_forcing_period=fundamental, supplied_period=p,
                first_lap_pair_endpoints=boundaries, cycle_laps=augmented//p,
                cycle_updates=augmented, scalar_period=scalar, cycle_entry_update=mu,
                strobe_transient_laps=(mu+p-1)//p, peak=max(states),
                first_peak_update=states.index(max(states)), recurrent_peak=recurrent,
                first_recurrent_peak_update=mu+cycle.index(recurrent))


@lru_cache(maxsize=None)
def partition_sizes(first_endpoint, parts):
    if parts == 1:
        return (prefix_count(first_endpoint, 3),)
    sizes = [0] * parts
    ordinal = 0
    for _, second_endpoint in outside_endpoints(first_endpoint):
        for _, third_endpoint in outside_endpoints(second_endpoint):
            sizes[ordinal % parts] += prefix_count(third_endpoint, 1)
            ordinal += 1
    return tuple(sizes)


def partition_witness(pairs, first, shard, part, parts):
    """Check that the recorded word occurs in this generator shard before replay."""
    if (not isinstance(pairs, list) or len(pairs) != 4
            or any(not isinstance(pair, list) or len(pair) != 2
                   or any(type(gap) is not int or gap < 0 for gap in pair)
                   for pair in pairs)):
        raise ValueError("a witness must have four pairs of nonnegative integer gaps")
    first_pair, endpoint = first[shard]
    if tuple(pairs[0]) != first_pair:
        raise ValueError("witness belongs to a different first-pair shard")
    ordinal = 0
    for depth, pair in enumerate(pairs[1:], start=2):
        for candidate, next_endpoint in outside_endpoints(endpoint):
            if candidate == tuple(pair):
                endpoint = next_endpoint
                break
            if parts > 1 and depth == 2:
                ordinal += prefix_count(next_endpoint, 1)
            elif parts > 1 and depth == 3:
                ordinal += 1
        else:
            raise ValueError("witness contains an ineligible excursion pair")
    if ordinal % parts != part:
        raise ValueError("witness belongs to a different third-prefix partition")
    return literal(pairs)


def check_shard(record, first):
    def histogram(key, minimum):
        result = {}
        for index, count in record[key].items():
            if (not isinstance(index, str) or not index.isascii() or not index.isdecimal()
                    or index != str(int(index)) or int(index) < minimum
                    or type(count) is not int or count <= 0):
                raise ValueError("invalid " + key + " histogram")
            result[int(index)] = count
        return result
    cycles = histogram("cycle", 1)
    transients = histogram("transient", 0)
    primitive = histogram("primitive_cycle", 1)
    words = record["words"]
    _, endpoint = first[record["shard"]]
    population = partition_sizes(endpoint, record["parts"])[record["part"]]
    if (type(words) is not int or words != population or words <= 0
            or sum(cycles.values()) != words or sum(transients.values()) != words
            or any(count > cycles.get(ratio, 0) for ratio, count in primitive.items())):
        raise ValueError("inconsistent shard histogram totals")
    if set(record["primitive_examples"]) != {str(ratio) for ratio in primitive}:
        raise ValueError("missing or extra primitive witness")
    def replay(pairs):
        return partition_witness(pairs, first, record["shard"], record["part"], record["parts"])
    for ratio, pairs in record["primitive_examples"].items():
        witness = replay(pairs)
        if (witness["cycle_laps"] != int(ratio)
                or witness["primitive_forcing_period"] != witness["supplied_period"]
                or witness["scalar_period"] != witness["cycle_updates"]):
            raise ValueError("invalid shard primitive period witness")
    for quantity in ("peak", "recurrent_peak"):
        entry = record[quantity]
        value = entry["value"]
        if type(value) is not int or value != replay(entry["pairs"])[quantity]:
            raise ValueError("invalid shard " + quantity + " witness")
    if record["recurrent_peak"]["value"] > record["peak"]["value"]:
        raise ValueError("recurrent peak exceeds overall peak")


def summarize(records):
    if any(type(r[key]) is not int for r in records for key in ("shard", "part", "parts")):
        raise ValueError("invalid partition identifiers")
    parts = [(r["shard"],r["part"],r["parts"]) for r in records]
    if sorted(parts)!=sorted(JOBS):
        raise ValueError("incomplete or duplicate partitions")
    records = sorted(records,key=lambda r:(r["shard"],r["part"]))
    histograms = {k:Counter() for k in ("cycle","primitive_cycle","transient")}
    shard_totals, examples = Counter(), {}
    first=list(outside_endpoints(1))
    for r in records:
        check_shard(r, first)
        words=r["words"]
        shard_totals[r["shard"]] += words
        for key,h in histograms.items():
            h.update({int(k):v for k,v in r[key].items()})
        for ratio,pairs in r["primitive_examples"].items():
            examples.setdefault(int(ratio),pairs)
    expected=json.loads((RESEARCH/"six_impulses"/"eight_frontier.json").read_text())["escaping_levels"][-1]["prefixes"]
    words=sum(shard_totals.values())
    if words!=expected:
        raise ArithmeticError("count differs from eight-impulse frontier")
    if set(examples)!=set(histograms["cycle"]):
        raise ArithmeticError("at least one ratio still needs a primitive witness")
    for ratio,pairs in list(examples.items()):
        w=literal(pairs)
        if w["cycle_laps"]!=ratio or w["primitive_forcing_period"]!=w["supplied_period"] or w["scalar_period"]!=w["cycle_updates"]:
            raise ArithmeticError("invalid primitive period witness")
        examples[ratio]=w
    extremes={}
    for quantity in ("peak","recurrent_peak"):
        record=max((r[quantity] for r in records),key=lambda entry:entry["value"])
        w=literal(record["pairs"])
        if w[quantity]!=record["value"]:
            raise ArithmeticError("replayed peak mismatch")
        extremes[quantity]=record["value"]
        extremes[quantity+"_witness"]=w
    return dict(words=words,shards=[{"first_pair":pair,"first_endpoint":n,"words":shard_totals[i]}
                      for i,(pair,n) in enumerate(first)],
                cycle_lengths_in_supplied_laps=dict(sorted(histograms["cycle"].items())),
                primitive_cycle_lengths_in_supplied_laps=dict(sorted(histograms["primitive_cycle"].items())),
                transient_lengths_in_supplied_laps=dict(sorted(histograms["transient"].items())),
                **extremes,primitive_examples=dict(sorted(examples.items())))


def save(path, value):
    path.write_text(json.dumps(value,indent=2)+"\n")


def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--workers",type=int,default=4)
    parser.add_argument("--check",action="store_true",help="check saved shards and witnesses without running C++ again")
    parser.add_argument("--output-dir",type=Path,default=HERE)
    args=parser.parse_args()
    if args.check:
        shards=json.loads((args.output_dir/"partitions.json").read_text())
        current=json.loads(json.dumps(summarize(shards)))
        if current != json.loads((args.output_dir/"results.json").read_text()):
            raise ArithmeticError("stored results do not match the certified summary")
        print(f"Validated the saved partition totals for {current['words']:,} rooted words and replayed every shard witness.")
    else:
        if not 1<=args.workers<=4:
            parser.error("choose 1 through 4 workers")
        shards=sorted(scan(args.workers),key=lambda r:(r["shard"],r["part"]))
        result=summarize(shards)
        args.output_dir.mkdir(parents=True,exist_ok=True)
        save(args.output_dir/"partitions.json",shards)
        save(args.output_dir/"results.json",result)
        print(f"Closed {result['words']:,} rooted words.")


if __name__=="__main__":
    main()

