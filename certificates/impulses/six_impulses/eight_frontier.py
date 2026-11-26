"""Count four-pair escaping paths without enumerating all ordered words."""

import json
from collections import Counter

from certify import BASE, outside_endpoints, segment, signed_closures


def run():
    closures = signed_closures((1, -1) * 4)
    counts = Counter(BASE)
    levels = []
    parents = []
    for _ in range(4):
        following = Counter()
        predecessor = {}
        for n, ways in counts.items():
            for pair, endpoint in outside_endpoints(n):
                following[endpoint] += ways
                predecessor.setdefault(endpoint, (n, pair))
        parents.append(predecessor)
        counts = following
        levels.append({"prefixes": sum(counts.values()), "outside_values": len(counts),
                       "max_endpoint": max(counts)})

    peak = max(row["peak"] for row in closures)
    # Trace one chain that realizes the closure upper bound at the end of pair 4.
    path = []
    value = peak
    for predecessor in reversed(parents):
        value, pair = predecessor[value]
        path.append(pair)
    path.reverse()
    seed = value
    for pair in path:
        value, _ = segment(pair, value)
    if seed not in BASE or value != peak:
        raise ArithmeticError("invalid one-pass witness")
    return dict(signed_closures=closures, escaping_levels=levels,
                one_pass_peak=peak, peak_seed=seed, witness_pairs=path,
                peak_step=sum(2 + b + a for b, a in path))


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
