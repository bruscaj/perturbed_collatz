"""Exact small check for the nonescaping class; literal-time replay of sharp examples."""
from collections import Counter
from functools import lru_cache
from itertools import product
from pathlib import Path
import json


def ordinary(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def failing_base_pairs():
    pairs = []
    u = ordinary(1) + 1
    b = 0
    while u > 2:
        v = ordinary(u) - 1
        a = 0
        while v > 2:
            pairs.append((b, a))
            v = ordinary(v)
            a += 1
        u = ordinary(u)
        b += 1
    return pairs


def symbols(pairs):
    word = []
    for b, a in pairs:
        word.extend([1] + [0] * b + [-1] + [0] * a)
    return tuple(word)


@lru_cache(maxsize=None)
def pair_endpoint(n, pair):
    for impulse in symbols((pair,)):
        n = ordinary(n) + impulse
        if n < 0:
            raise RuntimeError("unsafe transition")
    return n


def rotates(word):
    return (word[i:] + word[:i] for i in range(len(word)))


def escapes(word):
    n = 1
    for pair in word:
        n = pair_endpoint(n, pair)
        if n <= 2:
            return False
    return True


def max_ratio(word):
    maximum = 0
    for rotated in rotates(word):
        for n in range(3):
            seen = {}
            while n not in seen:
                seen[n] = len(seen)
                for pair in rotated:
                    n = pair_endpoint(n, pair)
                if len(seen) > 1000:
                    raise RuntimeError("small census failed to close")
            maximum = max(maximum, len(seen) - seen[n])
    return maximum


def least_period(xs):
    for p in range(1, len(xs) + 1):
        if len(xs) % p == 0 and all(x == xs[i % p] for i, x in enumerate(xs)):
            return p
    raise RuntimeError("empty cycle")


def replay(pairs, seed, phase=0):
    forcing = symbols(pairs[phase:] + pairs[:phase])
    n = seed
    seen = {}
    path = []
    while (n, len(path) % len(forcing)) not in seen:
        t = len(path)
        seen[n, t % len(forcing)] = t
        path.append(n)
        n = ordinary(n) + forcing[t % len(forcing)]
        if n < 0 or t > 100000:
            raise RuntimeError("witness failed to close safely")
    onset = seen[n, len(path) % len(forcing)]
    cycle = path[onset:]
    return {
        "forcing_period": least_period(forcing),
        "augmented_transient": onset,
        "scalar_period": least_period(cycle),
        "peak": max(path),
        "first_peak_step": path.index(max(path)),
        "recurrent_peak": max(cycle),
        "period_boundary_values": path[::len(forcing)],
    }


def main():
    failing = failing_base_pairs()
    counts = Counter()
    for word in product(failing, repeat=3):
        if not any(escapes(w) for w in rotates(word)):
            counts[max_ratio(word)] += 1
    if len(failing) != 15 or counts != {1: 457, 2: 272, 3: 51, 4: 6}:
        raise RuntimeError(f"unexpected exceptional census: {failing}, {counts}")

    small_peak = ((1, 2), (21, 13), (42, 74))
    small_ratio = ((1, 4), (2, 3), (1, 8))
    for word in (small_peak, small_ratio):
        if any(escapes(w) for w in rotates(word)):
            raise RuntimeError("purported complementary witness escapes")

    cases = {}
    for label, word in (("complement_peak", small_peak), ("complement_ratio", small_ratio)):
        cases[label] = replay(word, 1)
    results = json.loads(Path(__file__).with_name("census.json").read_text())
    for label in ("peak", "response_ratio", "recurrent_peak"):
        witness = results[label]
        cases[label] = replay(witness["pairs"], witness["seed"], witness["before_pair"])
        case = cases[label]
        if label == "response_ratio":
            agrees = case["scalar_period"] == case["forcing_period"] * witness["value"]
        else:
            agrees = case[label] == witness["value"]
        if not agrees:
            raise RuntimeError(f"{label} witness failed")
    cases["recurrent_peak_from_one"] = replay(results["recurrent_peak"]["pairs"], 1)
    positive = cases["recurrent_peak_from_one"]
    if positive["recurrent_peak"] != results["recurrent_peak"]["value"] or positive["first_peak_step"] != 104:
        raise RuntimeError("positive recurrent-peak witness failed")
    if cases["complement_peak"]["recurrent_peak"] != 642842:
        raise RuntimeError("complement peak failed")
    if cases["complement_ratio"]["scalar_period"] != 4 * cases["complement_ratio"]["forcing_period"]:
        raise RuntimeError("complement ratio failed")

    print(json.dumps({"failing_pair_choices": len(failing),
                      "complement_ratio_histogram_in_failing_triples": dict(sorted(counts.items())),
                      "witnesses": cases}, indent=2))


if __name__ == "__main__":
    main()
