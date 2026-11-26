"""All-gap verification for three alternating pulse pairs, using Python integers."""

import json
from collections import Counter
from functools import lru_cache
from itertools import product

BASE = (0, 1, 2)
SIGNS = (1, -1) * 3
# A missed return or long path raises an error; no truncation is accepted.
LIMIT = 1000


def ordinary(n):
    return (3 * n + 1) // 2 if n % 2 else n // 2


def signed_closures(signs=SIGNS):
    current = set(BASE)
    rows = []
    for sign in signs:
        following = set()
        for n in current:
            start = ordinary(n) + sign
            if start < 0:
                raise ArithmeticError("unsafe impulse")
            value = start
            for _ in range(LIMIT):
                following.add(value)
                if value <= 2:
                    following.add(ordinary(value))  # the rest of the base cycle
                    break
                value = ordinary(value)
            else:
                raise RuntimeError(("ordinary return unresolved", start))
        rows.append({"sign": sign, "size": len(following), "peak": max(following)})
        current = following
    return rows


def outside_endpoints(n):
    """Yield every (pair, endpoint) with endpoint outside the base."""
    pre_minus = ordinary(n) + 1
    for b in range(LIMIT):
        if pre_minus <= 2:
            return
        endpoint = ordinary(pre_minus) - 1
        for a in range(LIMIT):
            if endpoint <= 2:
                break
            yield (b, a), endpoint
            endpoint = ordinary(endpoint)
        else:
            raise RuntimeError(("unresolved post-minus tail", n, b))
        pre_minus = ordinary(pre_minus)
    raise RuntimeError(("unresolved post-plus tail", n))


@lru_cache(maxsize=None)
def escaping_pairs(n):
    return list(outside_endpoints(n))


@lru_cache(maxsize=150_000)
def segment(pair, n):
    """Output and peak of the exact segment, including its input."""
    b, a = pair
    value = ordinary(n) + 1
    peak = max(n, value)
    for _ in range(b):
        value = ordinary(value)
        peak = max(peak, value)
    value = ordinary(value) - 1
    if value < 0:
        raise ArithmeticError(("unsafe segment", pair, n))
    peak = max(peak, value)
    for _ in range(a):
        value = ordinary(value)
        peak = max(peak, value)
    return value, peak


def certify_word(word):
    # Discovery times are shared across starts. A repeated vertex discovered
    # during this start closes a new cycle. An older vertex has a known future.
    seen = {}
    peak = 0
    ratios = 0
    interval_peaks = []
    recurrent_peak = 0
    for phase, n in product(range(3), BASE):
        start_time = len(seen)
        while (phase, n) not in seen:
            seen[phase, n] = len(seen)
            n, local_peak = segment(word[phase], n)
            interval_peaks.append(local_peak)
            peak = max(peak, local_peak)
            phase = (phase + 1) % 3
            if len(seen) >= LIMIT:
                raise RuntimeError(("unresolved word", word, phase, n))
        entry = seen[phase, n]
        if entry >= start_time:
            pair_steps = len(seen) - entry
            if pair_steps % 3:
                raise ArithmeticError("cycle missed its initial phase")
            ratios |= 1 << (pair_steps // 3)
            recurrent_peak = max(recurrent_peak, max(interval_peaks[entry:]))
    return peak, recurrent_peak, ratios, len(seen)


def describe_witness(word, target, kind):
    """Replay individual updates and report one initial state attaining target."""
    for start_phase, seed in product(range(3), (1, 2, 0)):
        n = seed
        i = start_phase
        seen = {}
        step = 0
        target_steps = []
        while (i, n) not in seen:
            seen[i, n] = step
            b, a = word[i]
            for d in (1,) + (0,) * b + (-1,) + (0,) * a:
                n = ordinary(n) + d
                step += 1
                if n == target:
                    target_steps.append(step)
            i = (i + 1) % 3
        period = sum(2 + b + a for b, a in word)
        cycle_steps = step - seen[i, n]
        recurrent_steps = [t for t in target_steps if t >= seen[i, n]]
        if (kind == "peak" and target_steps) or (kind == "recurrent" and recurrent_steps) or (
            kind == "ratio" and cycle_steps == target * period
        ):
            result = dict(pairs=word, seed=seed, first_pair_index=start_phase,
                          forcing_period=period, cycle_steps=cycle_steps,
                          repeated_pair_index=i, repeated_value=n,
                          first_boundary_visit_step=seen[i, n],
                          repeated_boundary_step=step)
            if kind == "peak":
                result["first_peak_step"] = target_steps[0]
            if kind == "recurrent":
                result["step_at_recurrent_peak"] = recurrent_steps[0]
            return result
    raise RuntimeError(("witness missing", word, target, kind))


def run():
    rows = signed_closures()
    counts = [0] * 3
    max_peak = max(row["peak"] for row in rows)
    max_recurrent = max_peak
    max_ratio = 5
    peak_word = ratio_word = recurrent_word = None
    largest_graph = 0
    ratio_histogram = Counter()
    all_ratios = 0
    ratio_examples = {}
    high_ratio_words = set()
    transitions = 0
    for seed in BASE:
        for first, x in escaping_pairs(seed):
            counts[0] += 1
            for second, y in escaping_pairs(x):
                counts[1] += 1
                for third, _ in escaping_pairs(y):
                    counts[2] += 1
                    word = (first, second, third)
                    peak, recurrent_peak, ratios, graph_size = certify_word(word)
                    ratio = ratios.bit_length() - 1
                    if word[0] != word[1] or word[0] != word[2]:
                        new_ratios = ratios & ~all_ratios
                        while new_ratios:
                            value = new_ratios.bit_length() - 1
                            ratio_examples[value] = word
                            new_ratios ^= 1 << value
                        all_ratios |= ratios
                    if ratio >= 10:
                        rotations = [word[i:] + word[:i] for i in range(3)]
                        high_ratio_words.add((ratio, min(rotations)))
                    largest_graph = max(largest_graph, graph_size)
                    transitions += graph_size
                    ratio_histogram[ratio] += 1
                    if peak > max_peak:
                        max_peak, peak_word = peak, word
                    if recurrent_peak > max_recurrent:
                        max_recurrent, recurrent_word = recurrent_peak, word
                    if ratio > max_ratio:
                        max_ratio, ratio_word = ratio, word
    one_pass = ((1, 2), (21, 13), (42, 8))
    first_pass_witness = describe_witness(one_pass, rows[-1]["peak"], "peak")
    if first_pass_witness["first_peak_step"] > first_pass_witness["forcing_period"]:
        raise ArithmeticError("one-pass witness did not attain peak in first pass")
    return {
        "signed_closures": rows,
        "escaping_prefix_counts": counts,
        "largest_examined_boundary_graph": largest_graph,
        "examined_boundary_transitions": transitions,
        "rooted_triples_by_largest_cycle_ratio": dict(sorted(ratio_histogram.items())),
        "primitive_core_period_examples": {
            r: describe_witness(w, r, "ratio") for r, w in sorted(ratio_examples.items())
        },
        "all_high_ratio_words_up_to_rotation": [
            {"largest_ratio": r, "pairs": w} for r, w in sorted(high_ratio_words)
        ],
        "one_pass_peak_witness": first_pass_witness,
        "max_peak": max_peak,
        "max_recurrent_peak": max_recurrent,
        "max_response_period_ratio": max_ratio,
        "peak_witness": describe_witness(peak_word, max_peak, "peak"),
        "recurrent_peak_witness": describe_witness(recurrent_word, max_recurrent, "recurrent"),
        "ratio_witness": describe_witness(ratio_word, max_ratio, "ratio"),
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
