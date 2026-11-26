#!/usr/bin/env python3
"""Regenerate the small exact examples used in the expanded exposition.

The parameters below are fixed examples, not a bounded test of a universal
theorem. Physical and positive-coordinate replay are implemented separately.
All JSON fields must agree with the regenerated record.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
import json
from pathlib import Path


HERE = Path(__file__).resolve().parent


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def strict_json(text: str) -> dict:
    def unique_pairs(items):
        result = {}
        for key, value in items:
            require(key not in result, "duplicate JSON key")
            result[key] = value
        return result

    def reject_number(value):
        raise ValueError("noninteger or nonfinite JSON number: " + value)

    return json.loads(text, object_pairs_hook=unique_pairs,
                      parse_float=reject_number, parse_constant=reject_number)


def canonical(data: dict) -> str:
    return json.dumps(data, sort_keys=True, separators=(",", ":"), allow_nan=False)


def shortcut(n: int) -> int:
    return n // 2 if n % 2 == 0 else (3 * n + 1) // 2


def physical(seed: int, impulses: list[int], steps: int, phase: int = 0) -> list[int]:
    result = [seed]
    for tick in range(steps):
        result.append(shortcut(result[-1]) + impulses[(phase + tick) % len(impulses)])
    return result


def letter_step(letter: str, z: int) -> int:
    require(z > 0, "positive-coordinate replay received a nonpositive input")
    if letter == "T":
        return z // 2 if z % 2 == 0 else (3 * z + 1) // 2
    require(letter == "U", "invalid common letter")
    return 3 * z // 2 if z % 2 == 0 else (z + 1) // 2


def letters(seed: int, word: str) -> list[int]:
    result = [seed]
    for letter in word:
        result.append(letter_step(letter, result[-1]))
    return result


def primitive_period(word: list[int]) -> int:
    for period in range(1, len(word) + 1):
        if len(word) % period == 0 and all(word[i] == word[i % period] for i in range(len(word))):
            return period
    raise ValueError("nonempty word was required")


def tail_to_base(seed: int) -> list[int]:
    values = [seed]
    while values[-1] > 2:
        require(len(values) < 10000, "the example tail failed to reach the base")
        values.append(shortcut(values[-1]))
    return values


def closed_orbit(seed: int, impulses: list[int]) -> tuple[list[int], int]:
    state = (seed, 0)
    seen: dict[tuple[int, int], int] = {}
    values = []
    while state not in seen:
        require(len(values) < 10000, "the example orbit failed to close")
        seen[state] = len(values)
        value, phase = state
        values.append(value)
        state = (shortcut(value) + impulses[phase], (phase + 1) % len(impulses))
    return values, seen[state]


def foundations() -> dict:
    impulses = [1, 0, -1]
    height = [0, 1, 1]
    paths = []
    for phase in range(3):
        path = physical(5, impulses, 6, phase)
        normalized = [n + 1 - height[(phase + k) % 3] for k, n in enumerate(path)]
        word = "".join("T" if height[(phase + k) % 3] else "U" for k in range(6))
        require(normalized == letters(normalized[0], word), "height conjugacy example failed")
        paths.append({"launch_phase": phase, "physical": path, "positive": normalized})
    parity = [1, 1, 0]
    realizers = [n for n in range(8) if [x % 2 for x in physical(n, impulses, 3)[:-1]] == parity]
    require(realizers == [5], "wrong three-step parity residue")
    bias = [0]
    for j, bit in enumerate(parity):
        bias.append(3 ** bit * bias[-1] + 2 ** j * (bit + 2 * impulses[j]))
    worked = []
    for n, steps in [(5, 3), (13, 3), (61, 6)]:
        worked.append({"seed": n, "physical": physical(n, impulses, steps)})
    require(worked[-1]["physical"][-1] == (81 * 61 + 51) // 64, "two-lap example failed")
    repeated = []
    for copies in range(1, 5):
        n = 8 ** copies - 3
        path = physical(n, impulses, 3 * copies)
        require([x % 2 for x in path[:-1]] == parity * copies, "repeated itinerary differs")
        require(path[-1] == 9 ** copies - 3, "repeated-prefix affine identity differs")
        repeated.append({"copies": copies, "seed": n, "endpoint": path[-1], "physical": path})
    return {
        "impulses": impulses, "height": height, "seed": 5, "steps": 6,
        "ordinary": physical(5, [0], 6), "phase_paths": paths,
        "parity_example": {"input_parities": parity, "modulus": 8, "residue": 5,
                           "bias_sequence": bias, "numerator_scale": 9, "numerator_bias": 3,
                           "quotient_parameter_scale": 9, "quotient_parameter_bias": 6,
                           "twice_repeated_prefix_modulus": 64, "twice_repeated_prefix_residue": 61,
                           "worked_trajectories": worked, "repeated_prefix_examples": repeated},
    }


def impulse_pairs() -> dict:
    first_tail = tail_to_base(3)
    escaping = []
    negative_tails = []
    for b, value in enumerate(first_tail[:-1]):
        after_minus = shortcut(value) - 1
        tail = tail_to_base(after_minus)
        negative_tails.append({"b": b, "before_minus": value,
                               "after_minus": after_minus, "ordinary_tail": tail})
        escaping.extend({"b": b, "a": a, "endpoint": endpoint}
                        for a, endpoint in enumerate(tail[:-1]))
    require(len(escaping) == 15, "one-pair escaping list is incomplete")
    layers = [[0, 1, 2]]
    for sign in [1, -1]:
        layer = set()
        for value in layers[-1]:
            current = shortcut(value) + sign
            visited = set()
            while current not in visited:
                require(len(visited) < 10000, "signed-layer tail did not close")
                visited.add(current)
                current = shortcut(current)
            layer.update(visited)
        layers.append(sorted(layer))
    require([len(x) for x in layers[1:]] == [6, 14], "signed layer sizes differ")
    impulse_word = [1, 0, -1, 0, 0, 0, 0]
    values, start = closed_orbit(1, impulse_word)
    require(start == 0, "the one-pair witness unexpectedly has a transient")
    rows = []
    for tick in range(0, len(values), 7):
        segment = physical(values[tick], impulse_word, 7)
        rows.append({"start": segment[0], "end": segment[-1], "peak": max(segment),
                     "physical": segment})
    doubled, double_start = closed_orbit(1, impulse_word * 2)
    require(double_start == 0 and len(doubled) == 98, "doubled-clock period differs")
    require(primitive_period(values) == 49, "scalar cycle was not primitive")
    return {
        "root_seed": 1, "ordinary_tail_after_plus": first_tail,
        "negative_tails": negative_tails, "escaping_pairs": escaping,
        "signed_layers": layers,
        "witness": {"pair": [1, 4], "impulses": impulse_word,
                    "primitive_forcing_period": primitive_period(impulse_word),
                    "lap_rows": rows, "scalar_cycle": values,
                    "peak": max(values), "least_scalar_period": primitive_period(values),
                    "augmented_period": len(values), "doubled_clock_augmented_period": len(doubled)},
    }


def synchronization() -> dict:
    word = "UTTUTUUUUT"
    initial = list(range(1, 7))
    reference = letters(1, word)
    tracks = {str(seed): letters(seed, word) for seed in initial}
    ensembles = [sorted({track[tick] for track in tracks.values()}) for tick in range(len(word) + 1)]
    for tick, letter in enumerate(word):
        require(reference[tick] in (1, 2, 3), "reference left its protected set")
        require(not (reference[tick] == 3 and letter == "T"), "forbidden reference transition")
    require(reference[-1] == 1 and ensembles[-1] == [1], "common reset failed")
    height = [int(letter == "T") for letter in word]
    impulses = [height[(i + 1) % len(word)] - height[i] for i in range(len(word))]
    response = [reference[i] - 1 + height[i] for i in range(len(word))]
    require(all(shortcut(response[i]) + impulses[i] == response[(i + 1) % len(word)]
                for i in range(len(word))), "physical reference response does not close")
    reset_paths = []
    for seed in range(6):
        path = physical(seed, impulses, len(word))
        require(path[-1] == 0, "phase-zero physical reset failed")
        require([path[k] + 1 - height[k % len(word)] for k in range(len(path))]
                == tracks[str(seed + 1)], "independent physical replay disagrees with normalized replay")
        reset_paths.append({"seed": seed, "physical": path})
    counterexample = physical(5, impulses, len(word), 1)
    require(counterexample[-1] == 3 and response[1] == 1, "rotation counterexample was lost")
    merger_rows = [(1, [2, 5], "UTU"), (1, [3], "TU"), (1, [4], "T"),
                   (2, [1, 3, 4], "TUTU"), (2, [5], "U"),
                   (3, [1, 2, 5], "UTUTU"), (3, [4], "UTTU")]
    count = 0
    for r, comparisons, merger_word in merger_rows:
        rpath = letters(r, merger_word)
        for k, letter in enumerate(merger_word):
            require(not (rpath[k] == 3 and letter == "T"), "merger table violates controller")
        for comparison in comparisons:
            require(letters(comparison, merger_word)[-1] == rpath[-1], "merger table entry fails")
            count += 1
    return {
        "word": word, "initial_ensemble": initial, "reference": reference,
        "tracks": tracks, "ensembles": ensembles, "cardinalities": list(map(len, ensembles)),
        "height": height, "impulses": impulses, "physical_response": response,
        "primitive_forcing_period": primitive_period(impulses),
        "phase_zero_reset_paths": reset_paths,
        "rotation_failure": {"seed": 5, "phase": 1, "physical": counterexample,
                             "response_at_phase": response[1], "endpoint": counterexample[-1]},
        "protected_merger_table_cases_checked": count,
    }


def analytic_constants() -> dict:
    f = Fraction
    matrix = [[f(20, 39), f(19, 39), f(0)],
              [f(111, 206), f(0), f(95, 206)], [f(0), f(1), f(0)]]
    stationary = [f(4329, 10048), f(3914, 10048), f(1805, 10048)]
    require([sum(stationary[i] * matrix[i][j] for i in range(3)) for j in range(3)]
            == stationary, "stationary distribution differs")
    require(f(841, 1000) ** 4 > f(1, 2), "fourth-root upper bound fails")
    require(f(1107, 1000) ** 4 > f(3, 2), "second fourth-root upper bound fails")
    gains = [f(974, 975), f(1027083, 1030000), f(369, 370)]
    require(all(x < f(999, 1000) for x in gains), "drift gain bound fails")
    require(8 * 111 ** 4 < 200 ** 4, "concavity error bound fails")
    require(19 * 16000 ** 4 >= 25 * 2000 ** 5, "geometric drift threshold fails")
    require(f(95, 206) > f(9, 20) and f(9, 20) ** 4 > f(1, 25), "closure bound fails")
    return {"stationary_distribution": [str(x) for x in stationary],
            "gain_upper_bounds": [str(x) for x in gains], "threshold": 16000,
            "checks_use_exact_rational_or_integer_arithmetic": True}


def regenerate() -> dict:
    return {"schema_version": 1,
            "scope": "Finite worked examples; universal conclusions use the written proofs",
            "model": "Signed shortcut Collatz plus post-step impulse; zero continues",
            "foundations": foundations(), "impulse_pairs": impulse_pairs(),
            "synchronization": synchronization(), "analytic_constants": analytic_constants()}


def check() -> dict:
    """Check the complete saved record and return the regenerated examples."""
    data = regenerate()
    stored = strict_json((HERE / "examples.json").read_text())
    require(canonical(stored) == canonical(data), "examples.json differs from complete exact regeneration")
    return data


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="Regenerate the accompanying examples.json")
    args = parser.parse_args()
    target = HERE / "examples.json"
    if args.write:
        data = regenerate()
        target.write_text(json.dumps(data, indent=2) + "\n")
    else:
        check()
    print("PASS: seed/phase paths, affine examples, 15 escaping pairs, signed layers, 49/98-step cycles,")
    print("      common reset and rotation failure, 12 merger cases, and exact analytical constants")


if __name__ == "__main__":
    main()
