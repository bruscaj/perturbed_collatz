"""Exact arithmetic certificate for inverse arithmetic-progression steering.

The fixed forcing is (+1, 0, -1), with the shortcut Collatz operator.
No dependency on the existing repository verifier is used.

Run ``python3 certify_ap.py`` to regenerate certificate.json.
Run ``python3 certify_ap.py --demo`` for constructive all-phase examples.
The universal theorem is in README.md; the examples are implementation checks.
"""

from __future__ import annotations

if not __debug__:
    raise SystemExit('Certificate checks require assertions; run without -O.')

import json
import sys
from itertools import product

WORD = (1, 0, -1)
LENGTH = 18
SCALE = 1 << LENGTH


def step(n: int, d: int) -> int:
    return (n // 2 if n % 2 == 0 else (3 * n + 1) // 2) + d


def advance(n: int, phase: int, length: int) -> tuple[int, int]:
    odd = 0
    for j in range(length):
        odd += n % 2
        n = step(n, WORD[(phase + j) % 3])
    return n, odd


def branches() -> list[dict]:
    """Compose the all-even itinerary and the 18 one-odd itineraries backwards."""
    rows = []
    for odd_position in [None, *range(LENGTH)]:
        c, denominator, odd = 0, 1, 0
        for j, d in enumerate(reversed(WORD * 6)):
            epsilon = int(j == odd_position)
            c = 2 * c - (2 * d + epsilon) * denominator
            denominator *= 3**epsilon
            odd += epsilon
        assert denominator == 3**odd
        r = c * pow(denominator, -1, SCALE) % SCALE
        value, actual_odd = advance(r, 0, LENGTH)
        # Independent direct forward replay of the representative residue.
        assert actual_odd == odd
        assert denominator * r - SCALE * value == c
        assert 2 * (SCALE - denominator) + c > 0
        # Every integral child is strictly larger than a parent y >= 2.
        rows.append({"odd": odd, "offset": c, "residue_mod_2_18": r})
    assert len({r["residue_mod_2_18"] for r in rows}) == 19
    return rows


BRANCHES = branches()


def kernel_witness(y: int, desired_mod9: int) -> tuple[int, int, int, int]:
    """Return (child, physical_length, branch_index, extra_even_lap)."""
    assert y >= 2 and y % 3
    assert desired_mod9 in (1, 2, 4, 5, 7, 8)
    for branch_index, record in enumerate(BRANCHES):
        x, remainder = divmod(SCALE * y + record["offset"], 3 ** record["odd"])
        if remainder or not x % 3:
            continue
        for extra in (0, 1):
            z = x if not extra else 8 * x + 6
            if z % 9 == desired_mod9:
                return z, LENGTH + 3 * extra, branch_index, extra
    raise AssertionError("Finite steering kernel failed")


def certificate() -> dict:
    rows = []
    for residue in range(27):
        if not residue % 3:
            continue
        y = residue if residue >= 2 else residue + 27
        witnesses = []
        for target_class in (1, 2, 4, 5, 7, 8):
            x, length, branch_index, extra = kernel_witness(y, target_class)
            assert x > y and x % 9 == target_class
            assert advance(x, 0, length)[0] == y
            x2, length2, index2, extra2 = kernel_witness(y + 27, target_class)
            assert (length2, index2, extra2) == (length, branch_index, extra)
            increment = (8**extra) * SCALE * 27 // (3 ** BRANCHES[branch_index]["odd"])
            assert x2 == x + increment and increment % 9 == 0
            witnesses.append({"target_mod9": target_class, "branch_index": branch_index,
                              "extra_even_lap": extra, "physical_steps": length})
        rows.append({"parent_mod27": residue, "witnesses": witnesses})
    return {
        "forcing": list(WORD),
        "eligible_parent": "y >= 2, y not divisible by 3, phase zero",
        "block_length": LENGTH,
        "guarantee": "Every unit class modulo 9 has an inverse witness in 18 or 21 physical steps",
        "inverse_formula": "x = (2^18 * y + offset) / 3^odd",
        "branches": BRANCHES,
        "rows": rows,
        "all_even_lap": "A(y) = 8*y+6",
        "even_lap_pair": "A^(2*j)(y) = (64^j*(7*y+6)-6)/7",
        "analytic_kernel": [
            {"parent_mod9": r, "apply_A_first": r in (5, 7),
             "good_mod9": (8 * r + 6) % 9 if r in (5, 7) else r,
             "one_odd_offset": (0, -2, 5)[((8 * r + 6) if r in (5, 7) else r) % 3]}
            for r in (1, 2, 4, 5, 7, 8)
        ],
        "explicit_constructor_moduli": "2^a * 3^b * 7^c, for all a,b,c >= 0",
        "full_theorem_moduli": "all positive moduli, after the positive modular-word completion lemma",
        "claim_boundary": "Inverse accessibility and sufficient sets; no proof of global capture or divergence",
    }


def eligible_predecessor(y: int) -> int:
    """Eligible predecessor exactly two phase-zero returns before any y >= 0."""
    assert y >= 0
    if y % 3:
        s = 64 * y + 54
    else:
        t = y // 3
        s = 64 * t + (6 if t % 3 else 16)
    assert s >= 2 and s % 3 and advance(s, 0, 6)[0] == y
    return s


def unit_steer(y: int, desired: int, k3: int, k7: int) -> tuple[int, int]:
    """Backward steering to desired modulo 3^k3 * 7^k7, desired a 3-unit.

    The linear search for the exponent is intentionally simple. The proof uses
    LTE and CRT, rather than treating the finite loop as a universal proof.
    """
    assert y >= 2 and y % 3 and k3 >= 1 and k7 >= 0 and desired % 3
    mod3, mod7 = 3**k3, 7**k7
    q, length = y, 0
    if q % 9 in (5, 7):
        q, length = 8 * q + 6, 3
    assert q % 9 in (1, 2, 4, 8)
    offset = (0, -2, 5)[q % 3]
    output_mod3 = ((8 * q + offset) // 3) % 3
    extra = int(desired % 3 != output_mod3)
    output_modulus = mod3 * mod7
    output_class = desired % output_modulus
    if extra:
        output_class = (output_class - 6) * pow(8, -1, output_modulus) % output_modulus
    modulus = 3 ** (k3 + 1) * mod7
    input_class = ((3 * output_class - offset) * pow(8, -1, modulus)) % modulus
    assert input_class % 9 == q % 9
    period = 3 ** (k3 - 1) * mod7
    residue = q % modulus
    exponent = None
    for j in range(period):
        if residue == input_class:
            exponent = j
            break
        residue = (64 * residue + 54) % modulus
    assert exponent is not None
    z = (64**exponent * (7 * q + 6) - 6) // 7
    z, remainder = divmod(8 * z + offset, 3)
    assert remainder == 0
    if extra:
        z = 8 * z + 6
    assert z % output_modulus == desired % output_modulus
    return z, length + 6 * exponent + 3 + 3 * extra


def ternary_seven_steer(y: int, desired: int, k3: int, k7: int) -> tuple[int, int]:
    """No restriction on the requested output class modulo 3^k3 * 7^k7."""
    modulus = 3 ** (k3 + 1) * 7**k7
    parent_class = ((3 * desired + 2) * pow(8, -1, modulus)) % modulus
    assert parent_class % 3 == 1
    z, length = unit_steer(y, parent_class, k3 + 1, k7)
    x, remainder = divmod(8 * z - 2, 3)
    assert remainder == 0 and advance(x, 0, 3)[0] == z
    assert x % (3**k3 * 7**k7) == desired % (3**k3 * 7**k7)
    return x, length + 3


def ap_predecessor(target: int, arrival_phase: int, launch_phase: int,
                   residue: int, a2: int, b3: int, c7: int) -> tuple[int, int]:
    """Construct a positive seed in a requested AP reaching a safe augmented target."""
    assert 0 <= arrival_phase < 3 and 0 <= launch_phase < 3
    assert target >= (0 if arrival_phase == 0 else 1)
    if arrival_phase == 0:
        phase0_target, tail = target, 0
    elif arrival_phase == 1:
        phase0_target, tail = 2 * (target - 1), 1
    else:
        phase0_target, tail = 4 * target - 2, 2
    y = eligible_predecessor(phase0_target)
    tail += 6

    length = max(1, a2)
    while (launch_phase + length) % 3:
        length += 1
    scale = 2**length
    r = residue % 2**a2
    value, odd = advance(r, launch_phase, length)
    offset = 3**odd * r - scale * value
    # If the representative r=0 is unsafe at its phase, this calculation still
    # takes place in Z; the eventual positive seed is safe by admissibility.
    while scale * y + offset <= 0:
        y = 8 * y + 6
        tail += 3
    modulus = 3 ** (odd + b3) * 7**c7
    desired = ((3**odd * residue - offset) * pow(scale, -1, modulus)) % modulus
    z, middle = ternary_seven_steer(y, desired, odd + b3, c7)
    x, remainder = divmod(scale * z + offset, 3**odd)
    assert remainder == 0 and x > 0
    assert x % (2**a2 * 3**b3 * 7**c7) == residue % (2**a2 * 3**b3 * 7**c7)
    total = length + middle + tail
    assert (launch_phase + total) % 3 == arrival_phase
    assert advance(x, launch_phase, total)[0] == target
    return x, total


def demos() -> dict:
    cases = []
    parameters = [(0, 0, 0), (3, 0, 0), (0, 3, 0), (0, 0, 2),
                  (2, 1, 1), (3, 2, 1)]
    for arrival_phase, launch_phase, (a2, b3, c7) in product(range(3), range(3), parameters):
        target = 0 if arrival_phase == 0 else 1
        modulus = 2**a2 * 3**b3 * 7**c7
        for residue in {0, 1 % modulus, (modulus - 1) % modulus}:
            x, length = ap_predecessor(target, arrival_phase, launch_phase,
                                      residue, a2, b3, c7)
            cases.append({"target": target, "arrival_phase": arrival_phase,
                          "launch_phase": launch_phase, "modulus": modulus,
                          "residue": residue, "steps": length,
                          "seed_bits": x.bit_length()})
    return {"exact_constructive_examples": len(cases),
            "largest_step_count": max(c["steps"] for c in cases),
            "largest_seed_bits": max(c["seed_bits"] for c in cases),
            "cases": cases}


if __name__ == "__main__":
    print(json.dumps(demos() if "--demo" in sys.argv else certificate(), indent=2))
