"""Exact 24-step inverse-tree certificate, independent of the C++ census.

Enumerate all parity words with at most eight odd inputs by composing inverse
operations. Independently replay the unique input residue for each formula.
The theorem and counting proof are in GROWTH.md. Standard library only.
"""

if not __debug__:
    raise SystemExit('Certificate checks require assertions; run without -O.')

from collections import Counter
from decimal import Decimal, localcontext
from hashlib import sha256
from itertools import combinations
from math import comb
from struct import pack
import json
import sys

LENGTH = 24
ODD_LIMIT = 8
SCALE = 2**LENGTH
THRESHOLD = 34
EXPECTED = [1, 4, 17, 35, 57, 69, 53, 32, 13]
WORD = (1, 0, -1) * 8


def advance(n):
    odd = 0
    for d in WORD:
        epsilon = n % 2
        odd += epsilon
        n = ((3 * n + 1) // 2 if epsilon else n // 2) + d
    return n, odd


def inverse_offsets(odd):
    for positions in combinations(range(LENGTH), odd):
        mask = sum(1 << j for j in positions)
        c, denominator = 0, 1
        for j, d in enumerate(reversed(WORD)):
            epsilon = (mask >> j) & 1
            c = 2 * c - (2 * d + epsilon) * denominator
            if epsilon:
                denominator *= 3
        assert denominator == 3**odd
        yield c


def exponent_approx(multiplicities):
    with localcontext() as context:
        context.prec = 60
        lo, hi = Decimal(0), Decimal(1)
        for _ in range(180):
            s = (lo + hi) / 2
            mass = sum(Decimal(m) * (Decimal(3**o) / SCALE)**s
                       for o, m in enumerate(multiplicities))
            if mass > 1:
                lo = s
            else:
                hi = s
        return f"{(lo+hi)/2:.18f}"


def exact_mass_bound(numerator, denominator, upper=False):
    """Certify mass at rational s by integer powers, with denominator 10^9."""
    grid = 10**9
    bounds = []
    for o in range(ODD_LIMIT + 1):
        target = grid**denominator * 3**(o * numerator)
        factor = SCALE**numerator
        lo, hi = 0, grid + 1
        while hi - lo > 1:
            mid = (lo + hi) // 2
            if mid**denominator * factor <= target:
                lo = mid
            else:
                hi = mid
        assert lo**denominator * factor <= target
        assert (lo + 1)**denominator * factor > target
        bounds.append(lo + int(upper))
    total = sum(m * b for m, b in zip(EXPECTED, bounds))
    assert total < grid if upper else total > grid
    return {"exponent_numerator": numerator, "exponent_denominator": denominator,
            "bound": "strict upper" if upper else "lower",
            "rational_denominator": grid, "term_numerators": bounds,
            "weighted_sum_numerator": total,
            "relation_to_one": "less" if upper else "greater"}


def certificate():
    seen = bytearray(SCALE)
    digest = sha256()
    groups = []
    for o in range(ODD_LIMIT + 1):
        d = 3**o
        modulus = 3 * d
        inverse_scale = pow(SCALE, -1, d)
        inverse_denominator = pow(d, -1, SCALE)
        counts = [0] * modulus
        words = 0
        min_c, max_c = None, None
        for c in inverse_offsets(o):
            r = c * inverse_denominator % SCALE
            assert not seen[r]
            seen[r] = 1
            y, actual_odd = advance(r)
            assert actual_odd == o
            assert d * r - SCALE * y == c
            assert c + d <= SCALE
            assert THRESHOLD * (SCALE - d) + c > 0
            digest.update(pack("<BqI", o, c, r))
            words += 1
            min_c = c if min_c is None else min(min_c, c)
            max_c = c if max_c is None else max(max_c, c)
            parent_class = -c * inverse_scale % d
            for t in range(3):
                parent = parent_class + t * d
                child, remainder = divmod(SCALE * parent + c, d)
                assert remainder == 0
                if parent % 3 and child % 3:
                    counts[parent] += 1
        assert words == comb(LENGTH, o)
        unit_counts = [counts[r] for r in range(modulus) if r % 3]
        assert min(unit_counts) == EXPECTED[o]
        groups.append({
            "odd_count": o,
            "formulas": words,
            "parent_modulus": modulus,
            "counts_at_unit_residues_in_ascending_order": unit_counts,
            "minimum": min(unit_counts), "maximum": max(unit_counts),
            "count_histogram": dict(sorted(Counter(unit_counts).items())),
            "min_offset": min_c, "max_offset": max_c,
            "minimum_growth_numerator_at_34": THRESHOLD * (SCALE - d) + min_c,
            "size_bound_slack": SCALE - d - max_c,
        })
        print(f"Certified odd count {o}: {words} formulas, minimum {min(unit_counts)}", file=sys.stderr)
    assert sum(seen) == sum(comb(LENGTH, o) for o in range(ODD_LIMIT + 1))
    even_mass = sum(EXPECTED[o] * 3**(o // 2) for o in range(0, ODD_LIMIT + 1, 2))
    odd_mass = sum(EXPECTED[o] * 3**((o - 1) // 2) for o in range(1, ODD_LIMIT + 1, 2))
    assert (even_mass, odd_mass) == (3049, 1594)
    assert even_mass + odd_mass > 2 ** (LENGTH // 2)
    return {
        "forcing": [1, 0, -1], "physical_length": LENGTH,
        "return_map_iterate": 8, "odd_limit": ODD_LIMIT,
        "eligible_target": "phase zero, y >= 34, y not divisible by 3",
        "minimum_counts": EXPECTED, "children_per_vertex": sum(EXPECTED),
        "formula_count": sum(g["formulas"] for g in groups),
        "formula_digest_order": "odd count, then lexicographic odd positions in reverse-time order",
        "formula_digest_encoding": "little-endian uint8 odd count, int64 offset, uint32 starting residue",
        "formula_sha256": digest.hexdigest(),
        "growth_equation": "sum_o minimum_counts[o]*(2^24/3^o)^(-delta)=1",
        "exponent_approx": exponent_approx(EXPECTED),
        "square_root_mass": {"rational_part": even_mass, "sqrt3_coefficient": odd_mass,
                             "denominator": 4096, "greater_than_one_using_sqrt3_gt_1": True},
        "certified_exponent_interval": [exact_mass_bound(107, 200), exact_mass_bound(67, 125, upper=True)],
        "groups": groups,
    }


if __name__ == "__main__":
    print(json.dumps(certificate(), indent=2))
