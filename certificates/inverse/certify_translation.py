"""Check positive inverse words that complete a ternary prefix into translation.

These finite examples check the algebra of the general proof. They are not an
exhaustive search over moduli or seeds. No enormous ancestor from a fixed root
is materialized: the full proof supplies it by ternary steering.
"""

if not __debug__:
    raise SystemExit('Certificate checks require assertions; run without -O.')

import json
from math import gcd

OFFSETS = (0, -2, 5)


def compose(word):
    multiplier, offset, denominator = 1, 0, 1
    for branch in word:
        multiplier *= 8
        offset = 8 * offset + OFFSETS[branch] * denominator
        denominator *= 3
    return multiplier, offset, denominator


def domain(word):
    multiplier, offset, denominator = compose(word)
    return (-offset * pow(multiplier, -1, denominator)) % denominator


def apply_word(n, word):
    for branch in word:
        assert n % 3 == branch
        n, remainder = divmod(8 * n + OFFSETS[branch], 3)
        assert remainder == 0
    return n


def prefix(residue, k):
    n = residue % (3**k) + 3**k
    word = []
    for _ in range(k):
        branch = n % 3
        word.append(branch)
        n = (8 * n + OFFSETS[branch]) // 3
    assert domain(word) == residue % (3**k)
    return word


def multiplicative_order(a, m):
    n, e = a % m, 1
    while n != 1:
        n, e = n * a % m, e + 1
    return e


def complete(m, residue, k):
    assert m > 1 and gcd(m, 6) == 1
    e = multiplicative_order(8 * pow(3, -1, m), m)
    exponent = m * e
    w = prefix(residue, k)
    inverse = [branch for branch in reversed(w) for _ in range(exponent - 1)]
    translation = ([0] + [1] * (exponent - 1)) * 4
    v = w + inverse + translation
    assert len(v) == exponent * (k + 4)
    a, c, d = compose(v)
    assert a * pow(d, -1, m) % m == 1
    assert c * pow(d, -1, m) % m == 1
    assert domain(v) % 3**k == residue % 3**k
    whole = v * m
    whole_domain = domain(whole)
    n = whole_domain + 3 ** len(whole)
    assert n >= 2
    residues = []
    for _ in range(m):
        assert n % 3**k == residue % 3**k
        residues.append(n % m)
        old = n
        n = apply_word(n, v)
        assert n > old
    assert sorted(residues) == list(range(m))
    return {"modulus_coprime_to_6": m, "ternary_precision": k,
            "ternary_residue": residue % 3**k,
            "common_permutation_exponent": exponent,
            "completed_word_length": len(v),
            "repetition_domain_precision": len(whole),
            "block_residues_mod_m": residues,
            "domain_bit_length": whole_domain.bit_length()}


def certificate():
    rows = []
    for m in (5, 7, 11, 13, 25):
        for k in (0, 1, 2):
            for residue in {0, 1 % (3**k), (3**k - 1) % (3**k)}:
                rows.append(complete(m, residue, k))
    return {"checked_parameter_instances": len(rows),
            "all_instances_passed": True, "rows": rows}


if __name__ == "__main__":
    print(json.dumps(certificate(), indent=2))
