"""Literal finite Syracuse checks and a rational enclosure of a stated series.

No candidate proof/checker is imported. No infinite headline is certified.
All acceptance checks use explicit exceptions, including with Python -O.
"""
from fractions import Fraction as Q
from itertools import product
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def valuation(n):
    require(n > 0, "valuation requires a positive integer")
    k = 0
    while n % 2 == 0:
        n //= 2
        k += 1
    return k


def stride(x):
    k = valuation(3*x+1)
    return (3*x+1)//2**k, k


def window(x, h):
    result = []
    for _ in range(h):
        r = 0
        while True:
            x, k = stride(x)
            r += 1
            if k >= 2:
                break
        result.append(r)
    return tuple(result)


def run():
    cylinders = 0
    for t in range(1, 5):
        for ks in product((1, 2, 3), repeat=t):
            modulus = 2**(1+sum(ks))
            matches = []
            for x in range(1, modulus, 2):
                y, observed = x, []
                for _ in ks:
                    y, k = stride(y)
                    observed.append(k)
                if tuple(observed) == ks:
                    matches.append(x)
            require(len(matches) == 1, f"cylinder multiplicity: {ks}")
            for offset in (1, 2, 7):
                y = matches[0] + offset*modulus
                for expected in ks:
                    y, k = stride(y)
                    require(k == expected, "lifted cylinder changed valuation")
            cylinders += 1

    seeds = 0
    for x in range(1, 20000, 2):
        old = window(x, 4)
        y, k = stride(x)
        new = window(y, 3)
        require(old[0] == valuation(x+1), "remaining block length")
        predicted = ((old[0]-1,)+old[1:3]) if k == 1 else old[1:4]
        require(new == predicted, "literal block-window transition")
        seeds += 1

    # Independent arithmetic routes: direct sum of bad exit masses vs a
    # bit-length geometric-sum formula. 3^r and 2^r cannot be equal for r>0.
    direct, formula = Q(), Q()
    for r in range(1, 81):
        a, k, bad = Q(3, 2)**r, 2, Q()
        while Q(2)**(k-1) < a:
            bad += Q(1, 2**(r+k))
            k += 1
        require(Q(2)**(k-1) != a, "unexpected power equality")
        direct += bad
        threshold = (3**r).bit_length()-r
        formula += Q(1, 2**r)*(Q(1, 2)-Q(1, 2**threshold))
    require(direct == formula, "independent series sums differ")
    # Each omitted term is nonnegative and ≤2^(-r-1). Its geometric tail
    # after M=80 is 2^-81. This encloses the series, not the full infimum.
    tail = Q(1, 2**81)

    # A zero symbolic gain counts as failure: phi(r)=(r-1)ln(3/2), x=3.
    x = 3
    y, _ = stride(x)
    actual_ratio = Q(y, x)*Q(3, 2)**(valuation(y+1)-valuation(x+1))
    require(actual_ratio == Q(10, 9) > 1, "equality failure witness changed")
    require(stride(1)[0] == 1 and window(1, 4) == (1, 1, 1, 1), "fixed point")
    try:
        require(actual_ratio < 1, "mutated equality-as-success rejected")
    except ValueError:
        pass
    else:
        raise ValueError("equality mutation survived")
    return {
        "scope": "finite arithmetic only; not a proof of density or an infimum",
        "valuation_patterns": {"lengths": [1, 4], "letters": [1, 2, 3]},
        "exhausted_cylinders": cylinders,
        "odd_seeds": {"first": 1, "last": 19999, "count": seeds},
        "series_terms": 80,
        "series_lower": str(formula),
        "series_upper": str(formula+tail),
        "series_interval_width": str(tail),
        "equality_failure_ratio": str(actual_ratio),
        "negative_controls_rejected": ["zero symbolic gain declared successful"],
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
