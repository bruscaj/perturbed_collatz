"""Independent finite source-cap/depth oracle. Exact fractions only.
This checks finite translation; it proves no pressure or entropy limit.
Run python3 <this file>. All assertions replaced by explicit exceptions.
"""
from collections import Counter
from fractions import Fraction
from itertools import combinations
import json


def require(ok, message):
    if not ok:
        raise ValueError(message)


def compare_models(expected, actual):
    require(expected == actual, "source/depth dictionaries differ")


def floor_log2(q):
    if q <= 0:
        raise ValueError("positive rational required")
    k = q.numerator.bit_length() - q.denominator.bit_length()
    power = Fraction(2**k) if k >= 0 else Fraction(1, 2**(-k))
    return k if power <= q else k - 1


def compositions(total, length):
    for cuts in combinations(range(1, total), length - 1):
        points = (0,) + cuts + (total,)
        yield tuple(b-a for a,b in zip(points, points[1:]))


def source_words(n):
    s = (3**n).bit_length()
    y = Fraction(2**s, 3**n) # exact 2**closing_defect
    cap = [floor_log2(y * 3**t) for t in range(n+1)]
    result = {}
    for word in compositions(s,n):
        prefixes = [0]
        for k in word:
            prefixes.append(prefixes[-1] + k)
        if any(prefixes[t] > cap[t] for t in range(n)):
            continue
        reward = sum((Fraction(2**prefixes[t],3**t) for t in range(n)), Fraction(0))
        depths = tuple(cap[t]-prefixes[t] for t in range(n+1))
        result[word] = (depths,reward)
    return y,cap,result


def depth_words(n,y,cap):
    # Breadth expansion of exact depth states, then recover literal exponents.
    paths = [(0,)]
    for t in range(n):
        g = cap[t+1]-cap[t]
        paths = [path+(d,) for path in paths
                 for d in range(path[-1]+g)
                 if t < n-1 or d == 0]
    result = {}
    for path in paths:
        word = tuple(path[t]+cap[t+1]-cap[t]-path[t+1] for t in range(n))
        normalized = sum((Fraction(2**cap[t],3**t*2**path[t])/y for t in range(n)), Fraction(0))
        reward = y * normalized # restore the literal source reward
        result[word] = (path,reward)
    return result


def main():
    rows=[]
    smallest_defect=Fraction(2)
    for n in range(1,15):
        y,cap,literal=source_words(n)
        depth=depth_words(n,y,cap)
        compare_models(literal, depth)
        rung = y < smallest_defect
        smallest_defect = min(y,smallest_defect)
        base_cap=[floor_log2(Fraction(3**t)) for t in range(n)]
        require(not rung or cap[:-1] == base_cap, f"rung cap mismatch at {n}")
        maximum=max(r for _,r in literal.values())
        direct_max=sum((Fraction(2**cap[t],3**t) for t in range(n)), Fraction(0))
        require(maximum == direct_max, f"source maximum mismatch at {n}")
        phase_zero_max=sum((Fraction(2**base_cap[t],3**t) for t in range(n)),Fraction(0))
        require(maximum >= phase_zero_max, "relaxed cap maximum fell")
        rows.append({"n":n,"rung":rung,"source_words":len(literal),
                     "source_max":[maximum.numerator,maximum.denominator],
                     "phase_zero_max":[phase_zero_max.numerator,phase_zero_max.denominator],
                     "counts_at_fixed_phase_zero_max":sum(r>=phase_zero_max for _,r in literal.values())})
    y, cap, literal = source_words(2)
    bad_normalization={word:(path,reward/y) for word,(path,reward) in literal.items()}
    missing_word=dict(literal)
    missing_word.pop(next(iter(missing_word)))
    bad_endpoint=dict(literal)
    word=next(iter(bad_endpoint))
    value=bad_endpoint.pop(word)
    bad_endpoint[word[:-1]+(word[-1]+1,)]=value
    for name, corrupted in (("normalization",bad_normalization),("missing_word",missing_word),("endpoint",bad_endpoint)):
        try:
            compare_models(literal, corrupted)
        except ValueError:
            pass
        else:
            raise ValueError(f"negative control undetected: {name}")
    print(json.dumps({"negative_controls_rejected":["normalization","missing_word","endpoint"],"scope":"exact finite source/depth equality; no infinite theorem",
                      "checked_lengths":14,"rows":rows},indent=2))

if __name__ == "__main__":
    main()
