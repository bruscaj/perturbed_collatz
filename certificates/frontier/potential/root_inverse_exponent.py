"""Independently verify all integer inequalities in an inverse-growth potential."""

import argparse
from fractions import Fraction
import json
import mmap
from pathlib import Path
import struct
from sys import byteorder

from root_quotient_probe import CENTER, D, P, SHRINK_OFFSET


if not __debug__:
    raise SystemExit("Inverse-growth certificates require assertions. Run without -O.")


A_GROW = Fraction(667, 1000)


def verify_values(d, quantum, lo, hi, values, exponent, pruned, obstruction, ideal):
    if type(d) is not int or not 1 <= d <= len(values).bit_length():
        raise ValueError("precision must be positive and fit the supplied vector")
    if type(quantum) is not int or quantum <= 0:
        raise ValueError("certificate scale must be a positive integer")
    if any(type(weight) is not int or weight < 0 for weight in (lo, hi)):
        raise ValueError("branch weights must be nonnegative integers")
    if exponent < 0:
        raise ValueError("expected a nonnegative inverse-growth exponent")
    a_shrink = Fraction(2) if ideal else Fraction(2001, 1000) if pruned else Fraction(107, 50)
    a_grow = Fraction(2, 3) if ideal else A_GROW
    assert not ideal or obstruction
    comparisons = (Fraction(weight, quantum) ** exponent.denominator * factor ** exponent.numerator
                   for weight, factor in ((lo, a_shrink), (hi, a_grow)))
    if obstruction:
        assert all(c > 1 for c in comparisons)
    else:
        assert all(c < 1 for c in comparisons)
        if not pruned:
            assert (2 + Fraction(-min(SHRINK_OFFSET), D + min(CENTER))) * Fraction(2501, 2500) < a_shrink
        # Every inverse in the uncentered positive coordinate has a nonpositive intercept.
        inflation = Fraction(5001, 5000) if pruned else Fraction(2501, 2500)
        assert inflation * 2 < a_shrink
        assert inflation * Fraction(2, 3) < a_grow
    modulo = 3 ** d
    step = modulo // 3
    assert len(values) == P * modulo and all(type(v) is int and v > 0 for v in values)
    least = None
    greatest = None
    for p in range(P):
        q = (p - 1) % P
        prev = q * modulo
        for w in range(modulo):
            shrink = values[prev + (2 * w - SHRINK_OFFSET[q]) % modulo]
            weighted = lo * shrink
            if w % 3 == 0:
                base = prev + (2 * (w // 3)) % step
                weighted += hi * min(values[base], values[base + step], values[base + 2 * step])
            margin = weighted - quantum * values[p * modulo + w]
            least = margin if least is None else min(least, margin)
            greatest = margin if greatest is None else max(greatest, margin)
    if obstruction:
        assert greatest < 0
    else:
        assert least >= 0
    return len(values), greatest if obstruction else least


def verify(path, exponent, pruned=False, obstruction=False, ideal=False):
    if path.suffix == '.bin':
        with path.open('rb') as raw, mmap.mmap(raw.fileno(), 0, access=mmap.ACCESS_READ) as data:
            header = struct.unpack_from('<4Q', data)
            if byteorder != 'little':
                raise ValueError('binary checker requires a little-endian host')
            with memoryview(data)[32:].cast('Q') as values:
                return verify_values(*header, values, exponent, pruned, obstruction, ideal)
    certificate = json.loads(path.read_text())
    return verify_values(certificate['precision'], certificate['scale'], certificate['shrink_weight'],
                         certificate['grow_weight'], certificate['values'], exponent, pruned, obstruction, ideal)


def verify_branching():
    maximum = 0
    for start_phase in range(P):
        for start_residue in range(3):
            p, r = start_phase, start_residue
            distance = 0
            while r != 0 and distance <= 6:
                p = (p - 1) % P
                r = (2 * r - SHRINK_OFFSET[p]) % 3
                distance += 1
            assert r == 0
            maximum = max(maximum, distance)
    assert maximum == 5
    return maximum + 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--file", type=Path, default=Path(__file__).with_suffix(".json"))
    parser.add_argument("--exponent", type=Fraction, default=Fraction(3, 5))
    parser.add_argument("--pruned", action="store_true")
    parser.add_argument("--obstruction", action="store_true")
    parser.add_argument("--ideal", action="store_true", help="use limiting factors 2 and 2/3 for an obstruction")
    args = parser.parse_args()
    count, margin = verify(args.file, args.exponent, args.pruned, args.obstruction, args.ideal)
    branch_depth = verify_branching()
    print("Exponent", args.exponent, "integer constraints", count,
          "maximum negative margin" if args.obstruction else "minimum margin", margin)
    print("Uniform distinct-predecessor branch depth:", branch_depth)


if __name__ == "__main__":
    main()
