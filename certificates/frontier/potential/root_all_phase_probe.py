"""Bounded search for smaller future-equivalent transformed states.

A meeting witness may use two different forward durations. The search ranges
across all seven phases and compares transformed heights at the two starts.
"""

import argparse
from collections import Counter
import random


WORD = "UUUTUUT"
PHYSICAL_IMPULSES = (0, 0, 1, -1, 0, 1, -1)
HEIGHTS = (0, 0, 0, 1, 0, 0, 1)


def step(z, phase):
    if WORD[phase] == "T":
        return (3 * z + 1) // 2 if z % 2 else z // 2
    return (z + 1) // 2 if z % 2 else 3 * z // 2


def predecessors(z, phase):
    previous_phase = (phase - 1) % len(WORD)
    if WORD[previous_phase] == "T":
        yield 2 * z
        if z % 3 == 2:
            yield (2 * z - 1) // 3
    else:
        yield 2 * z - 1
        if z % 3 == 0:
            yield 2 * z // 3


def verify_witness(origin, origin_phase, witness):
    meeting, meeting_phase, forward_depth, other, other_phase, inverse_depth = witness
    assert 0 < other < origin
    for z, phase, depth in ((origin, origin_phase, forward_depth),
                            (other, other_phase, inverse_depth)):
        n = z - 1 + HEIGHTS[phase]
        for _ in range(depth):
            n = ((3 * n + 1) // 2 if n % 2 else n // 2) + PHYSICAL_IMPULSES[phase]
            phase = (phase + 1) % len(WORD)
        assert (n + 1 - HEIGHTS[phase], phase) == (meeting, meeting_phase)


def earlier_meeting(origin, phase, forward_limit, reverse_limit):
    stack = []
    for depth in range(forward_limit + 1):
        if depth == 0:
            z, meeting_phase, previous = origin, phase, None
        else:
            previous = z
            z = step(z, meeting_phase)
            meeting_phase = (meeting_phase + 1) % len(WORD)
        if z < origin:
            return z, meeting_phase, depth, z, meeting_phase, 0
        if reverse_limit == 0:
            continue
        next_phase = (meeting_phase - 1) % len(WORD)
        stack.extend((parent, next_phase, 1) for parent in predecessors(z, meeting_phase)
                     if parent != previous)
        while stack:
            parent, parent_phase, inverse_depth = stack.pop()
            if parent < origin:
                return z, meeting_phase, depth, parent, parent_phase, inverse_depth
            if inverse_depth == reverse_limit:
                continue
            # Every inverse operation leaves parent + 1 at least 2/3 as large.
            remaining = reverse_limit - inverse_depth
            if (parent + 1) * 2 ** remaining >= (origin + 1) * 3 ** remaining:
                continue
            next_phase = (parent_phase - 1) % len(WORD)
            stack.extend((ancestor, next_phase, inverse_depth + 1)
                         for ancestor in predecessors(parent, parent_phase))
    return None


def brute_has_witness(origin, phase, forward_limit, reverse_limit):
    z = origin
    for _ in range(forward_limit + 1):
        states = {z}
        test_phase = phase
        for _ in range(reverse_limit + 1):
            if min(states) < origin:
                return True
            states = {parent for value in states for parent in predecessors(value, test_phase)}
            test_phase = (test_phase - 1) % len(WORD)
        z = step(z, phase)
        phase = (phase + 1) % len(WORD)
    return False


def lift_boundary(forward_limit, reverse_limit):
    modulus = 2 ** forward_limit * 3 ** reverse_limit
    # Every tested endpoint has slope denominator dividing modulus, and the
    # absolute offset is smaller than 2^(forward_limit + reverse_limit + 2).
    return modulus, modulus * 2 ** (forward_limit + reverse_limit + 2)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=10000)
    parser.add_argument("--forward", type=int, default=10)
    parser.add_argument("--reverse", type=int, default=18)
    parser.add_argument("--seed", type=int, default=20261125)
    parser.add_argument("--lift", action="store_true", help="sample above the exact affine cutoff")
    args = parser.parse_args()
    for z in range(1, 256):
        for phase in range(len(WORD)):
            previous = (phase - 1) % len(WORD)
            assert set(predecessors(z, phase)) == {
                other for other in range(1, 2 * z + 1) if step(other, previous) == z
            }
            if z < 100:
                assert bool(earlier_meeting(z, phase, 5, 8)) == brute_has_witness(z, phase, 5, 8)
    modulus, boundary = lift_boundary(args.forward, args.reverse)
    randomizer = random.Random(args.seed)
    misses = Counter()
    methods = Counter()
    first_miss = None
    for _ in range(args.samples):
        z = randomizer.randrange(10**24, 10**25)
        if args.lift:
            z = boundary + 1 + randomizer.randrange(modulus)
        phase = randomizer.randrange(len(WORD))
        witness = earlier_meeting(z, phase, args.forward, args.reverse)
        if witness is None:
            misses[phase] += 1
            if first_miss is None:
                first_miss = z, phase
        else:
            verify_witness(z, phase, witness)
            methods[witness[2] == 0, witness[-1] == 0] += 1
    print(f"seed={args.seed}, samples={args.samples}, forward={args.forward}, reverse={args.reverse}")
    print("Misses per phase:", dict(sorted(misses.items())))
    print("Witness counts (inverse only, forward only):", dict(sorted(methods.items())))
    print("First missed state:", first_miss)
    if args.lift and first_miss:
        print("The whole progression from that state with modulus", modulus, "misses both windows.")


if __name__ == "__main__":
    main()
