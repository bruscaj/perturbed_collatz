"""Exact quotient of UUUTUUT by future-equivalence along expanding edges."""

import argparse
from collections import Counter
from dataclasses import dataclass
from fractions import Fraction
import random

from root_all_phase_probe import WORD, predecessors, step


D = 2059
CENTER = (280, 420, 630, 945, 388, 582, 873)
SHRINK_OFFSET = tuple(2 * c + D * (1 - 2 * (letter == "T"))
                      for c, letter in zip(CENTER, WORD))
P = len(WORD)


def valuation(n, prime):
    assert n > 0
    if prime == 2:
        return (n & -n).bit_length() - 1
    order = 0
    while n % prime == 0:
        n //= prime
        order += 1
    return order


def decode(w, phase):
    z, rem = divmod(w - CENTER[phase], D)
    assert z > 0 and rem == 0
    return z


@dataclass(frozen=True)
class Component:
    phase: int
    core: int
    exposure: int

    @property
    def entry_centered(self):
        return self.core * 2 ** self.exposure

    @property
    def end_centered(self):
        return self.core * 3 ** self.exposure

    @property
    def end_phase(self):
        return (self.phase + self.exposure) % P

    @property
    def entry_z(self):
        return decode(self.entry_centered, self.phase)

    def forward(self):
        next_phase = (self.end_phase + 1) % P
        next_centered = (self.end_centered + SHRINK_OFFSET[self.end_phase]) // 2
        return from_centered(next_centered, next_phase)

    def reverse(self):
        # Each position of the expanding chain has exactly one predecessor
        # whose own forward update is shrinking. Each belongs to a component
        # ending at that predecessor.
        w = self.entry_centered
        for j in range(self.exposure + 1):
            previous_phase = (self.phase + j - 1) % P
            yield from_centered(2 * w - SHRINK_OFFSET[previous_phase], previous_phase)
            if j < self.exposure:
                w = 3 * w // 2


def from_centered(w, phase):
    twos, threes = valuation(w, 2), valuation(w, 3)
    return Component((phase - threes) % P, w // (2 ** twos * 3 ** threes), twos + threes)


def component(z, phase):
    return from_centered(D * z + CENTER[phase], phase)


def literal_forward(c):
    z, phase = c.entry_z, c.phase
    while True:
        z_next = step(z, phase)
        phase_next = (phase + 1) % P
        if (z % 2 == 1) != (WORD[phase] == "T"):
            return component(z_next, phase_next)
        z, phase = z_next, phase_next


def literal_reverse(c):
    found = set()
    z, phase = c.entry_z, c.phase
    for index in range(c.exposure + 1):
        p = (phase - 1) % P
        parent, *_ = predecessors(z, phase)
        assert step(parent, p) == z
        found.add(component(parent, p))
        if index < c.exposure:
            assert (z % 2 == 1) == (WORD[phase] == "T")
            z = step(z, phase)
            phase = (phase + 1) % P
    return found


def validate():
    for phase in range(P):
        for z in range(1, 4000):
            w = D * z + CENTER[phase]
            step_phase = (phase + 1) % P
            w_next = D * step(z, phase) + CENTER[step_phase]
            assert 2 * w_next == (3 * w if w % 2 == 0 else w + SHRINK_OFFSET[phase])
            c = component(z, phase)
            assert c.exposure >= 0 and c.core % 2 and c.core % 3
            assert c.entry_z >= 1
            assert 0 <= c.phase < P
            assert c.forward() == literal_forward(c)
            other = set(c.reverse())
            assert other == literal_reverse(c)
            assert all(o.forward() == c for o in other)


def bounded_profile(samples, digits, seed):
    rng = random.Random(seed)
    ranks = {
        "core, length": lambda c: (c.core, c.exposure),
        "centered entry": lambda c: c.entry_centered,
        "entry z": lambda c: c.entry_z,
    }
    misses = Counter()
    lengths = Counter()
    for _ in range(samples):
        phase = rng.randrange(P)
        z = rng.randrange(10 ** (digits - 1), 10 ** digits)
        origin = component(z, phase)
        lengths[origin.exposure] += 1
        outgoing = origin.forward()
        incoming = tuple(origin.reverse())
        common_next = tuple(outgoing.reverse())
        witness_sets = (incoming, (outgoing,), common_next, incoming + (outgoing,) + common_next)
        for rankname, rank in ranks.items():
            threshold = rank(origin)
            for label, options in zip(("inverse", "forward", "coalescence", "union"), witness_sets):
                misses[(rankname, label)] += not any(rank(c) < threshold for c in options)
    print(f"Samples {samples}, digits {digits}, seed {seed}")
    print("First five quotient chain exposures:", sorted(lengths.items())[:5], "maximum", max(lengths))
    for name in ranks:
        print(name, {label: misses[name, label] for label in ("inverse", "forward", "coalescence", "union")})


def validate_hard_family():
    e0, period = 209, 420
    core = 59
    assert period % 7 == 0 and pow(2, period, D) == 1
    assert core * pow(2, e0, D) % D == CENTER[1]
    assert period % 6 == 0 and core * pow(2, e0, 9) % 9 == 7
    assert pow(3, period, 8) == 1 and (core * pow(3, e0, 8) + SHRINK_OFFSET[0]) % 8 == 4
    assert valuation(SHRINK_OFFSET[0], 3) == 3
    assert tuple(valuation(abs(q), 3) for q in SHRINK_OFFSET) == (3, 0, 0, 0, 4, 0, 0)
    assert (core * pow(2, e0 - 3, 9) - SHRINK_OFFSET[4] // 81) % 9 in (3, 6)
    constants = {}
    for d in (-3, -2, -1, 1):
        constant = Fraction(3, 2) ** d * SHRINK_OFFSET[0] - SHRINK_OFFSET[d % 7]
        assert constant.numerator % 3 and constant.denominator % 3
        constants[d] = str(constant)
    for e in (e0, e0 + period, e0 + 13 * period):
        c = Component(1, core, e)
        marked_z = decode(9 * c.entry_centered // 4, 3)
        assert marked_z % 3 == 0 and marked_z // 3 % 108 == 3
        outgoing = c.forward()
        assert outgoing.exposure == 4
        alternatives = set(c.reverse()) | {outgoing} | set(outgoing.reverse()) - {c}
        for other in alternatives:
            assert other.core > c.core and other.entry_centered > c.entry_centered
    print("Checked long hard-family blueprint: entry phase 1, core 59, exposure 209+420k.")
    print("Nonidentity successor-sibling constants (position offset, additive constant):", constants)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--samples", type=int, default=100000)
    parser.add_argument("--digits", type=int, default=24)
    parser.add_argument("--seed", type=int, default=20261125)
    args = parser.parse_args()
    validate()
    validate_hard_family()
    bounded_profile(args.samples, args.digits, args.seed)
    start = component(1, 0)
    state = start
    trace = []
    while state not in trace:
        trace.append(state)
        state = state.forward()
    print("Known cycle in components:", [(c.entry_z, c.phase, c.exposure) for c in trace], "repeat index", trace.index(state))


if __name__ == "__main__":
    main()
