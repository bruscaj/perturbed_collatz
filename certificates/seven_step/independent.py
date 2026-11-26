"""Independent transformed-coordinate reconstruction of the direct frontier.

The primary checker works in physical coordinates.  This file uses T/U maps,
checks their conjugacy to the signed physical recurrence symbolically, and
reconstructs all short first returns without importing the primary checker.
Every arithmetic record represents all integers q >= its stated minimum.
"""
def require(condition, message):
    if not condition:
        raise ValueError(message)


D = (0, 0, 1, -1, 0, 1, -1)
H = (0, 0, 0, 1, 0, 0, 1)
S = (3, 5, 6)
W = {3: 1, 5: 1, 6: 2}
CAPS = {3: 3, 5: 8, 6: 7}
FAMILIES = [
    ("S00", 3, 4, 3, 9, 7, 5, 2, 0),
    ("S01", 5, 2, 0, 3, 0, 6, 1, 1),
    ("S02", 5, 32, 3, 81, 9, 3, 5, 0),
    ("S03", 5, 128, 115, 243, 220, 5, 7, 0),
    ("S06", 6, 16, 7, 81, 36, 3, 4, 0),
    ("S08", 6, 64, 15, 243, 58, 5, 6, 0),
]


def positive_step(a, b, phase):
    require(a % 2 == 0, "Parity varies on the proposed infinite domain")
    if H[phase] == 1:
        factor, offset = (3, 1) if b % 2 else (1, 0)
    else:
        factor, offset = (1, 1) if b % 2 else (3, 0)
    require((factor * b + offset) % 2 == 0, "Nonintegral update")
    return factor * a // 2, (factor * b + offset) // 2, (phase + 1) % 7


def first_return(a, b, phase, cap, minimum):
    for tick in range(1, cap + 1):
        a, b, phase = positive_step(a, b, phase)
        require(a > 0 and a * minimum + b >= 1, "Unsafe symbolic state")
        if phase in S:
            require(a % 3 == 0, "Section guard varies with the parameter")
            if b % 3 == 0:
                return a // 3, b // 3, phase, tick
    return None


def check():
    # z = 2q+r, n=z-1+h.  Compare the two affine expressions, not samples.
    for phase in range(7):
        require(D[phase] == H[(phase + 1) % 7] - H[phase], "Height mismatch")
        for parity in (0, 1):
            n_a, n_b = 2, parity - 1 + H[phase]
            multiplier = 3 if n_b % 2 else 1
            add = 1 if n_b % 2 else 0
            actual = (multiplier * n_a // 2,
                      (multiplier * n_b + add) // 2 + D[phase]
                      + 1 - H[(phase + 1) % 7], (phase + 1) % 7)
            require(actual == positive_step(2, parity, phase), "Conjugacy failed")

    classified = {name: 0 for name, *_ in FAMILIES}
    singleton = set()
    long_domains = 0
    records = 0
    for phase, cap in CAPS.items():
        modulus = 2 ** cap
        for residue in range(modulus):
            minimum = int(residue == 0)
            records += 1
            out = first_return(3 * modulus, 3 * residue, phase, cap, minimum)
            matched = [row for row in FAMILIES
                       if row[1] == phase and residue % row[2] == row[3]]
            require(len(matched) <= 1, "Overlapping listed families")
            if out is None:
                require(not matched and phase in (5, 6), "Unexpected long branch")
                long_domains += 1
                continue
            oa, ob, op, ticks = out
            gap_a, gap_b = W[phase] * modulus - W[op] * oa, W[phase] * residue - W[op] * ob
            if gap_a < 0:
                require(len(matched) == 1, "Unlisted growing tail")
                row = matched[0]
                name, _, mod, rem, am, bm, dest, time, tmin = row
                scale, shift = modulus // mod, (residue - rem) // mod
                require(scale * minimum + shift >= tmin, "Family domain mismatch")
                require(out == (am * scale, am * shift + bm, dest, time), "Endpoint mismatch")
                require(gap_a * minimum + gap_b < 0, "Growing family has an omitted exception")
                classified[name] += 1
            else:
                require(gap_a > 0 and not matched, "Unexpected zero slope or family label")
                if gap_a * minimum + gap_b <= 0:
                    require(minimum == 0 and gap_a + gap_b > 0, "Unaccounted finite exceptions")
                    singleton.add((phase, residue))
    require(records == 392 and long_domains == 9, "Incomplete domain count")
    require(singleton == {(3, 1), (3, 2), (5, 1)}, "Wrong finite basis")
    require(classified == {"S00": 2, "S01": 128, "S02": 8,
                           "S03": 2, "S06": 8, "S08": 2}, "Wrong growing partition")

    # Reconstruct all entrance domains independently; these are infinite rays.
    avoid = []
    exits = 0
    for residue in range(384):
        minimum = int(residue == 0)
        a, b, phase = 384, residue, 0
        for tick in range(1, 8):
            a, b, phase = positive_step(a, b, phase)
            require(a * minimum + b >= 1, "Unsafe entrance domain")
            if phase in S and b % 3 == 0:
                require(a % 3 == 0, "Variable section guard")
                require(27 * 384 >= 8 * W[phase] * a, "Exit slope bound")
                require(27 * (384 * minimum + residue)
                        >= 8 * W[phase] * (a * minimum + b), "Exit intercept bound")
                exits += 1
                break
        else:
            require(phase == 0 and a < 384 and 1 <= b < residue, "Avoiding descent")
            require(128 * a <= 27 * 384 and 128 * b <= 27 * residue + 220, "Avoiding envelope")
            avoid.append([residue, a, b])
    require(len(avoid) == 14 and exits == 370, "Entrance coverage mismatch")
    return {"status": "passed", "conjugacy_parity_cases": 14,
            "infinite_section_domains": records, "long_domains": long_domains,
            "direct_growing_families": classified, "phase_zero_domains": 384,
            "avoiding_affine_rows": avoid, "finite_exceptions": sorted(singleton)}


if __name__ == "__main__":
    import json
    print(json.dumps(check(), indent=2))
