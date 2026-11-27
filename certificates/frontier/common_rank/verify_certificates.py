#!/usr/bin/env python3
"""Independent whole-affine verification using signed physical n dynamics.

No imports from the builder or older certificate packages. Explicit checks
remain active under Python -O. Every replay uses integer coefficients over
an unbounded nonnegative parameter, never interpolation from sample seeds.
"""

from __future__ import annotations

import argparse
from collections import Counter
from fractions import Fraction
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parent
H = (0, 0, 0, 1, 0, 0, 1)
D = (0, 0, 1, -1, 0, 1, -1)
CYCLE_N = (0, 0, 0, 1, 1, 2, 2)


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def affine_step(a: int, b: int, p: int) -> tuple[int, int, int, str]:
    require(a >= 0 and a % 2 == 0 and b >= H[p], "unsafe or variable-parity affine domain")
    odd = b % 2
    if odd:
        a, b = 3 * a // 2, (3 * b + 1) // 2 + D[p]
    else:
        a, b = a // 2, b // 2 + D[p]
    p = (p + 1) % 7
    require(b >= H[p], "affine path leaves positive-z domain")
    return a, b, p, "G" if odd else "S"


def point_step(n: int, p: int) -> tuple[int, int]:
    require(n >= H[p], "unsafe point")
    out = (n // 2 if n % 2 == 0 else (3 * n + 1) // 2) + D[p]
    j = (p + 1) % 7
    require(out >= H[j], "point leaves domain")
    return out, j


def verify(path: Path) -> dict:
    c = json.loads(path.read_text())
    name = path.stem
    expected = {
        "three_family": ({1: (4, 0), 2: (7, 0), 3: (4, 0), 5: (5, 0)}, 43, 3,
                         {(1, 1), (1, 3), (5, 3), (1, 5), (3, 5)}),
        "common_Q_first_return": ({1: (4, 0), 2: (8, 0), 3: (6, 0), 5: (6, 0), 6: (12, 3)},
                                  32, 5, {(3, 2), (1, 3), (2, 3), (1, 5)}),
        "common_Q_cover": ({1: (4, 0), 2: (8, 0), 3: (6, 0), 5: (6, 0), 6: (12, 3)},
                           88, 5, {(1, 1), (3, 2), (1, 3), (2, 3), (1, 5)}),
    }
    require(name in expected, "unknown certificate convention")
    rank, row_count, growing_count, finite_expected = expected[name]
    require(c["status"] == "PASS" and c["word"] == "UUUTUUT"
            and c["all_seed_capture_proved"] is False, "scope or status changed")
    require({int(p): (r["weight"], r["offset"]) for p, r in c["rank"].items()} == rank,
            "wrong rank")
    require(c["section_phases"] == list(rank), "wrong section")
    marks = {p: (tuple((1, 2, 5)) if name == "common_Q_cover" and p in (1, 2, 5)
                 else tuple(rank)) for p in rank}
    require({int(p): tuple(v) for p, v in c["target_marks"].items()} == marks, "wrong return convention")
    rows = c["complete_rows"]
    require(len(rows) == row_count, "row count changed")
    require({int(p): count for p, count in c["rows_by_phase"].items()}
            == dict(Counter(r["input_phase"] for r in rows)), "row-count metadata differs")
    index = {(r["input_phase"], r["M"], r["r"]): r for r in rows}
    require(len(index) == len(rows), "duplicate rows")
    growing, finite = [], set()
    for row in rows:
        i, j, M, r, A, b, length, lo = (row[k] for k in
            ("input_phase", "output_phase", "M", "r", "A", "b", "steps", "t_min"))
        require(i in rank and j in marks[i] and M == 2 ** length and 0 <= r < M,
                "invalid return domain")
        require(lo == int(r == 0), "positive-domain boundary changed")
        a, physical_b, p, trace = 3 * M, 3 * (M * lo + r) - 1 + H[i], i, ""
        for tick in range(1, length + 1):
            a, physical_b, p, letter = affine_step(a, physical_b, p)
            trace += letter
            z_b = physical_b + 1 - H[p]
            require(a % 3 == 0, "mark divisibility varies within a domain")
            hit = p in marks[i] and z_b % 3 == 0
            require(hit == (tick == length), "not the stated first return")
        require((a // 3, (physical_b + 1 - H[p]) // 3, p) == (A, A * lo + b, j),
                "wrong whole-affine endpoint")
        require(trace == row["trace"], "wrong parity trace")
        slope = rank[j][0] * A - rank[i][0] * M
        intercept = rank[j][0] * b + rank[j][1] - rank[i][0] * r - rank[i][1]
        require((slope, intercept) == (row["rank_gain_slope"], row["rank_gain_offset"]),
                "rank gain differs")
        require(slope != 0, "unclassified zero-slope row")
        if slope > 0:
            require(slope * lo + intercept > 0 and row["kind"] == "growing" and row["finite_t_max"] is None,
                    "growing domain not uniformly growing")
            growing.append(row)
        else:
            hi = intercept // (-slope)
            if hi >= lo:
                require(row["kind"] == "finite_exception" and row["finite_t_max"] == hi,
                        "finite exceptions omitted")
                finite.update((M * t + r, i) for t in range(lo, hi + 1))
            else:
                require(row["kind"] == "decreasing" and row["finite_t_max"] is None,
                        "wrong decreasing classification")
    require(growing == c["growing_rows"] and len(growing) == growing_count, "residual list differs")
    expected_residuals = {
        "three_family": {(1, 2, 0), (3, 4, 3), (5, 8, 2)},
        "common_Q_first_return": {(1, 2, 0), (1, 4, 1), (2, 2, 0), (3, 4, 3), (5, 2, 0)},
        "common_Q_cover": {(1, 2, 0), (1, 16, 9), (2, 8, 2), (3, 4, 3), (5, 8, 2)},
    }
    require({(r["input_phase"], r["M"], r["r"]) for r in growing}
            == expected_residuals[name], "unexpected residual domains")
    require(finite == finite_expected, "finite boundary set differs")
    caps = {int(p): cap for p, cap in c["first_return_caps"].items()}
    require(set(caps) == set(rank), "cap phases incomplete")
    fixed_classes, seen_caps = 0, {}
    for launch, cap in caps.items():
        modulus = 2 ** cap
        max_tick = 0
        multiplicity = Counter()
        for base in range(1, modulus + 1):
            matches = [r for r in rows if r["input_phase"] == launch and base % r["M"] == r["r"]]
            require(len(matches) == 1, "input partition has overlap or a hole")
            row = matches[0]
            a, b, p = 3 * modulus, 3 * base - 1 + H[launch], launch
            for tick in range(1, cap + 1):
                a, b, p, _ = affine_step(a, b, p)
                z_b = b + 1 - H[p]
                require(a % 3 == 0, "variable mark test in fixed-modulus audit")
                if p in marks[launch] and z_b % 3 == 0:
                    require((p, tick) == (row["output_phase"], row["steps"]), "different first return")
                    t0 = (base - row["r"]) // row["M"]
                    require(a // 3 == row["A"] * (modulus // row["M"])
                            and z_b // 3 == row["A"] * t0 + row["b"], "fixed-modulus affine mismatch")
                    max_tick = max(max_tick, tick)
                    multiplicity[(row["M"], row["r"])] += 1
                    break
            else:
                raise ValueError("unresolved fixed-modulus class")
            fixed_classes += 1
        for row in rows:
            if row["input_phase"] == launch:
                require(multiplicity[(row["M"], row["r"])] == modulus // row["M"],
                        "dyadic leaf multiplicity differs")
        seen_caps[launch] = max_tick
    require(seen_caps == caps, "return cap not attained")
    entries = c["phase_zero_entry_classes"]
    require(len(entries) == 96 and [x["residue"] for x in entries] == list(range(1, 97)),
            "entry partition incomplete")
    max_entry = 0
    for item in entries:
        require(item["modulus"] == 96, "entry modulus changed")
        a, b, p = 96, item["residue"] - 1, 0
        for tick in range(1, 6):
            a, b, p, _ = affine_step(a, b, p)
            z_b = b + 1 - H[p]
            require(a % 3 == 0, "entry mark test depends on parameter")
            if p in rank and z_b % 3 == 0:
                require((tick, p, a, z_b) == (item["steps"], item["output_phase"],
                                             item["z_slope"], item["z_offset"]), "entry endpoint changed")
                max_entry = max(max_entry, tick)
                break
        else:
            raise ValueError("entry class unresolved")
    require(max_entry == c["phase_zero_entry_bound"] == 5
            and c["global_section_entry_bound"] == 11, "entry bound differs")
    paths = c["finite_exception_capture_paths"]
    require({(x["m"], x["phase"]) for x in paths} == finite and len(paths) == len(finite),
            "finite capture coverage differs")
    finite_lengths = []
    for item in paths:
        n, p = 3 * item["m"] - 1 + H[item["phase"]], item["phase"]
        physical_path = [[n + 1 - H[p], p]]
        for _ in range(200):
            if n == CYCLE_N[p]:
                break
            n, p = point_step(n, p)
            physical_path.append([n + 1 - H[p], p])
        else:
            raise ValueError("finite point not captured")
        require(physical_path == item["path"], "finite path differs")
        finite_lengths.append(dict(m=item["m"], phase=item["phase"], steps=len(physical_path) - 1))
    for phase in range(7):
        require(point_step(CYCLE_N[phase], phase) == (CYCLE_N[(phase + 1) % 7], (phase + 1) % 7),
                "known cycle not invariant")
    lower_bound = None
    if name == "three_family":
        require(c["prior_result"] == dict(
            commit="d66684dae29459f15ca2043aabf6cc0d5dbd8db5",
            path="research/attack_sprint_2026_11_25_continuation/root_three_family.md",
            claim="Prior off-main three-family theorem; independently reconstructed here."),
            "prior-result provenance changed")
        used = set()
        witnesses = c["phase_affine_lower_bound_cycles"]
        require(len(witnesses) == 3, "missing lower-bound cycles")
        for witness in witnesses:
            keys = [tuple(k) for k in witness["domains"]]
            require(len(keys) == len(set(keys)) == 3 and not (set(keys) & used), "reused lower-bound domain")
            selected = [index[k] for k in keys]
            gain = Fraction(1)
            for i, row in enumerate(selected):
                require(row["output_phase"] == selected[(i + 1) % len(selected)]["input_phase"],
                        "not a closed phase cycle")
                gain *= Fraction(row["A"], row["M"])
            require(gain == Fraction(243, 128) and str(gain) == witness["slope_product"],
                    "lower-bound gain differs")
            used.update(keys)
        lower_bound = 3
    return dict(status="PASS", certificate=name,
                certificate_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                whole_affine_rows_replayed=len(rows), fixed_modulus_classes_replayed=fixed_classes,
                complete_phase_zero_entry_classes=96, phase_zero_entry_bound=max_entry,
                all_phase_entry_bound=11, first_return_caps=caps, growing_domains=len(growing),
                finite_capture_paths=finite_lengths, fixed_section_phase_affine_lower_bound=lower_bound,
                no_sample_interpolation=True, signed_physical_dynamics=True,
                all_seed_capture_proved=False)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--directory", type=Path, default=ROOT)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    reports = [verify(args.directory / (name + ".json")) for name in
               ("three_family", "common_Q_first_return", "common_Q_cover")]
    result = dict(status="PASS", reports=reports)
    if args.output:
        args.output.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
