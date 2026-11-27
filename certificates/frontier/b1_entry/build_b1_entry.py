#!/usr/bin/env python3
"""Construct a finite inverse-entry cover of every safe state into B1.

This is a witness search, not an optimality or termination claim about search.
The independent consumer replays every witness in the signed physical map.
"""
from __future__ import annotations

import argparse
from collections import Counter, deque
import json
from pathlib import Path

HEIGHTS = (0, 0, 0, 1, 0, 0, 1)
MODULUS = 27
PRECISION = 3


def witness(phase: int, residue: int) -> dict:
    queue = deque([(MODULUS, residue, phase, 0, "", [(MODULUS, residue, phase)])])
    seen = set()
    while queue:
        a, b, p, grows, word, trace = queue.popleft()
        if p == 1 and a % 6 == 0 and b % 6 == 0 and b >= 6:
            # Each trace triple is (coefficient, intercept, phase).
            physical = [
                {"phase": j, "n": [c, e - 1 + HEIGHTS[j]]}
                for c, e, j in reversed(trace)
            ]
            return {
                "target_phase": phase,
                "target_residue": residue,
                "target_z": [MODULUS, residue],
                "source_phase": 1,
                "source_t": [a // 6, b // 6],
                "source_z": [a, b],
                "steps": len(word),
                "inverse_word": word,
                "forward_physical_trace": physical,
            }
        key = (p, grows, b % (2 * 3 ** (PRECISION - grows)), bool(word))
        if key in seen:
            continue
        seen.add(key)
        previous = (p - 1) % 7
        # The shrinking physical predecessor exists at every positive z.
        child = (2 * a, 2 * b - 1 + HEIGHTS[previous], previous)
        queue.append((*child, grows, word + "S", trace + [child]))
        # Keep at least one ternary digit to make 3 | source_z uniform.
        if grows < PRECISION - 1 and (2 * b - HEIGHTS[previous]) % 3 == 0:
            child = (2 * a // 3, (2 * b - HEIGHTS[previous]) // 3, previous)
            queue.append((*child, grows + 1, word + "G", trace + [child]))
    raise RuntimeError(f"No witness for phase={phase}, residue={residue}")


def build() -> dict:
    rows = [witness(p, r) for p in range(7) for r in range(1, MODULUS + 1)]
    return {
        "schema": "seven-step-b1-inverse-entry-v1",
        "model": {
            "physical_impulses": [0, 0, 1, -1, 0, 1, -1],
            "safe_heights": list(HEIGHTS),
            "coordinate": "z = n + 1 - h[phase]",
            "zero_convention": "safe zero continues evolving",
        },
        "claim": "For every phase p and z >= 1, a positive B1 launch (6t-1,1), t>=1, reaches (z-1+h[p],p).",
        "parameter_domain": "v is an integer with v >= 0",
        "target_modulus": MODULUS,
        "target_residues": list(range(1, MODULUS + 1)),
        "target_phases": list(range(7)),
        "clock_maximum": max(row["steps"] for row in rows),
        "row_count": len(rows),
        "rows": rows,
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=Path(__file__).with_name("b1_entry_certificate.json"))
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    result = build()
    payload = json.dumps(result, indent=2, sort_keys=True) + "\n"
    if args.check:
        if args.output.read_text() != payload:
            raise SystemExit("Stored certificate differs from exact witness regeneration")
    else:
        args.output.write_text(payload)
    print(json.dumps({
        "status": "PASS",
        "rows": result["row_count"],
        "max_steps": result["clock_maximum"],
        "inverse_grows": dict(Counter(row["inverse_word"].count("G") for row in result["rows"])),
        "mode": "check" if args.check else "write",
    }, sort_keys=True))


if __name__ == "__main__":
    main()
