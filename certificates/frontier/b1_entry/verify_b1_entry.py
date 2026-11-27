#!/usr/bin/env python3
"""Independently verify whole-ray B1 entry in the signed physical recurrence.

No generator or normalized inverse implementation is imported. The consumer
starts from physical n=6t-1 at phase one, and uses only odd/even physical
updates followed by the specified impulse. Checks survive Python -O.
"""
from __future__ import annotations

import argparse
from collections import Counter
from copy import deepcopy
import hashlib
import json
from pathlib import Path

IMPULSES = (0, 0, 1, -1, 0, 1, -1)
HEIGHTS = (0, 0, 0, 1, 0, 0, 1)
CLAIM = "For every phase p and z >= 1, a positive B1 launch (6t-1,1), t>=1, reaches (z-1+h[p],p)."


class InvalidCertificate(ValueError):
    pass


def need(condition: bool, message: str) -> None:
    if not condition:
        raise InvalidCertificate(message)


def integer(value: object, name: str, minimum: int | None = None) -> int:
    need(type(value) is int, f"{name} must be an exact integer")
    if minimum is not None:
        need(value >= minimum, f"{name} is below its minimum")
    return value


def pair(value: object, name: str) -> tuple[int, int]:
    need(type(value) is list and len(value) == 2, f"{name} must have two integers")
    return integer(value[0], name + " coefficient"), integer(value[1], name + " intercept")


def check(data: object) -> dict:
    need(type(data) is dict, "certificate must be an object")
    need(set(data) == {
        "schema", "model", "claim", "parameter_domain", "target_modulus",
        "target_residues", "target_phases", "clock_maximum", "row_count", "rows",
    }, "unexpected certificate fields")
    need(data["schema"] == "seven-step-b1-inverse-entry-v1", "wrong schema")
    expected_model = {
        "physical_impulses": list(IMPULSES),
        "safe_heights": list(HEIGHTS),
        "coordinate": "z = n + 1 - h[phase]",
        "zero_convention": "safe zero continues evolving",
    }
    need(json.dumps(data["model"], sort_keys=True) == json.dumps(expected_model, sort_keys=True),
         "model metadata must match the signed physical recurrence")
    need(data["claim"] == CLAIM, "claim metadata mismatch")
    need(data["parameter_domain"] == "v is an integer with v >= 0", "parameter domain mismatch")
    need(integer(data["target_modulus"], "target modulus", 1) == 27, "wrong target modulus")
    need(type(data["target_residues"]) is list
         and all(type(x) is int for x in data["target_residues"])
         and data["target_residues"] == list(range(1, 28)), "residue partition mismatch")
    need(type(data["target_phases"]) is list
         and all(type(x) is int for x in data["target_phases"])
         and data["target_phases"] == list(range(7)), "phase partition mismatch")
    need(type(data["rows"]) is list, "rows must be a list")
    need(integer(data["row_count"], "row count", 1) == len(data["rows"]) == 189,
         "wrong number of affine rows")
    domains = set()
    steps_total = 0
    lengths = Counter()
    grow_histogram = Counter()
    source_parameters = []
    for index, row in enumerate(data["rows"]):
        tag = f"row {index}"
        need(type(row) is dict and set(row) == {
            "target_phase", "target_residue", "target_z", "source_phase", "source_t",
            "source_z", "steps", "inverse_word", "forward_physical_trace",
        }, tag + " has unexpected fields")
        phase = integer(row["target_phase"], tag + " target phase", 0)
        residue = integer(row["target_residue"], tag + " target residue", 1)
        need(phase < 7 and residue <= 27, tag + " target domain is out of range")
        need((phase, residue) not in domains, tag + " duplicates a target domain")
        domains.add((phase, residue))
        need(pair(row["target_z"], tag + " target z") == (27, residue), tag + " target ray mismatch")
        need(integer(row["source_phase"], tag + " source phase") == 1, tag + " source is not in phase one")
        source_a, source_b = pair(row["source_t"], tag + " source t")
        need(source_a > 0 and source_b >= 1, tag + " B1 parameter is not positive on the full ray")
        need(pair(row["source_z"], tag + " source z") == (6 * source_a, 6 * source_b),
             tag + " source z does not identify its B1 launch")
        steps = integer(row["steps"], tag + " steps", 1)
        need(steps <= 30, tag + " exceeds the stated clock bound")
        word = row["inverse_word"]
        need(type(word) is str and len(word) == steps and set(word) <= {"G", "S"},
             tag + " has an invalid inverse word")
        trace = row["forward_physical_trace"]
        need(type(trace) is list and len(trace) == steps + 1, tag + " trace length mismatch")
        a, b, p = 6 * source_a, 6 * source_b - 1, 1
        for tick, state in enumerate(trace):
            need(type(state) is dict and set(state) == {"phase", "n"}, tag + " trace fields mismatch")
            need(integer(state["phase"], tag + " trace phase") == p, tag + " physical phase mismatch")
            need(pair(state["n"], tag + " trace n") == (a, b), tag + " physical affine trace mismatch")
            # n(v) >= h[p] for every v>=0; safe zeros retain their dynamics.
            need(a > 0 and b >= HEIGHTS[p], tag + " leaves the safe physical domain")
            if tick == steps:
                break
            need(a % 2 == 0, tag + " parity is not uniform on its full affine ray")
            is_odd = b % 2
            need(word[steps - 1 - tick] == ("G" if is_odd else "S"),
                 tag + " inverse word disagrees with physical parity")
            if is_odd:
                a, b = 3 * a // 2, (3 * b + 1) // 2 + IMPULSES[p]
            else:
                a, b = a // 2, b // 2 + IMPULSES[p]
            p = (p + 1) % 7
        need((a, b, p) == (27, residue - 1 + HEIGHTS[phase], phase),
             tag + " does not reach its exact target ray")
        steps_total += steps
        lengths[steps] += 1
        grow_histogram[word.count("G")] += 1
        source_parameters.append((source_a, source_b))
    need(domains == {(p, r) for p in range(7) for r in range(1, 28)},
         "target rays do not cover every phase and positive integer")
    need(integer(data["clock_maximum"], "clock maximum", 1) == max(lengths) == 30,
         "clock maximum is not the actual maximum")
    phase_one = [row for row in data["rows"] if row["target_phase"] == 1]
    return {
        "status": "PASS",
        "target_modulus": 27,
        "whole_affine_rays": len(domains),
        "physical_affine_steps": steps_total,
        "max_steps": max(lengths),
        "phase_one_target_rays": len(phase_one),
        "phase_one_max_steps": max(row["steps"] for row in phase_one),
        "minimum_source_t_intercept": min(b for _, b in source_parameters),
        "inverse_grow_counts": dict(sorted(grow_histogram.items())),
        "clock_histogram": dict(sorted(lengths.items())),
        "scope": "Whole affine domains v>=0; no sampled-seed inference and no B1 capture premise discharged.",
    }


def corruption_tests(original: dict) -> list[str]:
    mutations = []

    def add(name, change):
        data = deepcopy(original)
        change(data)
        mutations.append((name, data))

    add("wrong physical impulse", lambda d: d["model"]["physical_impulses"].__setitem__(2, 0))
    add("truncated-zero convention", lambda d: d["model"].__setitem__("zero_convention", "zero stops"))
    add("wrong claim", lambda d: d.__setitem__("claim", "every B1 source is captured"))
    add("missing parameter boundary", lambda d: d.__setitem__("parameter_domain", "v >= 1"))
    add("wrong target modulus", lambda d: d.__setitem__("target_modulus", 9))
    add("missing residue metadata", lambda d: d["target_residues"].pop())
    add("missing phase metadata", lambda d: d["target_phases"].pop())
    add("missing target ray", lambda d: d["rows"].pop())
    add("duplicate target ray", lambda d: d["rows"].__setitem__(1, deepcopy(d["rows"][0])))
    add("wrong target residue", lambda d: d["rows"][0].__setitem__("target_residue", 0))
    add("wrong target phase", lambda d: d["rows"][0].__setitem__("target_phase", 7))
    add("wrong target affine coefficient", lambda d: d["rows"][0]["target_z"].__setitem__(0, 54))
    add("wrong source phase", lambda d: d["rows"][0].__setitem__("source_phase", 2))
    add("boolean source coefficient", lambda d: d["rows"][0]["source_t"].__setitem__(0, True))
    add("negative source coefficient", lambda d: d["rows"][0]["source_t"].__setitem__(0, -1))
    add("zero source boundary", lambda d: d["rows"][0]["source_t"].__setitem__(1, 0))
    add("wrong source z", lambda d: d["rows"][0]["source_z"].__setitem__(1, 6))
    add("wrong elapsed clock", lambda d: d["rows"][0].__setitem__("steps", d["rows"][0]["steps"] + 1))
    add("invalid inverse symbol", lambda d: d["rows"][0].__setitem__("inverse_word", "X" * d["rows"][0]["steps"]))
    add("false physical trace", lambda d: d["rows"][0]["forward_physical_trace"][1]["n"].__setitem__(1, 0))
    add("false intermediate phase", lambda d: d["rows"][0]["forward_physical_trace"][1].__setitem__("phase", 0))
    add("missing trace endpoint", lambda d: d["rows"][0]["forward_physical_trace"].pop())
    add("incorrect maximum clock", lambda d: d.__setitem__("clock_maximum", 29))
    add("incorrect row count", lambda d: d.__setitem__("row_count", 188))
    rejected = []
    for name, data in mutations:
        try:
            check(data)
        except InvalidCertificate:
            rejected.append(name)
        else:
            raise InvalidCertificate(f"Corruption was accepted: {name}")
    return rejected


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate", type=Path, default=Path(__file__).with_name("b1_entry_certificate.json"))
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    raw = args.certificate.read_bytes()
    data = json.loads(raw)
    report = check(data)
    report["corruptions_rejected"] = corruption_tests(data)
    report["corruption_count"] = len(report["corruptions_rejected"])
    report["certificate_sha256"] = hashlib.sha256(raw).hexdigest()
    need(raw == args.certificate.read_bytes(), "verification changed its source certificate")
    payload = json.dumps(report, indent=2, sort_keys=True) + "\n"
    if args.output is not None:
        args.output.write_text(payload)
    print(payload, end="")


if __name__ == "__main__":
    main()
