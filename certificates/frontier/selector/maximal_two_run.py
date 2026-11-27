"""Exact maximal-run decoder for positive B1 words G^k H^j.

G(t)=(243*t+52)/128 on t == 4 (mod 128).
H(t)=(9*t+29)/128 on t == 11 (mod 128).

select(t) accepts exactly when some legal word G^k H^j, k,j >= 1,
has a positive endpoint smaller than t. It computes one G-run length
and one H-run length by valuations; it does not search over run lengths.
The audit uses separate guarded iteration and the original physical map.
This module uses only the Python standard library.
"""

from __future__ import annotations

from dataclasses import asdict, dataclass
from fractions import Fraction
from hashlib import sha256
from pathlib import Path
import argparse
import json


FORCING = (0, 0, 1, -1, 0, 1, -1)
SAFE_FLOOR = (0, 0, 0, 1, 0, 0, 1)


@dataclass(frozen=True, slots=True)
class Certificate:
    source_t: int
    target_t: int
    g_steps: int
    h_steps: int
    physical_steps: int
    w_drop: int


def v2(n: int) -> int:
    """The exponent of 2 in a positive integer."""
    if n <= 0:
        raise ValueError("v2 requires a positive integer")
    return (n & -n).bit_length() - 1


def select(t: int) -> Certificate | None:
    """Return the last, hence smallest, endpoint of the maximal H suffix.

    No external depth cap, physical simulation, or enumeration of k or j
    is used. Returning None means only that this particular grammar has
    no strict original-parameter reduction at this source.
    """
    if type(t) is not int or t <= 0:
        return None
    x = 115 * t + 52
    e = v2(x)
    # An H entry is odd; therefore the valuation after the G prefix is 0.
    # This also explicitly excludes the empty G prefix.
    if e < 7 or e % 7:
        return None
    k = e // 7
    g_numerator = pow(243, k) * (x >> e) - 52
    s, remainder = divmod(g_numerator, 115)
    if remainder or s <= 0:
        raise ArithmeticError("G conjugacy failed to give a positive integer")
    z = 119 * s - 29
    j = v2(z) // 7
    if j == 0:
        return None
    h_numerator = pow(9, j) * (z >> (7 * j)) + 29
    y, remainder = divmod(h_numerator, 119)
    if remainder or y <= 0:
        raise ArithmeticError("H conjugacy failed to give a positive integer")
    if y >= t:
        return None
    return Certificate(t, y, k, j, 7 * (k + j), 8 * (t - y))


def direct_select(t: int) -> Certificate | None:
    """Independent, guarded macro iteration, used for audit only."""
    if type(t) is not int or t <= 0:
        return None
    s = t
    k = 0
    while s % 128 == 4:
        s = (243 * s + 52) // 128
        k += 1
    if k == 0:
        return None
    j = 0
    while s % 128 == 11:
        previous = s
        s = (9 * s + 29) // 128
        if not 0 < s < previous:
            raise AssertionError("A legal positive H step failed to decrease")
        j += 1
    if j == 0 or s >= t:
        return None
    return Certificate(t, s, k, j, 7 * (k + j), 8 * (t - s))


def fixed_quota_accepts(t: int) -> bool:
    """Membership in the earlier G^k H^ceil(k/4) source family."""
    if type(t) is not int or t <= 0:
        return False
    x = 115 * t + 52
    e = v2(x)
    if e < 7 or e % 7:
        return False
    k = e // 7
    j = (k + 3) // 4
    modulus = 1 << (7 * j)
    q = x >> e
    return (119 * pow(243, k, modulus) * (q % modulus) - 9523) % modulus == 0


def verify_physical(cert: Certificate) -> None:
    """Replay the original signed physical recurrence, with explicit phases."""
    if not (cert.source_t > cert.target_t > 0):
        raise AssertionError("Certificate must decrease the original parameter")
    if not (cert.g_steps >= 1 and cert.h_steps >= 1):
        raise AssertionError("Both runs must be nonempty")
    if cert.physical_steps != 7 * (cert.g_steps + cert.h_steps):
        raise AssertionError("Clock mismatch")
    if cert.w_drop != 8 * (cert.source_t - cert.target_t):
        raise AssertionError("Original W-drop mismatch")
    n, phase = 6 * cert.source_t - 1, 1
    for _ in range(cert.physical_steps):
        if n < SAFE_FLOOR[phase]:
            raise AssertionError("Unsafe intermediate physical state")
        n = (n // 2 if n % 2 == 0 else (3 * n + 1) // 2) + FORCING[phase]
        phase = (phase + 1) % 7
    if (n, phase) != (6 * cert.target_t - 1, 1):
        raise AssertionError("Physical endpoint or phase mismatch")
    if n < SAFE_FLOOR[phase]:
        raise AssertionError("Unsafe final physical state")


def word_progression(k: int, j: int) -> dict[str, int]:
    """The entire legal G^k H^j ray: t=M*v+r, endpoint=A*v+B.

    This construction lifts one base-128 digit per guard. It is independent
    of the valuation decoder and has no assumed rank decrease.
    """
    if k < 1 or j < 1:
        raise ValueError("Both run lengths must be positive")
    modulus, residue, slope, offset = 1, 0, 1, 0
    for a, b, guard in [(243, 52, 4)] * k + [(9, 29, 11)] * j:
        digit = ((guard - offset) * pow(slope, -1, 128)) % 128
        residue += modulus * digit
        modulus *= 128
        numerator = a * (slope * digit + offset) + b
        offset, remainder = divmod(numerator, 128)
        if remainder:
            raise AssertionError("Guard lift did not yield an integer")
        slope *= a
    if not (0 < residue < modulus and offset > 0):
        raise AssertionError("Nonpositive source or endpoint representative")
    return {"g_steps": k, "h_steps": j, "source_a": modulus,
            "source_b": residue, "target_a": slope, "target_b": offset}


def verify_affine_physical(ray: dict[str, int]) -> list[dict[str, int]]:
    """Exact replay for every integer v>=0, using physical affine states.

    At every update the coefficient is even, so the constant fixes parity
    throughout the ray. Nonnegative coefficients and safe constants prove
    all intermediate states safe for the whole ray, not merely samples.
    """
    a, b, phase = 6 * ray["source_a"], 6 * ray["source_b"] - 1, 1
    steps = 7 * (ray["g_steps"] + ray["h_steps"])
    trace: list[dict[str, int]] = []
    for clock in range(steps + 1):
        if a < 0 or b < SAFE_FLOOR[phase]:
            raise AssertionError("Whole-ray safety or slope failure")
        trace.append({"clock": clock, "phase": phase, "n_a": a, "n_b": b})
        if clock == steps:
            break
        if a % 2:
            raise AssertionError("Physical parity is not uniform on this ray")
        if b % 2:
            a, b = 3 * a // 2, (3 * b + 1) // 2 + FORCING[phase]
        else:
            a, b = a // 2, b // 2 + FORCING[phase]
        phase = (phase + 1) % 7
    expected = (6 * ray["target_a"], 6 * ray["target_b"] - 1, 1)
    if (a, b, phase) != expected:
        raise AssertionError("Whole-ray physical endpoint mismatch")
    return trace


def verify_affine_macros(ray: dict[str, int]) -> None:
    """Independently check every G/H guard for every source on a whole ray."""
    a, b = ray["source_a"], ray["source_b"]
    word = [(243, 52, 4)] * ray["g_steps"] + [(9, 29, 11)] * ray["h_steps"]
    for slope, offset, guard in word:
        if a <= 0 or b <= 0 or a % 128 or b % 128 != guard:
            raise AssertionError("A whole-ray macro guard is not valid")
        a, b = slope * a // 128, (slope * b + offset) // 128
    if (a, b) != (ray["target_a"], ray["target_b"]):
        raise AssertionError("Whole-ray macro endpoint mismatch")


def strict_extension_ray() -> tuple[dict[str, int], list[dict[str, int]]]:
    """A whole G^33 H^8 ray whose H-run ends exactly after eight steps."""
    base = word_progression(33, 8)
    for digit in range(128):
        t0 = base["source_a"] * digit + base["source_b"]
        y0 = base["target_a"] * digit + base["target_b"]
        if y0 % 128 != 11 and 0 < y0 < t0:
            break
    else:
        raise AssertionError("No strict-extension subray found")
    ray = {"g_steps": 33, "h_steps": 8,
           "source_a": 128 * base["source_a"], "source_b": t0,
           "target_a": 128 * base["target_a"], "target_b": y0,
           "base_ray_digit": digit, "exit_residue_mod128": y0 % 128}
    if not (ray["source_a"] > ray["target_a"] > 0
            and ray["source_b"] > ray["target_b"] > 0):
        raise AssertionError("The entire ray must strictly decrease")
    if ray["source_a"] != 2**294 or ray["target_a"] != 128 * 3**181:
        raise AssertionError("Unexpected exact ray slopes")
    # Exact maximal G-run, and constant non-H exit on this whole subray.
    e0 = v2(115 * ray["source_b"] + 52)
    if e0 != 7 * 33 or v2(115 * ray["source_a"]) <= e0:
        raise AssertionError("G-run length is not uniformly 33")
    if ray["target_a"] % 128 or ray["exit_residue_mod128"] == 11:
        raise AssertionError("H exit must be uniformly outside its guard")
    verify_affine_macros(ray)
    trace = verify_affine_physical(ray)
    for v in (0, 1, 2, 17, 10**20):
        t = ray["source_a"] * v + ray["source_b"]
        expected_y = ray["target_a"] * v + ray["target_b"]
        cert = select(t)
        if cert is None or (cert.g_steps, cert.h_steps, cert.target_t) != (33, 8, expected_y):
            raise AssertionError("Strict-extension selector mismatch")
        if fixed_quota_accepts(t):
            raise AssertionError("The earlier fixed-quota family unexpectedly accepts")
        verify_physical(cert)
    return ray, trace


def audit() -> dict[str, object]:
    finite_limit = 131072
    accepted = 0
    quota_accepted = 0
    maximum_clock = 0
    for t in range(1, finite_limit + 1):
        cert, independently_iterated = select(t), direct_select(t)
        if cert != independently_iterated:
            raise AssertionError(("Finite-domain decoder mismatch", t))
        if cert is not None:
            accepted += 1
            maximum_clock = max(maximum_clock, cert.physical_steps)
            verify_physical(cert)
        if fixed_quota_accepts(t):
            quota_accepted += 1
            if cert is None:
                raise AssertionError("An earlier fixed-quota source was lost")
    for bad in (0, -1, -128, True, 1.0, "4", None):
        if select(bad) is not None:
            raise AssertionError("Invalid original parameter was accepted")
    if select(4) is not None or select(11) is not None:
        raise AssertionError("An empty G or H prefix was accepted")

    generated_inputs = 0
    generated_reductions = 0
    generated_fixed_quota_sources = 0
    max_source_bits = 0
    for k in list(range(1, 41)) + [64, 128, 256]:
        quota = (k + 3) // 4
        js = sorted({1, 2, max(1, quota - 1), quota, quota + 1})
        for j in js:
            ray = word_progression(k, j)
            for v in (0, 1, 2, 17):
                t = ray["source_a"] * v + ray["source_b"]
                cert = select(t)
                if cert != direct_select(t):
                    raise AssertionError(("Generated-ray decoder mismatch", k, j, v))
                generated_inputs += 1
                max_source_bits = max(max_source_bits, t.bit_length())
                if cert is not None:
                    generated_reductions += 1
                    maximum_clock = max(maximum_clock, cert.physical_steps)
                    verify_physical(cert)
                if j >= quota:
                    generated_fixed_quota_sources += 1
                    if cert is None or not fixed_quota_accepts(t):
                        raise AssertionError("An unbounded fixed-quota source was lost")

    ray, trace = strict_extension_ray()
    trace_json = json.dumps(trace, sort_keys=True, separators=(",", ":")).encode()
    beta = Fraction(3**181, 2**287)
    c, d = Fraction(52, 115), Fraction(29, 119)
    margin9 = 9 - beta * (9 + c) - d
    if not beta < 1 or not margin9 > 0:
        raise AssertionError("G33H8 whole-word bound failed")
    return {
        "status": "PASS",
        "scope": "Exact arithmetic selector, independently proved membership, and exact whole-affine physical ray. Finite regression counts do not prove a global coverage claim.",
        "selector_domain": "positive t with some legal G^k H^j, k,j>=1, whose endpoint is below original t",
        "run_length_search": "none: one G valuation and one H valuation",
        "external_depth_cap": None,
        "finite_domain": {"maximum_t": finite_limit, "maximal_two_run_accepted": accepted,
                          "fixed_quota_accepted": quota_accepted},
        "generated_ray_checks": {"inputs": generated_inputs, "accepted": generated_reductions,
                                 "fixed_quota_sources_preserved": generated_fixed_quota_sources,
                                 "largest_G_run_generated": 256, "largest_source_bits": max_source_bits,
                                 "largest_physical_clock_verified": maximum_clock},
        "strict_extension_ray": ray,
        "strict_extension_properties": {
            "all_v_ge0": True,
            "physical_steps": 287,
            "maximal_G_steps": 33,
            "maximal_H_steps": 8,
            "earlier_required_H_steps": 9,
            "whole_affine_macro_guards_verified": 41,
            "original_parameter_gap_a": ray["source_a"] - ray["target_a"],
            "original_parameter_gap_b": ray["source_b"] - ray["target_b"],
            "relative_slope": str(beta),
            "safe_uniform_margin_at_t9": str(margin9),
            "affine_states_verified": len(trace),
            "affine_trace_sha256": sha256(trace_json).hexdigest(),
        },
        "ordinary_binary_regularity_of_enlarged_domain": "not established; no inference from containing a nonregular subset",
        "coverage_novelty_scope": "Strictly beyond the fixed ceil(k/4) G/H family only; no union-of-historical-or-current-main comparison",
        "source_sha256": sha256(Path(__file__).read_bytes()).hexdigest(),
        "whole_affine_physical_trace": trace,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument('--output', type=Path,
                        default=Path(__file__).with_name('maximal_two_run_audit.json'))
    args = parser.parse_args()
    report = audit()
    output = args.output
    output.write_text(json.dumps(report, indent=2) + "\n")
    visible = {k: v for k, v in report.items()
               if k not in ("whole_affine_physical_trace", "strict_extension_ray", "strict_extension_properties")}
    visible["strict_extension_summary"] = {"G_steps": 33, "H_steps": 8,
                                          "physical_steps": 287, "whole_affine_states": 288,
                                          "exit_residue_mod128": report["strict_extension_ray"]["exit_residue_mod128"]}
    print(json.dumps(visible, indent=2))


if __name__ == "__main__":
    main()
