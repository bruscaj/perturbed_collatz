# Exact geometry certificates

This bundle checks the signed forcing `(+1, 0, -1)` with continued zero dynamics,
and the explicitly chosen entire interpolation

```text
C(z) = z + 1/4 - (z/2 + 1/4) cos(pi*z).
```

The integer system, its binary-digit layout, and the smooth interpolation have
different notions of a basin. The manuscript section **Integer basins, binary
neighborhoods, and a complex continuation** provides the analytical arguments
connecting these finite certificates to their stated universal conclusions.

## Reproduce

From the standalone release root, use Python 3.10 or later:

```sh
python3 -B certificates/geometry/verify.py
```

Only the standard library is required. The verifier recomputes every exact
certificate and compares the full result with `certificate.json`, using canonical
type-sensitive JSON. Duplicate keys, floating-point number tokens, and nonfinite
numbers are rejected; rational values must keep their exact string encoding.
Twenty-five cached negative cases exercise changed bounds, omitted disks and
cover leaves, missing trace points, wrong phase/time/model, type substitutions,
and empty data. It also checks
that all seven Python entrypoints reject `python -O`; every substantive comparison
uses an explicit failure check in addition to that safeguard. Run with
`--output /path/to/report.json` to save a concise report. The committed
`verification.json` records a successful regeneration and comparison.

For an intentional data refresh, `--write` replaces `certificate.json` with the
regenerated result. A normal subsequent run must still reproduce it exactly.
The refresh flag does not bypass the mathematical checks.

## What is checked

| Module | Exact scope |
| --- | --- |
| `discrete.py` | Two nonnegative cycles of physical periods three and nine; the separate signed negative three-cycle; all eight affine branches of one return; exact integer and binary-zoom examples. |
| `integer_disks.py` | Radius `1/1,000,000` complex capture disks at every phase-tagged center of those integer cycles, with uniform nonlinear and complete-cycle contraction bounds. |
| `attracting_disks.py` | Twelve cyclic disk inclusions enclosing two positive noninteger cycles, their disjoint same-phase disks, exact derivative-product bounds, and real multiplier intervals. |
| `separator.py` | A complete rational interval cover of `[0, 9/50]`, root brackets, derivative/sign inequalities, and the inward right endpoint used in the real-basin partition. |
| `phase_trace.py` | The point `71/100 + i/50` at all three launch phases, with certified first entries into the respective integer target disks at updates `43`, `91`, and `38`. |
| `rational.py` | Machin arctangent enclosure of pi, interval arithmetic, rational rounding, and real Taylor bounds. |
| `verify.py` | Complete regeneration, saved-output comparison, and optimization safeguards. |

Every numeric proof comparison uses exact integers or `fractions.Fraction`.
The phase-trace centers are generated deterministically from rational Taylor
polynomials and rounded rationally; `cmath`, floating-point trigonometry, and
floating-point trajectories are not used by the checker. Its balls enclose the
true complex orbit through explicit Taylor remainders and a bound on the second
derivative. The minimum distance tests use squared rational distances, so they
do not need numerical square roots.

The certificate JSON exposes rational strings, exact decimal disk centers, full
phase-tagged cycle lists, separator brackets, and the rational trajectory balls.
The rendering code can use these as inputs, but a floating-point raster remains
a numerical visualization. A sample hitting a magnitude guard or exhausting an
iteration budget is unresolved; it is not a certified divergent orbit.

## Scope and trust boundary

The bundle proves **five specific attracting cycles** of the chosen smooth
model. It does not enumerate every smooth attractor, classify all complex basin
boundaries, establish natural densities of the integer basins, or prove that the
two known nonnegative integer cycles capture every seed. The negative cycle is
outside the original safe nonnegative integer domain. The two noninteger cycles
are not integer-cycle counterexamples.

The analytic reasoning for the interval and disk majorants, induction through
error balls, contraction mapping, and basin conclusions is given in the
manuscript. The Python runtime and exact rational implementation are part of
this computer-assisted proof's trust boundary. These smooth certificates have
not been formalized in Lean. The separately shipped Lean inverse and binary-zoom
theorems retain their own explicit model and hypotheses. The new signed
`Collatz.Physical.cycle_multiplier_lt_one` theorem separately proves the
integer arithmetic cycle-gain inequality; it does not formalize the cosine
derivatives, rational disk/interval interpreter, or smooth basin arguments.
