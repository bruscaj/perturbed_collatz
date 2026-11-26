# Seven-step exact certificates

This package supports the manuscript section **A fixed seven-step forcing**.
It supports two conditional reductions, to four and to three infinite capture
obligations, for the prescribed forcing `(0, 0, 1, -1, 0, 1, -1)`.
The sections and ranks are different and are not combined by subtracting counts.
It does not prove capture of either complete residual family set, universal capture of this forcing, or the Collatz
conjecture. The Python programs here are exact arithmetic reconstructions.
The positive-seed three-family equivalence also has a separate Lean proof
in `lean/inverse/Collatz/ReleaseBridge.lean`; its family hypotheses remain open.

## Run

From the release root, using Python 3 and its standard library:

```sh
python3 certificates/seven_step/verify.py
python3 certificates/seven_step/test_mutations.py
python3 certificates/seven_step/three_family.py
python3 certificates/seven_step/test_three_family.py
```

The commands also work from another directory when invoked by absolute path.
No network, original research checkout, external data, or Python package is
needed. The first command reconstructs both stored certificates in a temporary
directory and requires every stored field to match. It then performs an
independent reconstruction in the positive coordinate. A failure exits with a
nonzero status. An optional `--output PATH` writes the full successful report.

`test_mutations.py` first accepts the authentic data, then requires rejection of
altered rank and scope statements, return convention, forcing, affine
coefficients, phases, return times, parameter bounds, family coverage, finite
exceptions, rank gaps, envelope bounds, and obstruction witnesses. It also
checks malformed, empty, duplicate-key, and wrong-type data. Finally, it
requires all three assertion-based command entry points to reject Python
optimization (`-O`) without writing a success report.

## Files

| File | Role |
| --- | --- |
| `verify.py` | Reconstructs both certificates, checks all fields, and runs the independent reconstruction. |
| `verify_relational.py` | Physical-coordinate proof calculations for section entry, long returns, full short-return coverage, the merger, and the refined rank. |
| `frontier.json` | Exact output of those calculations, including the four unresolved families. |
| `verify_rank_obstruction.py` | Eleven disjoint first-return witnesses and six exact slope cycles for the phase-affine rank obstruction. |
| `rank_obstruction.json` | Witness traces and the exact obstruction calculation. |
| `independent.py` | Separately written positive-coordinate reconstruction of the 384 entry domains and 392 section domains, with symbolic verification of the coordinate conjugacy. |
| `test_mutations.py` | Hostile certificate and disabled-assertion tests. |
| `three_family.py` | Standalone reconstruction of the alternative 43-cylinder section, all 324 physical classes, uniform entry, finite captures, and the three-cycle rank obstruction. |
| `three_family.json` | Complete alternative section data, with three unresolved families and five exact capture chains. |
| `test_three_family.py` | Eighteen altered/malformed certificates and two optimized entry points must be rejected. |

To regenerate the data explicitly, run:

```sh
python3 certificates/seven_step/verify_relational.py --output certificates/seven_step/frontier.json
python3 certificates/seven_step/verify_rank_obstruction.py --output certificates/seven_step/rank_obstruction.json
python3 certificates/seven_step/verify.py
```

Regeneration changes data files. Ordinary verification does not.

## Exact mathematical scope

Use phases `0,...,6`, heights `(0,0,0,1,0,0,1)`, and
`z = n + 1 - height[phase]`. In this coordinate the prescribed word is
`UUUTUUT`. The section consists of `z = 3m`, `m >= 1`, at phases 3, 5, and 6.
Returns count the first strictly later section visit, including visits after
shrinking steps.

The primary simultaneous rank is `V(m,3)=V(m,5)=m`, `V(m,6)=2m`.
The merger uses the refinement
`rho(m,3)=rho(m,5)=2m`, `rho(m,6)=4m+1`.

The exact input partitions are 384 phase-zero domains for entry, and
`8 + 256 + 128 = 392` section domains for short returns. Each domain denotes
an entire arithmetic progression with an explicit parameter lower bound.
Integer coefficient propagation fixes every required parity and section
guard. This is not a scan of finitely many numerical seeds.

The remaining launch parameters are:

| ID | Section launch `(m, phase)` | Parameter domain |
| --- | --- | --- |
| S00 | `(4t + 3, 3)` | Integers `t >= 0` |
| S01 | `(2t, 5)` | Integers `t >= 1` |
| S02 | `(32t + 3, 5)` | Integers `t >= 0` |
| S03 | `(128t + 115, 5)` | Integers `t >= 0` |

The manuscript proves that capture of all positive physical seeds at every
phase is equivalent to capture of every launch in these four families. It
also proves the six-domain lower bound for the specific direct rank class
`R(m,i)=w_i*m+c_i`, with positive real weights and fixed real offsets. The
constraint cycles in that proof are not asserted to be orbit cycles.

## Alternative three-family section

Use the same forcing and positive coordinate, but mark phases `(1,2,3,5)`
with `z=3m`, `m>=1`, and the single rank `W=(4m,7m,4m,5m)`.
First returns have caps `(2,7,6,7)`. An adaptive parity partition has
43 disjoint cylinders; a separately implemented physical-coordinate
reconstruction checks all 324 fixed-modulus classes. All 1,536 phase-zero
entry rays enter within five updates, giving at most eleven from any phase.

| ID | Section launch `(m, phase)` | Parameter domain |
| --- | --- | --- |
| B1 | `(2t,1)` | Integers `t>=1` |
| A3 | `(4t+3,3)` | Integers `t>=0` |
| N03 | `(8t+2,5)` | Integers `t>=0` |

Every other first return strictly decreases W except the five finite states
`(1,1),(1,3),(1,5),(3,5),(5,3)`, whose literal capture times are
`4,2,0,14,16`. The manuscript proves equivalence between global capture
and capture of these three whole families by least-W induction. It also
proves that three growing domains are unavoidable for direct positive
phase-affine ranks on this section. No modulo-27 tagged refinement is
included and no remaining capture obligation is closed.

To regenerate this additional certificate explicitly:

```sh
python3 certificates/seven_step/three_family.py --output certificates/seven_step/three_family.json
python3 certificates/seven_step/three_family.py
```

## Trust boundary

The checks rely on the Python interpreter and their source code. The data
comparison binds all metadata, rejects duplicate JSON keys and nonstandard
numeric constants, and distinguishes booleans and floats from integer fields.
The independent reconstruction uses the same stated mathematics but does not
import the primary checker's arithmetic implementation.

For the original four-family section, the manuscript supplies the arguments
for entry, control beyond the short verification caps, phase-correct mergers,
and well-founded induction; that theorem is not formalized here. The alternative
three-family equivalence has a separate signed Lean proof and release bridge.
The 43 source Lean rows were independently matched to the table and Python
rows, including the shifted zero-residue parameter convention. Its direct
positive-seed entry bound is six updates; the Python/manuscript safe-state
bound of eleven is a distinct auxiliary statement. The Python checkers are
not converted into kernel proofs by this correspondence. Proving the three
universal capture hypotheses, and formalizing the remaining written claims,
remain separate tasks.
