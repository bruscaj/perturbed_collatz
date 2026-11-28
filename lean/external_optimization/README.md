# Finite optimization and computable approximation

This standalone Lean 4.35.0/mathlib project implements 15 frozen targets for
finite strict-cycle deletion optimization and certified approximation of the
literal run-window O3 prime infimum. It includes a total computable program
returning the exact finite graph's integer deletion numerator. No efficiency
claim, exact higher-depth closed form, sharp asymptotic constant, global Collatz
convergence, or bridge-pressure limit is asserted.

**Full source-pinned assurance passed:** at `b5dcda3404b14b43e1985c2e31219ce811e46881`, run 46111672437 passed all seven mandatory jobs. This project covered all 15 required frozen statements and 952 own/reused theorem/helper closures: fresh source-bound replay, trusted comparison, all six checker modes in both stages, and 18 rejected controls following a second positive full pipeline. [Exact receipts and complete archives](../../verification/external_optimization/README.md) preserve the checked source/tree and 63 project digests. Later source or documentation changes require their own regression.

For positive depth h and M,J≥2, vertices encode h run lengths in {1,…,M}.
Ascending edges decrease the first run length; exit edges retain their halving
label K∈{2,…,J}, including distinct parallel edges. The exact edge gain is
log(3)−K·log(2), with arbitrary real vertex potentials. A deleted edge subset is
safe when every surviving directed cycle has strictly negative total gain.
Generic finite-graph results identify minimum failure weight with minimum safe
deletion cost and reduce cycle testing to elementary cycles. Exact dyadic edge
weights give a common denominator 2^(J+hM), and an attained natural numerator.

The original corrections are arbitrary real functions on the full positive
run-window domain. Finite vertex potentials extend to that domain. The graph's
retained source-cylinder weights, omitted mass and the previously proved literal
density law yield a rational bracket for the infimum over achieved odd-seed
natural failure densities. This infimum is not substituted by an assumed density
or a trajectory independence hypothesis.

`OptimizationCode.optimizer` is an explicit finite search over masks. It tests
closed labeled-edge words of lengths 1 through the vertex count using the exact
integer comparison 3^length < 2^sumK, and minimizes integer cost. Invalid numeric
slots are ignored; loops, parallel exits and all safe deletion subsets are
represented. The program uses no real comparisons or noncomputable minimizer.
The proof supplies a uniform `Primrec`/`Computable` certificate and equality to
the original canonical numerator, including the fallback case.

For an input (h0,b), h=h0+1 and M=J=h+b+2. The resulting exact numerator divided
by 2^(J+hM) is q with q≤p_h≤q+2^(-b). Computability and correctness hold uniformly
for all natural inputs; this exhaustive algorithm may be very expensive.

The pinned primary source is [Polson–Sokolov v1.4.0, O3 prime](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch11_open.tex),
label `prob:ch11:o3p`, with its stated Syracuse/run conventions. Finite optimization
is a constructive companion to that literal infimum problem. Jake S. Brusca is
the author; ChatGPT assisted with ideas, proofs, code, writing and separate-context
AI review. No human expert refereeing, novelty certification or external
acceptance is claimed.

The self-contained [written proof](OPTIMIZATION_PROOF.md) reconstructs the finite
cycle/deletion equivalences, source truncation, integer program and its uniform
correctness and accuracy bounds.

## Frozen meanings and coverage

Ten primitive/type/challenge files retain their exact canonical bytes:
`Definitions`, `ExpectedTypes`, `GeneralDefinitions`, `GeneralExpectedTypes`,
`RateDefinitions`, `RateExpectedTypes`, `OptimizationDefinitions`,
`OptimizationExpectedTypes`, `OptimizationAlgorithmTypes`, and
`OptimizationChallenge` (all `.lean`). Historical draft comments remain in these
frozen bytes. `specification.json` pins them. The original elaborated proposition
register is preserved as `frozen_propositions.json`: the 15 required statements
are implemented, while its optional `MonotonicFiniteOptimum` entry is not claimed.
The isolated Challenge holes are never imported by the implementation.

The 49 canonical owned modules are listed in `owned_modules.json`. `Audit.lean`
checks the 15 exact types and all owned theorem/helper closures, rejects own
custom axioms and imported Challenge holes, and permits only `propext`,
`Quot.sound`, and `Classical.choice`. `inventory.json` binds the complete source,
configuration, type and helper inventories. The optional monotonicity Challenge
and all private audit adapters are excluded.

## Reproduce

1. Install the official toolchain named in `lean-toolchain`.
2. Run `lake resolve-deps` to prepare exact public Git-pinned dependencies.
3. Fetch selected official mathlib caches with
   `xargs lake exe cache get < cache-imports.txt`.
4. On Linux run `python3 verify.py --mode full --report /tmp/optimization-full.json`.
5. Run `python3 test_mutations.py --mode full --report /tmp/optimization-controls.json`.

Dependency fetching is separate from verification. The verifier never downloads
or updates dependencies and never reuses own proof build outputs. `--mode build`
performs a clean own-source build and complete transitive axiom audit only.
`--toolchain DIR` selects the official compiler. `--dependency-cache DIR` accepts
a prepared `.lake/packages` directory; alternatively `--mathlib-cache DIR`
accepts the pinned public mathlib checkout and its normal dependency cache.
Caches are copied without modification and their exact Git source pins are
checked. Missing dependencies, unavailable checkers and failed gates fail closed.

Full mode exports every inventoried own theorem/helper root from a fresh Audit
environment, then requires `lake check --from-export ... --paranoid` and the
trusted comparator on all 15 frozen statements. Both stages must explicitly
report acceptance by Lean default, Lean paranoid, lean4lean, nanoda, con-leche
and con-ron. Large complete audit output is saved compressed next to the report;
its size and SHA-256 are also recorded. Compilation alone does not establish
that those replay and comparison gates ran.
