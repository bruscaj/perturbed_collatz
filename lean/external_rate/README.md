# Inverse-depth rate for the run-length-only O3′ model

This standalone Lean 4.35.0/mathlib project implements all 11 required frozen
rate targets. If p_h is the infimum of actual relative odd-seed failure densities
over every real correction of the h-length window, the statements include

    127/(32768 h) ≤ p_h ≤ 5/(2 h),  h≥1,
    p_h → 0.

**Verified source snapshot:** all 11 targets, 765 theorem/helper closures, fresh
source-bound replay, frozen comparison, all six checker modes and 10 hostile
controls passed at commit `1406f1a` in run `46101939355`. The [exact receipts](../../verification/external_rate/README.md)
record the checked source/tree and all project hashes. Historical pending text
in the frozen specification metadata and manuscript describes the pre-CI
snapshot. Later documentation/metadata heads require their own regression.

The scope is the precise run-length-only information model. The window is the
current remaining block length followed by h−1 complete future block lengths
from the literal odd-only Syracuse map. Corrections are arbitrary real-valued
functions of that window, including unbounded corrections; hidden exit
valuations are not correction inputs. Failure includes equality. Source one
continues at the fixed point and zero is excluded. First take seed cutoff to
infinity at fixed h and correction, then take the infimum, then let h grow.

The infimum is defined from literal achieved densities, not from a presumed
symbolic law. The reused finite-depth population proofs establish each actual
density and its exact series representation. A first-future-maximum marker
provides the shrinking upper bound. Finite cyclic histories, exact block-to-seed
normalization and a rational second-moment bound provide the lower bound. No
infinite iid integer trajectory, correction integrability or Collatz convergence
assumption is used.

The optional stronger liminf target remains separate and is **not implemented
or claimed here**. No exact p_h for every depth, sharp leading constant,
existence of lim h*p_h, general full-pair information theorem or ordinary Collatz
convergence is claimed. Jake S. Brusca is the author; ChatGPT assisted with ideas,
proofs, code, writing and separate-context AI review. No human expert refereeing,
novelty certification or external acceptance is claimed.

The primary source is [Polson–Sokolov v1.4.0, O3′](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch11_open.tex),
label `prob:ch11:o3p`, with the [block convention](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch05c_mmcollatz.tex).
The interpretation and precise formal model require independent semantic review;
this package does not certify that broader readings of the source exercise have
been solved.

The self-contained [written reconstruction](RATE_PROOF.md) gives the literal
model, marker transport, exact normalization and Cantelli calculation.

## Frozen boundary and source coverage

Seven original files retain their exact canonical bytes: `Definitions.lean`,
`ExpectedTypes.lean`, `GeneralDefinitions.lean`, `GeneralExpectedTypes.lean`,
`RateDefinitions.lean`, `RateExpectedTypes.lean`, `RateChallenge.lean`.
Historical draft comments describe the preserved preimplementation stage.
`specification.json` pins them. `RateChallenge` contains exactly 11 isolated
designated holes and is never imported by an implementation. `RateSolution`
implements those same declarations. `RateOptionalChallenge` is excluded.

The 45 owned modules are explicit in `owned_modules.json`: 28 minimal population
foundations, two rate definition/type modules, and 15 rate proof modules. Their
canonical filenames and source bytes are unchanged. The new public `Audit`
adapter inventories every theorem, including generated helpers, and rejects
custom axioms or challenge imports. Only `propext`, `Quot.sound`,
`Classical.choice` are permitted.

## Reproduce

1. Install the official toolchain in `lean-toolchain`.
2. Run `lake resolve-deps` to prepare the exact public Git-pinned lockfile.
3. Fetch the official mathlib cache with `lake exe cache get`, passing the module
   names in `cache-imports.txt` as arguments.
4. On Linux run `python3 verify.py --mode full --report /tmp/rate-full.json`.
5. Run `python3 test_mutations.py --mode full --report /tmp/rate-controls.json`.

`--mode build` is explicitly lower assurance: it freshly builds all owned
sources and audits their complete theorem closures. `--toolchain DIR` selects
the official compiler. `--dependency-cache DIR` accepts a normal prepared
`.lake/packages` directory; alternatively `--mathlib-cache DIR` accepts the pinned
public mathlib checkout and its dependency cache. Verification never fetches
network dependencies, changes supplied caches or reuses own proof build outputs.
Missing dependencies/checkers, unsupported platforms and failed required gates
fail verification.

Full mode freshly compiles Audit and exports every inventoried own theorem/helper
root from its environment, which imports both GeneralSolution and RateSolution.
It then requires `lake check --from-export ... --paranoid` for the complete
source-bound closure and the trusted comparator on all 11 frozen RateChallenge
statements with every bundled checker and independent nanoda. Ordinary
compilation is not evidence that those gates ran.
