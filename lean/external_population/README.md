# Formal population densities at every fixed finite information depth

This standalone Lean 4.35.0/mathlib project contains complete source proofs for
all 22 frozen **finite-depth density and source-model targets** associated with
the run-length-only interpretation of Polson–Sokolov O3′. For each fixed positive
finite depth and every arbitrary real correction, it proves literal relative
odd-seed density existence and an exact summable symbolic representation.
It also proves exact compatibility with the full frozen depth-one correction
class. It does not optimize the higher-depth infimum, prove its limit or rate,
or prove Collatz convergence. Jake S. Brusca is the author; ChatGPT assisted
with ideas, proofs, code, writing and separate-context AI review. No human
expert refereeing, novelty certification or external acceptance is claimed.

**Assurance:** public preparation and build-mode checks supply ordinary
compilation and transitive axiom assurance only. Full source-bound export,
sandboxed replay, frozen-statement comparison and independent checker coverage
require actual successful Linux `--mode full` receipts for this project. No
receipt from the separate depth-one or prefix project substitutes for them.

## Exact source model

The literal map is accelerated odd-only Syracuse on positive odd integers.
A remaining block includes its first valuation-at-least-two stride. The
information window contains that current remaining length and the next h−1
complete block lengths obtained by actual iteration. Corrections are arbitrary
real functions of the entire window; no boundedness, regularity, additivity or
finite support is required. Hidden exit valuations refine the population event
but are never extra inputs to the correction. Failure includes equality;
source one continues at its literal fixed point. Zero is excluded.

The proof first realizes every prescribed finite block refinement as exactly
one dyadic residue class in the parameter x=2n+1. It proves the finite-product
geometric weights and their projection fibers. A finite-tail transfer gives
literal coarse-window densities; a second transfer uses the exact positive
logarithmic error and per-cell stabilization to give every failure density.
No countable-additivity rule for natural density or independence along a fixed
positive orbit is assumed. Depth h is fixed before the population limit.

The primary source is [Polson–Sokolov v1.4.0, O3′](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch11_open.tex),
label `prob:ch11:o3p`, with the [block convention](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch05c_mmcollatz.tex).
Exact source commit: `5840497a23fc0d64127b850aea68862d7c93f2b7`.

The five specification files retain their original frozen bytes:
`Definitions.lean`, `ExpectedTypes.lean`, `GeneralDefinitions.lean`,
`GeneralExpectedTypes.lean`, `GeneralChallenge.lean`. Historical draft comments
in those files describe the preserved preimplementation stage.
`specification.json` records all five hashes. `GeneralChallenge` contains
22 isolated designated holes and must never enter an accepted proof import.
`GeneralSolution` implements those same 22 declarations. No canonical
specification or proof module was renamed for this standalone project.

## Reproduce

The lockfile pins mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`
and all public Git dependencies. Dependency preparation is separate from proof
verification:

1. Install the official toolchain in `lean-toolchain`.
2. Run `lake resolve-deps` to materialize the locked public dependencies.
3. Fetch the official mathlib cache with `lake exe cache get`, passing the
   module names in `cache-imports.txt` as its arguments.
4. On Linux, run `python3 verify.py --mode full --report /tmp/population-full.json`.
5. Run `python3 test_mutations.py --mode full --report /tmp/population-controls.json`.

Local `--mode build` performs a fresh own-source build and exhaustive theorem
closure audit; it is explicitly lower assurance. `--toolchain DIR` selects an
official installation. `--dependency-cache DIR` accepts a prepared public
`.lake/packages`, or `--mathlib-cache DIR` a pinned public mathlib checkout
and its normal dependency cache. Sources and dependency Git pins are checked;
the verifier copies dependencies and never mutates the supplied caches.
Own proof build artifacts are never copied into the fresh project. Relative
links tracked within pinned packages are preserved only inside their package.
No private source, path dependency or credentials are required.

Full mode freshly exports all inventoried own theorem/helper roots from
`GeneralSolution`, including their transitive proof premises. It requires
sandboxed `lake check --from-export ... --paranoid`, then the trusted comparator
for all 22 frozen declarations with every bundled checker and independent
`nanoda`. Missing checkers, unsupported platforms and required command failures
fail the gate. Ordinary successful compilation does not imply those gates ran.

The self-contained [written reconstruction](GENERAL_DENSITY_PROOF.md) derives
the source model, residue compiler and both finite-tail transfers.

## Inspect

- `GeneralSolution.lean`: the 22 frozen target implementations.
- `GeneralPreimage.lean`, `GeneralStrideWords.lean`, `GeneralBlockWords.lean`:
  exact literal finite-word/cell residue compiler, including valuation one,
  empty words and terminal length one.
- `GeneralWeights.lean`, `GeneralMarginal.lean`: normalized finite-product
  geometric sums and exact hidden-exit marginalization.
- `GeneralRefinementLabels.lean`, `GeneralProjection.lean`: actual source
  partition binding and the first finite-tail transfer.
- `GeneralGains.lean`, `GeneralDensity.lean`: exact error, zero-gain boundary,
  per-cell stabilization and the second finite-tail transfer.
- `GeneralSourceDensity.lean`, `GeneralCompatibility.lean`: original cutoff
  convention and whole-class depth-one equivalence.
- `Audit.lean`, `inventory.json`: every own/reused theorem closure, generated
  helpers, exact target bodies and source/configuration digests. Only
  `propext`, `Quot.sound`, `Classical.choice` are permitted axioms.

The copied depth-one dependencies are explicitly allowlisted in
`owned_modules.json`; no unrelated depth-one optimization or numerical module
is required. Kernel assurance concerns the declared formal statements, and
still requires semantic scrutiny by qualified readers.
