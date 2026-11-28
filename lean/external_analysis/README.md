# Formal depth-one finite-information potentials

This standalone Lean 4.35.0/mathlib project contains complete source proofs for
all 14 frozen targets of the **depth-one subquestion** of Polson–Sokolov O3′.
It includes arbitrary-correction density existence, exact symbolic density,
the infimum series, its nonattainment, and an exact numerical enclosure.
It does not settle the arbitrary-depth O3′ problem, M4, R8, R9 or Collatz
convergence. Jake S. Brusca is the author; ChatGPT assisted with ideas, proofs,
code, writing and separate-context AI review. No human expert refereeing or
external acceptance is claimed.

**Current assurance:** a standalone public-source clean build succeeded.
Full source-bound replay, frozen-statement comparison and independent kernel
checking require successful `--mode full` receipts for this project. A supporting
prefix-project receipt does not certify these analytic proofs. Build mode is
explicitly lower assurance. See the repository's current status register for
actual final-head CI results.

## The exact model

The source map is the accelerated odd-only Syracuse map on positive odd
integers. The block length includes its first valuation-at-least-two stride.
A correction is an arbitrary function `Nat → Real`, with no boundedness or
regularity restriction. The value at zero is proved immaterial. Failure is a
non-strict potential increase; the fixed seed one is included. Densities are
relative natural densities of odd seeds, and the source's cutoff convention is
proved equivalent to sampling the first N odd seeds. The infimum is over
actual achieved literal densities.

`Definitions.lean`, `ExpectedTypes.lean` and `Challenge.lean` retain their
original frozen bytes. Historical draft comments in those files describe the
specification stage; they are preserved to keep the statement freeze exact.
The challenge's 14 designated `sorry` holes are **not proofs** and that module
must never be imported by an accepted implementation. `Solution.lean` supplies
the matching 14 proofs. `specification.json` records the original three hashes
and the primary source pin without private runtime dependencies.

The primary source is [Polson–Sokolov v1.4.0, open problems](https://github.com/VadimSokolov/collatz/blob/v1.4.0/book/chapters/ch11_open.tex),
label `prob:ch11:o3p`, commit `5840497a23fc0d64127b850aea68862d7c93f2b7`.
The corresponding [block convention](https://github.com/VadimSokolov/collatz/blob/v1.4.0/book/chapters/ch05c_mmcollatz.tex)
is separately pinned. Source matching does not establish priority or acceptance.

## Reproduce

The public lockfile pins mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` and every transitive dependency.
Keep dependency fetching separate from proof verification:

1. Install the official toolchain named in `lean-toolchain`.
2. Run `lake resolve-deps` to materialize the locked public dependencies.
3. Fetch the official mathlib cache for the module names in `cache-imports.txt`,
   using `lake exe cache get` with those names as arguments. The cache covers
   their transitive imports; no private source or credentials are needed.
4. Run `python3 verify.py --mode full --report /tmp/o3-h1-full.json` on Linux
   with the sandbox support and independent checker bundled with Lean 4.35.0.
5. Run `python3 test_mutations.py --mode full --report /tmp/o3-h1-mutations.json`.

For local development, `python3 verify.py --mode build` performs a clean own
source build and exhaustive axiom audit; it does not pass the full assurance
gate. `--toolchain DIR` selects an official installation. `--dependency-cache`
accepts a prepared public `.lake/packages` directory. `--mathlib-cache` accepts
a pinned public mathlib checkout containing its dependency cache. These are
verified optional cache inputs, not path dependencies in the public project.
The verifier materializes copies and does not mutate their sources. Relative
links belonging to pinned dependencies are preserved only within their package.
Lake's `allowNonModules` compatibility option preserves the exact frozen source
headers when importing mathlib's module-system libraries. It suppresses that
Lake compatibility advisory; Lean proof warnings remain errors.

Full mode freshly exports every audited own theorem and generated helper,
including all transitive proof premises, then runs sandboxed `lake check
--from-export ... --paranoid`. It also runs the trusted comparator for all 14
frozen targets with every bundled checker and the independently implemented
`nanoda` checker. Required failures, missing checkers, timeouts and unsupported
platforms fail the gate. The official comparator resolves the already pinned
and prepared workspace in its sandbox before proof execution; missing public
dependencies must be fetched during the preparation stage.

## What to inspect

- `Solution.lean`: all 14 frozen target declarations.
- `inventory.json`: exact elaborated target types, permitted axiom closures,
  every own helper theorem and source/configuration digests.
- `CountablePartition.lean`, `PartitionGeneral.lean`: finite-tail density transfer;
  no countable-union density assumption or common stabilization threshold.
- `Cylinders.lean`, `ExitCylinders.lean`, `PopulationLabels.lean`: exact literal
  seed classes and their unconditional densities.
- `DepthOneLower.lean`, `DepthOneUpper.lean`, `DepthOneFormula.lean`,
  `DepthOneNonattainment.lean`: the actual-density infimum and strictness.
- `DepthOneNumerics.lean`, `NumericInfimum.lean`: rational floor certificates,
  the partial sum and a proven enclosure of width `2^-81` for the actual infimum.
- `Audit.lean`: every own theorem closure, including generated helpers. The
  permitted axioms are only `propext`, `Quot.sound`, `Classical.choice`.

The formal statement still requires semantic review by qualified readers.
Kernel checking establishes the specified theorem in the declared foundations;
it does not supply human peer review, a novelty assessment or a theorem for
larger information depth.
