# Finite source-word bridge foundations

This standalone Lean 4.35.0/mathlib project implements 25 frozen finite targets:
positive-letter/prefix encoding, strict-record rung arithmetic and unbounded
rungs, exact last-letter lowering, finite depth bridges, unchanged rewards,
finite threshold counts, and the unique mechanical maximum. It is supporting
finite mathematics for the bridge program. It proves no pressure or entropy
limit, differentiability theorem, M4 solution, R8 solution or R9 asymptotic.

**Source-pinned full assurance passed:** at commit `5369dc97e6b8d15d7b3ae437d320726f24f24aa7`, run `46105619785` passed all six mandatory jobs. This project's25 frozen targets and357 theorem/helper closures passed fresh proof export/replay, trusted statement comparison, all six checker modes at both stages and13 hostile controls. [Exact receipts](../../verification/external_bridge/README.md) identify the checked source/tree and36 project file digests. Later source or metadata changes require their own regression. No pressure or entropy limit follows from these finite results.

The slope is the actual theta=log(3)/log(2). A word has r ordered positive
integer letters and cumulative sums K_t. Its source endpoint is ceil(r*theta),
its interior caps are floor(t*theta+delta(r)), and its reward is exactly
sum_(t<r) 2^(K_t)/3^t. A strict rung compares the unnormalized upper ceiling
defect against positive earlier indices only. Slope bounds, irrationality,
positive-index nonintegrality and unbounded strict rungs are proved targets.

At a rung, interior caps equal floor(t*theta), but the original source depth
floor(r*theta)-K_r ends at **-1**. Lowering only the final letter by one produces
a positive-letter floor word and a zero-endpoint depth bridge. The proofs
establish that the final source letter is at least two before using natural
subtraction. The inverse raises that letter. Since rewards use t<r, every reward
term is unchanged. Explicit equivalences preserve finite threshold counts and
the unique maximum at the phase-zero reference B_r. Words and profiles have
finite domains; unconstrained infinite tails are never counted. Counts are of
ordered source words, with no quotient by cyclic rotations or assertion that
those words are integer Collatz cycles.

The primary source is [Polson–Sokolov v1.4.0, exact cycle notation and M4](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch10h_ratchets.tex),
labels `rrt:sec:exact` and `rrt:sec:m4`. At length one the source word (2) lowers
to (1), both rewards equal 1, and literal/transported closing depths are -1/0.
At length zero the word-admissibility populations are empty; the totalized
finite depth bridge is the sole zero profile. Off-rung floor/source population
equality is not asserted.

Jake S. Brusca is the author; ChatGPT assisted with ideas, proofs, code, writing
and separate-context AI review. No human expert refereeing, novelty certification
or external acceptance is claimed.

The self-contained [written proof](FINITE_BRIDGE_PROOF.md) develops the finite
dictionary, endpoint adjustment, reward identities and unique maximum.

## Frozen meanings and coverage

Six primitive/challenge files retain their exact canonical bytes:
`Definitions.lean`, `ExpectedTypes.lean`, `PrefixDefinitions.lean`,
`BridgeDefinitions.lean`, `BridgeExpectedTypes.lean`, `BridgeChallenge.lean`.
Historical draft comments are preserved inside those frozen bytes.
`specification.json` pins them. `frozen_propositions.json` preserves all 25 exact
elaborated V3 proposition bodies. `BridgeChallenge` contains the isolated
designated holes and is never imported by the implementation. `BridgeSolution`
implements the same 25 named declarations.

The 22 owned modules in `owned_modules.json` are the minimal reused population,
logarithm and approximation foundations, the source-rung arithmetic, the frozen
finite model and all finite proofs. Their canonical source bytes are unchanged.
`Audit.lean` checks all theorem closures, including generated helpers, rejects
own custom axioms and challenge imports, and matches the 25 frozen types. Only
`propext`, `Quot.sound` and `Classical.choice` are permitted axioms.

## Reproduce

1. Install the official toolchain named in `lean-toolchain`.
2. Run `lake resolve-deps` to prepare the exact public Git-pinned dependencies.
3. Fetch selected official mathlib caches with
   `xargs lake exe cache get < cache-imports.txt`.
4. On Linux run `python3 verify.py --mode full --report /tmp/bridge-full.json`.
5. Run `python3 test_mutations.py --mode full --report /tmp/bridge-controls.json`.

Dependency fetching is separate from verification. The verifier never updates
or downloads dependencies and never reuses own proof build outputs.
`--mode build` performs a fresh own-source build and complete axiom audit only.
`--toolchain DIR` selects the official compiler. `--dependency-cache DIR` accepts
a prepared `.lake/packages` directory; alternatively `--mathlib-cache DIR`
accepts the pinned public mathlib checkout and its normal dependency cache.
Supplied caches are copied without modification and their Git source pins are
checked. Missing dependencies, unsupported platforms, unavailable checkers and
failed gates fail verification.

Full mode exports every inventoried own theorem/helper root from a fresh Audit
environment, then requires `lake check --from-export ... --paranoid` and the
trusted comparator on all 25 frozen statements with every bundled checker and
independent nanoda. Both commands must explicitly report acceptance from Lean
default, Lean paranoid, lean4lean, nanoda, con-leche and con-ron. Compilation alone
does not show that those gates ran.
