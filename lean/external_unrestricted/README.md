# All-length fixed-reference c=1 source-word count

This standalone project concerns the explicit **all-length extension** of the source's positive ordered-word population at the fixed phase-zero reference B_r, for actual theta=log3/log2 and c=1. It does not refute the intended rung-only M4 question, address phase-adapted N*, or prove anything at c<1. It does not establish pressure/R8/R9, integer cycles or Collatz capture.

The proved statements give count>=2^floor(r/8) at large-defect lengths, count1 on unbounded actual strict rungs, bounded nonnegative normalized logarithmic counts, liminf0 and limsup>=(log2/log10)/8>0. Thus that exact all-length sequence has no real limit. See the self-contained [argument and23-target proof map](ARGUMENT.md).

The32 owned modules preserve canonical proof/spec bytes. Eight frozen files,23 proposition bodies and13 model bodies are pinned separately. The private fresh ordinary source integration passed504 theorem/helper closures with only propext, Quot.sound and Classical.choice. The public standalone build, source-bound replay, exact statement comparator, six checker modes and hostile controls have distinct reports: **full public assurance remains pending until actual source-pinned Linux receipts pass**. Successful compilation or this README is not independent kernel assurance or human expert refereeing.

## Reproduce

Install the pinned Lean4.35.0 toolchain. Fetch the exact public Git dependencies with Lake, then the official mathlib cache imports listed in `cache-imports.txt`. No private proof checkout or development build cache is a runtime dependency.

```sh
lake update
lake exe cache get $(cat cache-imports.txt)
python3 verify.py --mode build --report build.json
python3 verify.py --mode full --report full.json
python3 test_mutations.py --mode source --report source-controls.json
python3 -O test_mutations.py --mode source --report source-controls-optimized.json
python3 test_mutations.py --mode full --report full-controls.json
```

The lockfile pins all public Git revisions. Dependency fetching is preparation, not a verifier gate; `verify.py` never updates or downloads dependencies. With a prepared cache, supply exactly one of `--dependency-cache /path/to/.lake/packages` or `--mathlib-cache /path/to/pinned/mathlib` and optionally `--toolchain /path/to/lean4.35.0`. Every verification builds a fresh standalone source copy and materializes verified pinned dependencies. Full mode needs Linux sandbox support and fails closed on missing capabilities or any absent checker. Build mode is explicitly partial.

The full verifier exports every owned theorem/helper root, including generated helpers, and requires all six checker acceptances in both complete proof-closure replay and frozen-statement comparison. It compares all23 original proposition bodies and13 original model bodies, checks the complete owned-source inventory, and rejects every custom transitive axiom. The isolated `UnrestrictedChallenge.lean` is immutable trusted input and never an implementation import.

Portable mutation controls are source/hash/coverage checks, not theorem comparisons. Full semantic negatives first require the positive full23 pipeline. Reports retain exact source hashes and complete compressed command output. AI assisted the mathematics, implementation, documentation and reviews; overlapping authorship is disclosed. No human expert refereeing or novelty/priority acceptance is implied.
