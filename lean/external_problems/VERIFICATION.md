# Supporting proof reproduction

This project has five abstract integer prefix/depth theorems and 29 generated
theorem helpers. No real-valued pressure, entropy, density, or infimum theorem
is proved here. The separate inventory records elaborated types and transitive
axioms. The challenge holes are specification inputs and never imports of
`Solution` or `Audit`.

Use official Lean 4.35.0. There are no third-party packages. From the repository
root:

```sh
python3 lean/external_problems/verify.py --mode full --report /tmp/external-support.json
python3 lean/external_problems/test_mutations.py --mode full
```

Full mode requires Linux, bubblewrap, working user namespaces and the checkers
bundled with the pinned toolchain. It performs a clean build, inventories every
supporting theorem/helper, checks frozen statements and source hashes, then
runs `lake check --paranoid` and `lake comparator --paranoid` with the frozen
challenge and the nanoda checker enabled. A missing sandbox or rejected checker
is a failure. The challenge is built separately by the comparator.

On a host without Linux namespaces, `--mode build` explicitly reports partial
assurance; it cannot replace the mandatory CI `external-support` job. The
existing CI `evidence` job separately runs the complete legacy release gates.
Both jobs are required for this release's verification. Kernel validation and
AI statement inspection are not human peer review.

The frozen specification was written by a separate AI source/model reviewer
before the implementation. The implementation and audit were written by
another AI context. This separation is disclosed evidence, not an external
expert endorsement. Headline challenge/specifications for M4/R8/R9/O3′ remain
unwritten and unproved.
