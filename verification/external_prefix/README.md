# Supporting proof checker receipts

The [successful CI run](https://github.com/bruscaj/perturbed_collatz/actions/runs/46087579687)
checked public commit `ff0c0de65866f05f0c70d3b5699a57640951b0ae`, tree
`2954655dcb1f8ed1321f96302f46e0a84b30faa2`. These are original downloaded
machine receipts; later documentation commits do not change the source identity
recorded in them. Verify the recorded component hashes before applying a receipt
to another tree. The latest final-head CI remains a separate gate.

All five abstract integer prefix/depth theorem statements and all 29 generated
theorem helpers were freshly built, audited and exported with their full proof
dependencies. Sandboxed replay accepted the 1,758-declaration closure; trusted
challenge comparison checked the matching statements with the required primitive
definitions. Lean's kernel, its paranoid checker, lean4lean, nanoda, con-leche and
con-ron accepted the relevant exports. Only `propext`, `Quot.sound` and
`Classical.choice` occur in the checked dependencies.

The negative controls rejected changed trusted definitions, a missing module,
a theorem weakened to `True`, and a hidden imported custom axiom. Positive full
verification ran before negative controls, so sandbox failure could not count
as a successful rejection. Exact commands, exit statuses and output are in
`external-support.json` and `external-mutations.json`; finite evidence is in
`external-finite.json` and the source/tree pin in `external-source-tree.txt`.

This is verification of the five supporting statements. It does not cover the
legacy projects, any real logarithmic-slope instantiation, pressure/entropy,
Syracuse density/infimum, or M4/R8/R9/O3′ headline claims. It supplies no human
expert refereeing or literature acceptance. The full-environment attempts that
ended in runner shutdowns are not successful checks. Frozen Std definitions
were retained; no statement or axiom policy was weakened to obtain this pass.
