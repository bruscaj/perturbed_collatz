# External problems: M4/R8/R9 candidates and the run-length-only O3′ answer

Jake S. Brusca, 28 November 2026. ChatGPT assisted with the research,
proof drafts, code, writing and audit. This is a personal research project
and work in progress. Corrections and counterexamples are welcome.

The run-length-only O3′ package now determines each finite-depth infimum by a total computable scheme of certified rational brackets, proves convergence to zero, and proves decay order 1/h. At depth one it additionally gives an exact series and nonattainment. These results address all three stated O3′ requests in the algorithmic sense, with source-pinned full independent machine-checker receipts. Closed formulas at every depth, sharp constants, practical numerical tables, novelty and independent human expert refereeing remain separate.

M4/R8/R9 pressure, entropy, computation and critical-regularity claims remain draft candidates. Neither ordinary Collatz convergence nor global forced capture follows. The finite supporting libraries do not discharge those analytic gaps.

The [O3′ source-to-result map](O3_SOURCE_MAP.md) records the exact class, the three source requests and the scope of algorithmic determination.

## Original statements and interpretation

The primary source is Nicholas G. Polson and Vadim Sokolov,
*On the Collatz Conjecture: Martingales, Momentum and Continued Fractions*,
edition 1, v1.4.0, commit
`5840497a23fc0d64127b850aea68862d7c93f2b7`.
The three target chapters match upstream main
`2874a312a871ce3eb2de4368d3f1d16dbae27b20` at the audit date.
The [authors' index](https://vsokolov.org/books/collatz/results.html)
listed all four as open on 27 November 2026. A targeted search found no
verified resolution; this is not an exhaustive prior-art review or a
claim of priority or external acceptance. We link the source rather than
redistribute its chapters.

| Problem and primary source | Contribution | Exact boundary | Release status |
| --- | --- | --- | --- |
| [M4, `prob:ch20:band`](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch10f_missed.tex), and [detailed `rrt:sec:m4`](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch10h_ratchets.tex) | Rung entropy limit, variational characterization and computability | The isolated wording does not specify a rung restriction; the continuation explicitly fixes rungs and asks for the limit along rungs. The all-length fixed-B_r c=1 extension is a separate question, not a refutation of intended rung-only M4 or phase-adapted N*. A certified rung entropy table is still required. | Draft candidate for the intended rung question; analytic proof and assurance remain pending |
| [R8, `rrt:prob:r8`](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch10h_ratchets.tex) | Pressure convergence and differentiability for every nonnegative tilt along rungs | Critical differentiability is part of the problem. Convergence and finite-depth computations do not settle it. | Draft candidate; full critical argument and formal assurance pending |
| [R9, `rrt:prob:r9`](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch10h_ratchets.tex) | Near-maximal entropy asymptotic, with proposed leading coefficient `3/(2 ln 2 ln 10)` | First take the length limit along rungs at fixed threshold, then let the threshold tend to one. Finite counts do not certify either limit. | Draft candidate; analytic proof and full formalization pending |
| [O3′, `prob:ch11:o3p`](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch11_open.tex) | Arbitrary-correction density, inverse-depth rate, depth-one infimum/nonattainment and convergent finite optimization | Corrections may be unbounded real functions of the current remaining block and the next `h−1` complete blocks. Rate, algorithmic determination and closed forms are distinct claims. | Depth-one, general density, rate and optimization packages passed full source-pinned gates. At b5dcda3, all 15 optimization targets/952 closures, six checker modes in both stages and 18 controls passed; all seven mandatory jobs passed. See [receipts](../../verification/external_optimization/README.md) |

The source distinction is specific: `ch10f_missed.tex:219` defines general admissibility and line246 counts general lengths, while its M4 status at line458 points to rung tables and R8. The continuation at `ch10h_ratchets.tex:441,510` explicitly restricts the M4 limit question to rungs; its line461 defines off-rung N* using a different phase-adapted threshold. These passages support treating the all-length fixed-reference result separately, without claiming that the authors intended an unrestricted limit or that their intended M4 problem is refuted.

## The literal word model

Put θ=log₂3, δ(r)=ceil(rθ)−rθ and s=ceil(rθ). A rung is a strict
lower record of δ at positive integer lengths. An admissible word has
positive integer letters, prefix sums K₀=0 and Kᵣ=s, and interior caps
Kₜ≤floor(tθ+δ(r)). Its reward is

`Φ = Σ_(0≤t<r) 2^K_t / 3^t`,

and the phase-zero reference is

`B_r = Σ_(0≤t<r) 2^floor(tθ) / 3^t`.

The threshold is `Φ ≥ c B_r`; the count entropy uses base-ten logarithms,
whereas pressure uses natural logarithms. On a rung the interior caps are
floor(tθ). The literal depth `floor(tθ)−K_t` ends at **−1**, not zero.
Replacing the final prefix by floor(rθ) gives the convenient zero-endpoint
model; this requires a bijection, including positivity of the last letter.
The abstract integer supporting lemma is distinct from proving that θ and
the source's rung predicate meet its hypotheses.

For general lengths the caps can be computed without logarithms:
`K_t ≤ floor(tθ+δ(r))` is equivalent to
`2^K_t 3^(r−t) ≤ 2^s`. These exact integer comparisons drive the literal
enumerator; its second implementation independently enumerates depth paths.

At r=2 there are two words `(1,3)` and `(2,2)`, with rewards `5/3` and
`7/3`, while B₂=5/3. Thus both qualify at c=1. This finite example by itself refutes only all-length c=1 uniqueness. The
separate [all-length package](../../lean/external_unrestricted/README.md) now
provides 23 formal source proofs of liminf 0 and limsup≥log10(2)/8 for the
fixed-B_r extension at c=1. Its full independent assurance passed at source739a4f5:23 targets,13 models,504 closures, six modes in both stages and21 controls ([receipts](../../verification/external_unrestricted/README.md)). The intended rung-only M4 remains open.
This distinction does not refute intended rung-only M4 or phase-adapted N*.

## Syracuse finite-information model

For a positive odd seed use `S(x)=(3x+1)/2^v₂(3x+1)`. A block consists of
successive valuation-one strides and its first valuation-at-least-two
stride. Its remaining length is v₂(x+1). A depth-h potential is
`ln x + φ(r₀,…,r_(h−1))`, with arbitrary finite real values at every tuple.
Failure means nondecrease, including equality. At x=1 the map is fixed;
this singleton has zero odd-seed density.

The depth-one infimum, proved separately in the analytic package, is the series

`A = Σ_(r≥1) 2^(−r) [1/2 − 2^(−floor(1+r log₂(3/2)))]`.

The released exact arithmetic encloses **this series**. Identifying it
with the infimum over every allowed correction and proving nonattainment
are separate infinite theorems, not certified by the enclosure. A finite
valuation law for populations of initial seeds does not assert independence
along one fixed integer's infinite orbit.

## Evidence and remaining work

The [depth-one Syracuse written draft](../finite_information_lyapunov/README.md)
provides proofs of density existence, the infimum formula and nonattainment.
All 14 frozen h=1 targets passed the dedicated full analytic assurance job at
`8524770` ([exact receipts](../../verification/external_analysis/README.md)).
The arbitrary finite-depth density foundation passed full independent gates. Required rate proofs passed full independent gates at1406f1a; all 15 finite-optimization targets passed their own full independent gates at b5dcda3.
The [near-extremal entropy written draft](../arithmetic_bridge_pressure/README.md)
develops the rung/depth correspondence, large-tilt pressure, finite-block
matching lower bound and proposed R9 expansion. It also remains unformalized.

Run `python3 certificates/external_problems/verify.py` from the repository
root. Its JSON output states the finite domains and exact rational results.
It checks literal words, depth paths, small valuation cylinders, block
transitions, the series tail and deliberate model mutations. These are
finite certificates and model consistency tests.

For the remaining M4/R8/R9 analytic claims, required next gates are complete noncircular written proofs, separately
frozen full formal statements, proof of every model conversion and premise,
clean Lean builds and transitive axiom audits, fresh replay, trusted statement
comparison and independent checker replay. Numerical entropy claims need
rigorous rounding, tails and independent consumers. Review by separate AI
contexts has occurred; no qualified human review or author acknowledgment
is claimed. The [status register](status.json) keeps these fields separate.

The [population-density foundation](../../lean/external_population/README.md) now has complete source proofs for every fixed positive finite h and arbitrary real window corrections, including exact source binding and both finite-tail transfers. This22target package passed source build, all517closure audits, full source-bound replay/comparison, six checker modes and nine hostile controls at8746e08 ([receipts](../../verification/external_population/README.md)). Its companion written proof is self-contained in the public tree. No rate, optimum or full O3′ resolution follows from this foundation alone.

The [rate companion](../../lean/external_rate/RATE_PROOF.md) proves the explicit inverse-depth bounds and vanishing infimum, with all eleven required frozen statements implemented. All 765 theorem/helper closures, full replay/comparison, six checker modes and ten hostile controls passed at1406f1a ([receipts](../../verification/external_rate/README.md)). The optional stronger liminf and closed-form higher-depth values are not claimed by the rate theorem. Uniform algorithmic determination of the actual higher-depth infima is supplied by the separate [optimization package](../../lean/external_optimization/README.md).
