# External problem candidates: M4, R8, R9 and O3′

Jake S. Brusca, 27 November 2026. ChatGPT assisted with the research,
proof drafts, code, writing and audit. This is a personal research project
and work in progress. Corrections and counterexamples are welcome.

**No solution of these four open problems is certified by this release.**
The project has written proof candidates. The public material here first
records their exact scope and provides reproducible finite foundations.
The full four-problem claims below remain unproved in Lean. The h=1 O3′ subquestion has a [complete frozen-target proof package](../../lean/external_analysis/README.md), with full independent checker CI passed at8524770. There has been no human expert refereeing. Neither
ordinary Collatz convergence nor global forced capture follows.

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

| Problem and primary source | Candidate contribution | Exact boundary | Release status |
| --- | --- | --- | --- |
| [M4, `prob:ch20:band`](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch10f_missed.tex), and [detailed `rrt:sec:m4`](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch10h_ratchets.tex) | Rung entropy limit, variational characterization and computability | The short statement asks for an unrestricted length limit; the detailed discussion uses ladder rungs. These must be treated separately. A certified entropy table is still required. | Draft candidate; unresolved source interpretation and assurance gates |
| [R8, `rrt:prob:r8`](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch10h_ratchets.tex) | Pressure convergence and differentiability for every nonnegative tilt along rungs | Critical differentiability is part of the problem. Convergence and finite-depth computations do not settle it. | Draft candidate; full critical argument and formal assurance pending |
| [R9, `rrt:prob:r9`](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch10h_ratchets.tex) | Near-maximal entropy asymptotic, with proposed leading coefficient `3/(2 ln 2 ln 10)` | First take the length limit along rungs at fixed threshold, then let the threshold tend to one. Finite counts do not certify either limit. | Draft candidate; analytic proof and full formalization pending |
| [O3′, `prob:ch11:o3p`](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch11_open.tex) | Arbitrary-correction density, inverse-depth rate, depth-one infimum/nonattainment and convergent finite optimization | Corrections may be unbounded real functions of the current remaining block and the next `h−1` complete blocks. Rate, algorithmic determination and closed forms are distinct claims. | All 14 h=1 targets formalized; full checker CI passed at8524770. All22 arbitrary finite-depth density targets passed full gates at8746e08; all 11 required rate targets passed full replay/comparison/six-checker and hostile controls at1406f1a |

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
`7/3`, while B₂=5/3. Thus both qualify at c=1. This refutes an unrestricted
length extension of c=1 uniqueness, **not** the existence of an asymptotic
limit. At rung lengths the maximal word is unique. The off-rung asymptotic
claim requires an additional proof and remains a candidate here.

## Syracuse finite-information model

For a positive odd seed use `S(x)=(3x+1)/2^v₂(3x+1)`. A block consists of
successive valuation-one strides and its first valuation-at-least-two
stride. Its remaining length is v₂(x+1). A depth-h potential is
`ln x + φ(r₀,…,r_(h−1))`, with arbitrary finite real values at every tuple.
Failure means nondecrease, including equality. At x=1 the map is fixed;
this singleton has zero odd-seed density.

The proposed depth-one infimum is the series

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
The arbitrary finite-depth density foundation passed full independent gates. Required rate proofs passed full independent gates at1406f1a; all15 finite-optimization source proofs are now included, with their separate independent assurance gates pending.
The [near-extremal entropy written draft](../arithmetic_bridge_pressure/README.md)
develops the rung/depth correspondence, large-tilt pressure, finite-block
matching lower bound and proposed R9 expansion. It also remains unformalized.

Run `python3 certificates/external_problems/verify.py` from the repository
root. Its JSON output states the finite domains and exact rational results.
It checks literal words, depth paths, small valuation cylinders, block
transitions, the series tail and deliberate model mutations. These are
finite certificates and model consistency tests.

For the remaining arbitrary-depth and bridge claims, required next gates are complete noncircular written proofs, separately
frozen full formal statements, proof of every model conversion and premise,
clean Lean builds and transitive axiom audits, fresh replay, trusted statement
comparison and independent checker replay. Numerical entropy claims need
rigorous rounding, tails and independent consumers. Review by separate AI
contexts has occurred; no qualified human review or author acknowledgment
is claimed. The [status register](status.json) keeps these fields separate.

The [population-density foundation](../../lean/external_population/README.md) now has complete source proofs for every fixed positive finite h and arbitrary real window corrections, including exact source binding and both finite-tail transfers. This22target package passed source build, all517closure audits, full source-bound replay/comparison, six checker modes and nine hostile controls at8746e08 ([receipts](../../verification/external_population/README.md)). Its companion written proof is self-contained in the public tree. No rate, optimum or full O3′ resolution follows from this foundation alone.

The [rate companion](../../lean/external_rate/RATE_PROOF.md) proves the explicit inverse-depth bounds and vanishing infimum, with all eleven required frozen statements implemented. All 765 theorem/helper closures, full replay/comparison, six checker modes and ten hostile controls passed at1406f1a ([receipts](../../verification/external_rate/README.md)). The optional stronger liminf and exact higher-depth optima are not claimed.
