# Literal density representation at every fixed finite information depth

Written mathematical reconstruction, 2026-11-28 UTC, matching all 22 frozen
population-density targets in [GeneralExpectedTypes.lean](GeneralExpectedTypes.lean)
and their implementations in [GeneralSolution.lean](GeneralSolution.lean).
Jake S. Brusca is the author; ChatGPT assisted with the mathematics, proofs,
code, writing and separate-context AI review. This is a personal research
project and work in progress. No human expert refereeing, priority certification
or external acceptance is claimed. Compiler, replay and independent-checker
assurance are governed by the exact separate project receipts described in
[README.md](README.md). This writeup does not substitute for those gates.
The geometric helpers and the arithmetic/density implementations were developed
in different AI contexts; this is not wholly separate authorship of every
checked component.

The source is Polson–Sokolov, edition 1, v1.4.0, commit
`5840497a23fc0d64127b850aea68862d7c93f2b7`,
[`ch11_open.tex`, O3′](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch11_open.tex),
label `prob:ch11:o3p`, with the block convention in
[`ch05c_mmcollatz.tex`](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch05c_mmcollatz.tex),
`prop:ch5c:block` and the final depth-two exercise. The information model
here reads run lengths only. It does not give exit valuations to a correction.
The source's general-depth optimization, limit and rate remain separate
questions; this document proves the density representation foundation.

## 1. Literal finite windows and the statement

For a positive odd integer x, define

\[
 K(x)=v_2(3x+1),\qquad S(x)=(3x+1)/2^{K(x)},\qquad R(x)=v_2(x+1).
\]

These are the unchanged frozen h=1 arithmetic definitions. The divisions are
exact; S(x) is again positive odd. Let `B(x)=S^{R(x)}(x)` be the next block
seed, including the exit stride. For any positive finite integer h, define

\[
 W_h(x)=(R(x),R(Bx),\ldots,R(B^{h-1}x))\in\mathbb N_{\ge1}^{,h}.
\]

The first entry is the current **remaining** block length. Later entries
are the complete future blocks beginning after the intervening exits.
Fix an entirely arbitrary function
\(\varphi:\mathbb N_{\ge1}^{,h}\to\mathbb R\), and put
\(V_\varphi(x)=\log x+\varphi(W_h(x))\). Failure means
\(V_\varphi(Sx)\ge V_\varphi(x)\), including equality. We count failures
among x=2n+1, 0≤n<N, divide by N and let N tend to infinity with h and φ
fixed. No boundedness, additivity, finite support or regularity condition is
imposed on φ.

The formal domain is all vectors of h natural numbers. Every actual vector
is positive; any function on positive vectors extends arbitrarily to the
other vectors, and two extensions agreeing on positive vectors have the
same source failures. This is harmless totalization, not a restriction.

There are two types of coarse edge:

- Ascending: `(r,s₂,…,s_h)` with r≥2 and all s_i≥1. The successor window is
  `(r−1,s₂,…,s_h)`. Its mass and limiting gain are
  \[
  w_A=2^{-(r+s_2+\cdots+s_h)},\quad
  g_A=\log(3/2)+\varphi(r-1,s_2,\ldots,s_h)
                    -\varphi(r,s_2,\ldots,s_h).
  \]
- Exit: k≥2 and successor window `(s₁,…,s_h)`. The old window is
  `(1,s₁,…,s_{h−1})`. Its mass and limiting gain are
  \[
  w_E=2^{-(k+s_1+\cdots+s_h)},\quad
  g_E=\log3-k\log2+\varphi(s_1,\ldots,s_h)
                    -\varphi(1,s_1,\ldots,s_{h-1}).
  \]

Offsets in the formal `Edge h` encode exactly these positive parameter
ranges. In particular the newly exposed s_h is available only to the new
correction. The exit k is part of the event label and gain, never extra
information passed to φ.

We will prove that every failure density exists and equals

\[
 d_h(\varphi)=\sum_{A}w_A\mathbf1_{g_A\ge0}
                +\sum_{E}w_E\mathbf1_{g_E\ge0}. \tag{1}
\]

The combined masses are positive, summable and total one, so the selected
series converges and belongs to [0,1]. No statement about the optimum of
(1) or its variation with h is asserted.

## 2. Actual blocks, transport and source boundaries

Write x=2^r q−1 with q positive odd and r=R(x)≥1. For 0≤i≤r−1 the within-run
states are

\[
 x_i=3^i2^{r-i}q-1.
\]

For i<r−1, the number `3x_i+1` has exactly one factor of two, and its odd
quotient is x_{i+1}. At i=r−1,
`3x_i+1=2(3^r q−1)` has at least two factors of two. Thus the remaining block
has exactly r−1 valuation-one strides and then one exit of valuation ≥2.
Every iterate in this finite construction remains positive odd. Iterating
the block map any finite number of times therefore needs no termination
theorem for the whole orbit.

For r≥2, the first stride decreases R by one and leaves the next block seed
unchanged. Consequently it changes only the head of W_h. For r=1, B(x)=S(x),
so the block sequence shifts exactly once. This proves both window
transport laws and all window positivity assertions used above.

At x=1, S(1)=1, R(1)=1 and every future block is again one. Hence every
correction fails there by equality. The literal map is continued, not
artificially stopped. Zero and other nonsource inputs are excluded from
the failure predicate. These conventions also make correction values on
invalid vectors irrelevant at both source and successor evaluations.

These are `BlocksWellDefined`, `WindowValidity`, `WindowTransport`,
`CorrectionRestriction` and `FixedPointAndZero`; see [GeneralArithmetic.lean](GeneralArithmetic.lean).

## 3. A single-stride preimage of every dyadic cylinder

Use the odd-seed parameter x=2n+1. For integers k≥1, e≥0 and 0≤d<2^e,

\[
\begin{split}
 &\exists m\ge0:\ K(2n+1)=k,\ S(2n+1)=2m+1,\ m\equiv d\pmod{2^e}\\
 &\quad\Longleftrightarrow\quad
 3n+2\equiv2^{k-1}(2d+1)\pmod{2^{k+e}}. \tag{2}
\end{split}
\]

For the forward implication, exact valuation and division give
`3n+2=2^{k−1}(2m+1)`. Substitute `m=d+2^e q` to get (2). The right side
`2^{k−1}(2d+1)` lies strictly between zero and `2^{k+e}`.

Conversely, let q be the quotient of `3n+2` by `2^{k+e}`. The congruence,
using its normalized remainder, gives

    3n+2 = 2^(k−1)(2d+1) + 2^(k+e)q.

Set `m=d+2^e q`. Then `3(2n+1)+1=2^k(2m+1)`. Its residual factor is odd,
so its valuation is exactly k, its literal stride is 2m+1, and m has the
required remainder. There is no assumed inverse integer orbit.

Multiplication by three is invertible modulo every power of two. Therefore
the affine congruence on the right of (2) selects one unique normalized
residue n modulo `2^{k+e}`. For a positive exponent one can solve with the
inverse of three applied to `C+2^{k+e}−2`, avoiding an unjustified natural
subtraction `C−2`. Target C=1 is permitted. The auxiliary modulus-one case
has C=0 and the sole normalized representative zero.

The case k=1 is essential, not an excluded exit case. With e=0,d=0,
condition (2) becomes `(3n+2) mod 2=1`, exactly the valuation-one class.
All uses of k−1 are guarded by k≥1. This is [GeneralPreimage.lean](GeneralPreimage.lean).

## 4. Finite valuation words with a terminal remaining length

For a finite positive word \(\mathbf k=(k_0,\ldots,k_{T-1})\), let its
word event require these exact consecutive literal stride valuations and
then terminal block length r≥1. This is `StrideWordCell r ks x`.

For the empty word, writing x=2n+1 gives

\[
 R(2n+1)=r\quad\Longleftrightarrow\quad
 n\equiv2^{r-1}-1\pmod{2^r}. \tag{3}
\]

Indeed `x+1=2(n+1)` has valuation r exactly when
`n+1=2^{r−1}(2q+1)`. The positivity r≥1 justifies undoing the subtraction.
At r=1, (3) is n even and includes source seed one.

Inductively take the unique terminal/tail word class and pull it back using
(2) for the first valuation. Each prescribed valuation k increases the
modulus exponent by k. It follows that the full word event is exactly one
normalized class in n modulo

\[
 2^{,k_0+\cdots+k_{T-1}+r}. \tag{4}
\]

Both directions retain the actual literal endpoint of every stride. To
prove uniqueness, insert a competing normalized representative as its own
seed parameter. It belongs to its own class, hence by the exact event
equivalence belongs to the constructed class; both normalized remainders
must be equal. This is uniqueness of the class, not of a seed or orbit.
In particular the residue's own seed realizes the prescribed finite event.
See [GeneralStrideWords.lean](GeneralStrideWords.lean).

## 5. Compile the exact finite block refinements

Prescribe m completed blocks with positive lengths ℓ₀,…,ℓ_{m−1}, exits
κ₀,…,κ_{m−1}≥2, and one terminal remaining length ℓ_m≥1. Compile the
chronological valuation word

\[
 (\underbrace{1,\ldots,1}_{\ell_0-1},\kappa_0,
  \underbrace{1,\ldots,1}_{\ell_1-1},\kappa_1,\ldots,
  \underbrace{1,\ldots,1}_{\ell_{m-1}-1},\kappa_{m-1}).
\]

The first-exit characterization in Section 2 proves the converse as well:
ℓ−1 valuation-one strides followed by a valuation ≥2 force the actual
remaining length to be ℓ. Thus this word event plus terminal ℓ_m is
**equivalent** to the frozen `RefinedCell`, with its actual repeated block
seeds. For ℓ=1 the ones prefix is empty and the exit is at the current
state. The state after that exit is `S^[ℓ] x=B(x)`, not the pre-exit state.
For m=0 the word is empty and only (3) remains.

Its exponent in (4) is exactly

\[
 E=\sum_{i<m}(\ell_i-1+\kappa_i)+\ell_m. \tag{5}
\]

Consequently each valid finite block datum is one unique normalized class
modulo 2^E in the **odd-seed parameter n**, with no feasibility or population
premise. This proves frozen `RefinedCylinderClasses`; see
`GeneralBlockWords.refinedCell_iff_word` and `refined_cylinder_classes`.

A class d modulo M>0 contains exactly
`floor((N+M−1−d)/M)` representatives among 0≤n<N. Its count differs from
N/M by at most one. Dividing by N proves the actual relative odd natural
density `1/M`. With M=2^E this proves `RefinedCylinderDensities` with mass
2^-E, not half that value. See [GeneralCylinderDensity.lean](GeneralCylinderDensity.lean) and the reused
exact progression-count lemmas.

## 6. Normalized masses and source labels

The refined weight factors as

\[
 2^{-E}=\left(\prod_{i=0}^{m}2^{-\ell_i}\right)
          \left(\prod_{i=0}^{m-1}2^{-(\kappa_i-1)}\right). \tag{6}
\]

Every factor has geometric sum one over its prescribed range. Finite
products of these nonnegative summable families are summable, by induction
using the product-index sum theorem; their sums are the products of their
sums. Hence all refined weights are positive and sum to one for every m.
This is an algebraic geometric identity, not an assumed iid population
law. [GeneralWeights.lean](GeneralWeights.lean) supplies `RefinedWeightLaw`.

The offset `refinedLabel m n` records exactly the actual ℓ_i−1 and κ_i−2.
The positivity/exit bounds of Section 2 undo these natural subtractions.
Conversely matching a decoded cell recovers every original offset.
This proves `RefinedLabelCell`, a disjoint exhaustive partition of actual
launch indices; see [GeneralRefinementLabels.lean](GeneralRefinementLabels.lean).

For depth h use m=h. On an ascending cell the projection keeps ℓ₀,…,ℓ_{h−1}
with ℓ₀≥2, sums all h hidden exits and the unused terminal length ℓ_h, and
thus has geometric mass `2^-(ℓ₀+…+ℓ_{h−1})`. On an exit it keeps κ₀=k and
ℓ₁,…,ℓ_h, fixes ℓ₀=1 and sums κ₁,…,κ_{h−1}. Formula (6) gives mass

    2^-1 · 2^-(k−1) · product(2^-ℓ_i, i=1,…,h)
      = 2^-(k+ℓ₁+…+ℓ_h).

The offset projection is exactly the actual coarse label, by the two
window transport laws. These give `RefinementProjectionLaw` and
`CoarseMarginalLaw`; the latter is a sum over finite-data indices, not an
inference about countable unions of integer sets. The coarse ascending
masses total 1/2, since their first length starts at two, and the exit
masses total 1/2, since k starts at two. Thus `WeightLaw` holds.

The formal geometric factorization and fiber proofs are in [GeneralWeights.lean](GeneralWeights.lean)
and [GeneralMarginal.lean](GeneralMarginal.lean). The source-label binding is independently supplied
by [GeneralRefinementLabels.lean](GeneralRefinementLabels.lean).

## 7. The finite-tail transfer, applied first to coarse labels

Here is the elementary transfer principle used twice. Let a total actual
label function partition the population indices. Suppose its coordinate
frequencies converge to nonnegative summable masses w_i with sum one.
Let P be an event whose decision on each label i eventually agrees with a
fixed Boolean b_i; each label may have its own threshold.

For every finite label set F and every N≥1, direct disjoint counting gives

\[
 \sum_{i\in F}\operatorname{freq}_N(i\cap P)
 \le \operatorname{freq}_N(P)
 \le \sum_{i\in F}\operatorname{freq}_N(i\cap P)
                +1-\sum_{i\in F}\operatorname{freq}_N(i). \tag{7}
\]

For fixed i, eventual agreement changes only a finite prefix, whose
frequency tends to zero. Hence the selected coordinate limit is
`v_i=w_i 1_{b_i}`. For fixed finite F, both sums in (7) converge. Now choose
F with omitted mass `1−Σ_F w_i<ε`; positivity also bounds the omitted
selected mass by ε. Inequality (7) then traps the full frequency within an
error tending to at most ε of `Σ_i v_i`. Let ε decrease to zero. This proves
its limit without countable additivity of natural density and without a
uniform threshold over infinitely many labels.

For the **first** application, the labels are the exact refined labels of
Section 6, and the event is that their projection equals a chosen coarse
edge e. Its decision is exactly constant on each refined label, with
threshold zero. Sections 5–6 supply actual coordinate limits and normalized
weights. The limit is the geometric fiber sum, already identified with w_e.
Thus every actual coarse label has precisely its declared natural density.
This is `CoordinateLaw`, implemented by [GeneralProjection.lean](GeneralProjection.lean) and assembled
without remaining hypotheses in `GeneralDensity.coordinate_law`.

Every coarse edge is realized: otherwise its literal frequency would be
identically zero, contradicting this limit and its strictly positive mass.
This is `LabelRealizable`. Coarse cells need not individually be one
residue class; the first transfer is what accounts for their hidden exits.

## 8. Exact gain and the second finite-tail transfer

Exact division and positivity give, for every source seed x,

\[
 \log S(x)-\log x
   =\log3-K(x)\log2+\epsilon(x),\qquad
 \epsilon(x)=\log\left(1+\frac1{3x}\right)>0. \tag{8}
\]

Moreover ε(x) tends to zero as x tends to infinity. The window transports
in Section 2 and exact offset decoding show that the full potential
increment is the declared coarse gain g_e plus precisely ε(x). This is
`LiteralGainIdentity`, proved in [GeneralGains.lean](GeneralGains.lean) from the literal logarithmic
identity and actual window transport, not from a model expectation.

For any fixed h, φ and e, g_e is a fixed real number even if φ is unbounded
over all windows. If g_e≥0, the increment is nonnegative at every source
seed in that cell. If g_e<0, then eventually ε(2n+1)<−g_e, so the increment
is negative on that cell. Therefore there is a threshold M depending on
h, φ and e after which literal failure on that cell is exactly `g_e≥0`.
This is `CellStabilization`. In particular **zero gain is failure**, because
the actual correction ε is positive. There is no uniform cutoff over e or
over φ. At source one the negative gain log(3/4) and positive error
log(4/3) cancel; that finite initial exception is permitted.

For the **second** application of Section 7, use actual coarse labels,
literal failure P, the decision `g_e≥0`, the already proved coordinate law,
and the normalized coarse masses. The per-cell stabilization just proved
provides exactly the remaining hypothesis. Hence the literal failure
frequency converges to (1).

Selected masses are nonnegative and bounded termwise by w_e, so they are
summable and their total lies in [0,1]. This proves `SelectedMassSummable`,
`DensityEqualsSymbolic` and `DensityExists`. The first two finite-tail
applications cannot be replaced by an informal countable-additivity step:
the refined-to-coarse law and the coarse-to-failure law are separately
bound to actual finite populations.

## 9. Uniqueness and the original odd-integer cutoff

Limits of real sequences are unique, proving `DensityUnique`. Directly,
all finite failure frequencies lie in [0,1], also confirming those bounds
for every achieved density.

The positive odd integers ≤X are precisely
`2n+1` with `0≤n<floor((X+1)/2)`. The map n↦2n+1 is injective and the
literal failure predicate already excludes nonsource inputs. Thus the two
finite frequencies satisfy the exact identity

\[
 \operatorname{sourceFrequency}(X)
 =\operatorname{failureFrequency}\left(\left\lfloor\frac{X+1}{2}\right\rfloor\right).
\]

The cutoff tends to infinity with X, giving one implication of source
density equivalence. Conversely evaluate the source sequence at X=2N;
then the cutoff is exactly N, so its convergence implies convergence of
the first-N-odds sequence to the same value. Both directions hold even with
the finite N=0 convention. This is `SourceDensityEquivalence`; see
[GeneralSourceDensity.lean](GeneralSourceDensity.lean).

## 10. Exact compatibility with the whole frozen h=1 class

A one-coordinate natural window is canonically equivalent to a natural
number r, by evaluation at its unique coordinate and the inverse constant
window. Precomposition therefore gives mutually inverse maps between
**all** scalar corrections `Nat→Real` and **all** one-window corrections,
including the unused value at zero. This is an equality of whole classes,
not just compatibility for linear or bounded examples.

For a lifted scalar correction the literal potential is identical at every
x, and hence so are every failure predicate, every first-N-odds frequency
and every odd-≤X frequency. On the ascending edge the one-coordinate formula
is `log(3/2)+φ(r−1)−φ(r)` with weight 2^-r; on an exit it is
`log3−k log2+φ(s)−φ(1)` with weight 2^-(k+s). Evaluation at the single
coordinate is a bijection of the full edge index sets, preserving both
gain decisions and weights. Reindexing the summable selected series gives
exactly the frozen h=1 symbolic formula. This proves all conjuncts of
`DepthOneCompatibility`; see [GeneralCompatibility.lean](GeneralCompatibility.lean).

## Scope and complete target coverage

Sections 2, 5–10 cover all 22 frozen target bodies: the five arithmetic/domain
targets; refined class, density, label, weight and projection laws; geometric
coarse marginal and weight laws; actual coordinate law and realization;
literal gain and per-cell stabilization; selected summability; density
existence, exact symbolic law and uniqueness; source-cutoff equivalence;
and full-class h=1 compatibility. The proof order does not assume any of
these desired density laws as global hypotheses: the conditional transfer
helper is instantiated with the earlier proved components.

The logical order is `∀ fixed positive finite h, ∀ arbitrary φ, limit as N→∞`.
This supplies no uniformity in h, no formula or bound for the optimized
general-depth infimum, no limit or rate as h→∞, and no statement of
Collatz convergence. The written argument and its finite arithmetic checks
also do not replace exact source-bound compiler, axiom, replay or checker
receipts. The semantic division, exact frozen-source digests and the current assurance
scope are recorded in [specification.json](specification.json) and
[inventory.json](inventory.json).
