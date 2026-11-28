# Certified finite optimization for the literal O3′ density infimum

This is a mathematical reconstruction of all **15 required frozen optimization targets**, with the executable program and its correctness argument included. The statements are those in [OptimizationExpectedTypes.lean](OptimizationExpectedTypes.lean) and [OptimizationAlgorithmTypes.lean](OptimizationAlgorithmTypes.lean), recorded by [specification.json](specification.json) and [frozen proposition register](frozen_propositions.json). Historical “UNFROZEN” comments inside those canonical files were preserved by the freeze; they do not authorize changing the statements. The optional `MonotonicFiniteOptimum` is not among the fifteen claims proved here.

This companion is a written reconstruction, not an independent assurance receipt. A fresh all-fifteen ordinary Lean integration passed: 51 commands, all 15 frozen raw-proposition comparisons, and 952 transitive declaration-closure audits allowing only `propext`, `Quot.sound` and `Classical.choice`. This is lower assurance than the project-specific public full gate. Independent statement comparison, source-bound replay, six checker modes and hostile controls remain pending until successful public receipts are available. The standalone verifier and exact source inventory are provided in this directory. The author implemented several of these modules and earlier density/rate helpers, so this is not independent human or expert refereeing. Earlier exploratory arguments and tests predated the frozen specification; their existence is not retroactively an independent acceptance event. No publication-priority claim is made.

## 1. Source and attribution

The external problem is Polson–Sokolov, *Collatz*, edition 1, v1.4.0, `prob:ch11:o3p`, [ch11_open.tex at commit 5840497a23fc0d64127b850aea68862d7c93f2b7](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch11_open.tex). The correction reads run lengths only. Exit valuations are labels determining edge gains and weights; they are **not extra information supplied to the correction**.

The source book already gives the strict finite potential/cycle criterion in Theorem 6.3, `thm:ch5c:residue`, [ch05c_mmcollatz.tex, lines 92–126](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch05c_mmcollatz.tex#L92-L126). Its sufficiency argument shifts gains by a positive margin and maximizes outgoing path gain. That chapter’s pinned Git blob is `98db4e67810a1f093055c47812055be4c789df03`, SHA256 `ecd0bc8eb5f44e7b173bc9e4a821b64986d590b308e027c8f537c5b00ee62d89`. The generic criterion below is therefore not presented as new. Our formal proof handles arbitrary real gains, labelled parallel edges, loops, strict inequalities and weighted deletion costs in its stated interface.

For algorithmic context, Göke, Mendoza Cadena and Mnich, [*Resolving Infeasibility of Linear Systems: A Parameterized Approach*, IPEC 2019, Theorem 12, pp.17:8–17:9](https://doi.org/10.4230/LIPIcs.IPEC.2019.17), relates difference-constraint feasibility blockers to negative-cycle arc deletion. Its rational, nonstrict, cardinality-budget setting does not replace our strict-real and arbitrary nonnegative-cost proof. Karp’s [original minimum-cycle-mean report, Theorem 1 and final recurrence](https://www2.eecs.berkeley.edu/Pubs/TechRpts/1977/Archive/ERL-m-77-47.pdf) supplies classical cycle/path context. The program here is an exhaustive finite search; it does not implement or inherit those papers’ efficient algorithms. The cited original statements have the distinct scopes just described.

## 2. Literal source model and the density theorem being used

Fix an integer depth h≥1. On positive odd integers let

\[
 S(x)=\frac{3x+1}{2^{K(x)}},\qquad K(x)=v_2(3x+1).
\]

The current remaining block length is r₀=v₂(x+1). A block has r₀−1 strides with K=1, followed by one exit stride with K≥2. The next block lengths are obtained along the actual orbit, including continuation through x=1. Let w_h(x)=(r₀,…,r_{h−1}). Every finite-valued real function φ on positive h-tuples is allowed; no boundedness, continuity, growth or integrability restriction is imposed. The frozen type also gives φ values on tuples containing zero, which never occur as source windows and may be filled arbitrarily.

Set

\[
 V_\phi(x)=\log x+\phi(w_h(x)).
\]

Failure means Vφ(S(x))≥Vφ(x), including equality. Its literal relative-odd density is

\[
 d_h(\phi)=\lim_{N\to\infty}\frac1N
 \#\{0\le n<N:V_\phi(S(2n+1))\ge V_\phi(2n+1)\}.
\]

The actual achieved-density infimum is

\[
 p_h=\inf\{d:\exists\phi\ \operatorname{HasFailureDensity}(h,\phi,d)\}.
\]

This is `ExternalO3RateDraft.failureInfimum`, not a definition by a symbolic series.

We use the previously proved general-density theorem, whose complete cylinder argument is documented in [GENERAL_DENSITY_PROOF.md](../external_population/GENERAL_DENSITY_PROOF.md). Its exact content needed here is as follows. There are two countable families of symbolic edges:

1. **Ascending:** a positive window s=(s₀,…,s_{h−1}) with s₀≥2 gives s→(s₀−1,s₁,…,s_{h−1}), base gain log3−log2 and mass 2^{−Σsᵢ}.
2. **Exit:** K≥2 and a positive destination window s give (1,s₀,…,s_{h−2})→s, base gain log3−K log2 and mass 2^{−K−Σsᵢ}. For h=1 the source is simply (1).

Distinct K remain distinct parallel edge labels even when their endpoints coincide. Write gφ(e)=b(e)+φ(target e)−φ(source e), and w(e) for the mass. Then the label masses are summable, Σₑw(e)=1, and for every arbitrary φ the literal density exists and

\[
 d_h(\phi)=\sum_e w(e)\,\mathbf1_{g_\phi(e)\ge0}. \tag{2.1}
\]

Here is why this result applies without any regularity assumption on φ. A prescribed finite valuation word, with a terminal remaining block length, is one exact dyadic residue class: multiplication by the odd affine coefficient is invertible modulo the relevant power of two. Its relative-odd density is the reciprocal of that modulus. A refinement recording complete block lengths ℓᵢ, exits Kᵢ, and terminal length r has exponent Σᵢ(ℓᵢ−1+Kᵢ)+r. Summing the exits uses Σ_{K≥2}2^{−(K−1)}=1 and gives the two masses above. Finite geometric tails control the refinement complement; thus this computation is a natural-density theorem, not an independence assumption about actual integer trajectories.

On each fixed label, the exact increment is

\[
 V_\phi(S(x))-V_\phi(x)=g_\phi(e)+\log(1+1/(3x)).
\]

The last term is positive and tends to zero. Hence gφ(e)≥0 always fails on that label; if gφ(e)<0 only finitely many seeds on it fail. Choose finitely many labels whose masses sum to more than 1−ε. Because they form a finite partition fragment, its complement has upper density at most ε. Stabilization on these finitely many labels squeezes the full failure frequency between the selected mass and that mass plus ε, proving (2.1). There is no uniform threshold over all labels or all φ. The seed x=1 always fails but has density zero. In particular equality is never discarded by replacing ≥0 with >0.

The total mass also follows directly: ascending mass is (Σ_{r≥2}2^{−r})(Σ_{r≥1}2^{−r})^{h−1}=1/2, and exit mass is (Σ_{K≥2}2^{−K})(Σ_{r≥1}2^{−r})^h=1/2. Therefore all selected series are summable by domination, 0≤d_h(φ)≤1, and the achieved set is nonempty and bounded below. This justifies all real infima used later. The imported theorem is proved for this literal model before optimization; no optimizer conclusion is a premise of it.

## 3. Generic finite multigraphs: strict cycle feasibility

Let V and E be finite types. Each edge e has a source u, target v, real base gain bₑ, and nonnegative cost wₑ. The endpoints need not identify an edge: parallel labels are retained. A cycle is a closed walk of **positive** length t; vertices and edges may repeat. Its base gain is B(C)=Σ_{e in C}bₑ, counting occurrences. A self-loop is a legitimate length-one cycle; an empty walk is not a cycle.

For a deletion set D⊆E, strict feasibility means that some ψ:V→ℝ satisfies

\[
 b_e+\psi(v)-\psi(u)<0\quad(e\notin D). \tag{3.1}
\]

Cycle safety means B(C)<0 for every cycle avoiding D. We prove their equivalence and equivalence to D hitting every cycle with B(C)≥0 (`GenericStrictCycleCriterion`).

**Necessity.** Sum (3.1) around any surviving cycle. The potential differences telescope to zero, and the sum of a positive number of strictly negative summands is negative. A zero-gain cycle is therefore an obstruction just as a positive-gain cycle is.

**Sufficiency.** Assume cycle safety. Every surviving path can have its repeated-vertex closed portions removed. Each removed portion is nonempty and has negative gain, so removal preserves endpoints and increases the remaining gain. It ends in a simple path. For each u, define ψ(u) as the maximum gain of a simple surviving path starting at u, including the empty path of gain zero. There are finitely many such paths, so this maximum exists. Removing cycles shows that every surviving path from u has gain at most ψ(u). Prepending a surviving edge u→v to a maximizing path from v yields

\[
 b_e+\psi(v)-\psi(u)\le0. \tag{3.2}
\]

To make the inequalities strict, retain only the edges where equality holds in (3.2). These tight edges have no nonempty closed walk: their corrected gains would sum to zero on such a walk, contradicting original cycle safety. Give each tight edge unit gain. Define ρ(u) as the maximum length of a tight path starting at u. The same path argument gives

\[
 1+\rho(v)-\rho(u)\le0
\]

on every tight edge. Let xₑ=bₑ+ψ(v)−ψ(u)≤0 and yₑ=ρ(v)−ρ(u). If xₑ=0 then yₑ≤−1. If xₑ<0, every positive ε≤−xₑ/(|yₑ|+1) makes xₑ+εyₑ<0. A finite minimum of these positive allowances, together with 1 for tight edges and the empty-set case, gives a common ε>0. Thus ψ+ερ satisfies (3.1). This is the strict-real argument implemented in [OptimizationPaths.lean](OptimizationPaths.lean); no assumed positive cycle margin or feasible-potential oracle is used.

Finally, safety is equivalent to hitting every nonnegative cycle: an unhit nonnegative cycle contradicts safety, while a surviving cycle whose gain is not negative is nonnegative and hence would have to be hit. This covers equality and proves the full target.

## 4. Elementary cycles suffice

A cycle is elementary when its first t vertices are pairwise distinct; the repeated terminal vertex is excluded from this injectivity requirement. Such a cycle has t≤|V|, including t=1 loops.

If an arbitrary positive-length cycle is not elementary, two of its first t vertices coincide. The intervening subwalk and the complementary closed walk both have positive length strictly below t; the gains add to the original gain. Strong induction decomposes it into elementary cycles, preserving every edge occurrence. If every surviving elementary cycle has negative gain, the original gain is consequently negative. Conversely, safety immediately implies negativity on elementary cycles. This proves `GenericElementaryReduction`. The implementation uses the equivalent strong-induction/loop-removal construction, explicitly verifies endpoint incidence and length-one cases, and proves the cardinality bound by injectivity of the first vertices. No zero-length summand is required to be negative.

## 5. Weighted deletion optimum equals the potential optimum

Define the failure cost and deletion cost by

\[
 F(\psi)=\sum_{e\in E}w_e\mathbf1_{b_e+\psi(v)-\psi(u)\ge0},
 \qquad C(D)=\sum_{e\in D}w_e.
\]

For any ψ let Bψ be exactly its nonnegative corrected-gain edges. Removing Bψ leaves ψ strictly feasible, so Bψ is safe, and F(ψ)=C(Bψ). Hence every potential cost is at least the minimum safe deletion cost.

There are finitely many deletion sets. At least one is safe: delete all edges, after which no positive-length surviving cycle exists. Therefore some safe D* minimizes C(D). By Section 3 choose ψ* strictly feasible outside D*. Its failure set is contained in D*, so nonnegative weights give F(ψ*)≤C(D*). The reverse inequality just proved gives equality. Both sets of attainable costs are nonempty and bounded below by zero; their infima coincide with C(D*) and are attained by D*, ψ*. This proves every clause of `GenericDeletionOptimum`, including attainment. Zero-cost edges cause no difficulty; costs are never assumed strictly positive.

The source implementation is [OptimizationDeletion.lean](OptimizationDeletion.lean). This finite attainment statement does not assert that the infinite-window correction problem attains p_h.

## 6. The literal finite truncation and its encodings

Fix M,J≥2. The finite vertices are offsets vᵢ∈{0,…,M−1}; decoding gives the positive lengths sᵢ=vᵢ+1. Decoding is injective and its image is exactly all windows with 1≤sᵢ≤M. Given any real vertex potential ψ, extend it to all windows by ψ on that image and, for example, zero elsewhere. The extension is well-defined by injectivity and is an allowed arbitrary correction. This proves `VertexEncodingAndExtension`.

The finite edges are exactly these labelled objects:

- an ascending source vertex s with 2≤s₀≤M, with target (s₀−1,s₁,…,s_{h−1}), gain log3−log2 and weight 2^{−Σsᵢ};
- a pair (K,s), 2≤K≤J, 1≤sᵢ≤M, with source (1,s₀,…,s_{h−2}), target s, gain log3−K log2 and weight 2^{−K−Σsᵢ}.

These are `TruncatedEdge`; offsets K−2 enumerate the exits. Both endpoints lie in the vertex box. In particular the newly revealed last **destination** coordinate on an exit is truncated as well; omitting it would change the retained mass and invalidate the subsequent estimate. Ascending targets need no additional out-of-box exception because their positive heads only decrease by one.

The canonical label map sends ascending source offsets to (v₀−1,v₁,…,v_{h−1}) and exits to (K−2,v). It is injective. Its image is precisely the `Retained` symbolic edges: ascending source lengths all ≤M; or exit K≤J and all h destination lengths ≤M. The decoded endpoints, dyadic weights and corrected gains are exactly those in Section 2. These coordinate identities prove `EdgeEncodingAndWeights`; there is no graph approximation of gains or weights on retained edges. See [OptimizationEncoding.lean](OptimizationEncoding.lean).

## 7. Exact natural cycle signs and dyadic denominator

Let C be a nonempty finite-graph cycle of length t, with K=1 on an ascending edge and the labelled K≥2 on an exit. Its base gain is

\[
 B(C)=t\log3-\Big(\sum_{e\in C}K_e\Big)\log2.
\]

Every Kₑ≥1, so L=ΣKₑ≥t≥1. Monotonicity of log on positive numbers gives

\[
 B(C)<0\iff3^t<2^L,
 \qquad B(C)\ge0\iff2^L\le3^t. \tag{7.1}
\]

Moreover 3^t is odd and 2^L is even, so equality is impossible. These are the four assertions of `NaturalCycleSigns`. Actual edge equality failures are still included; nonzero **cycle** gains do not imply nonzero corrected gains on individual edges.

For an edge let E(e)=Σsᵢ on ascent, and E(e)=K+Σsᵢ on exit. Set B=J+hM. Ascending exponents satisfy E≤hM≤B; exit exponents satisfy E≤J+hM=B. Establishing these inequalities **before** natural subtraction gives

\[
 2^{-E(e)}=\frac{2^{B-E(e)}}{2^B},\qquad
 C(D)=\frac{U(D)}{2^B},\quad
 U(D)=\sum_{e\in D}2^{B-E(e)}\in\mathbb N. \tag{7.2}
\]

All equalities hold in ℚ, and hence in ℝ. There is no truncated-subtraction error and no rounding. This proves `CommonDyadicDenominator`.

Safe deletion sets exist by deleting all edges. Their natural costs U(D) have a least member, achieved by a safe D, and this member is ≤U(A) for every safe A. This proves `NumeratorMinimumWellPosed` and identifies the frozen `optimalNumerator`, originally defined as a natural infimum, with a genuine minimum.

Write

\[
 q_{h,M,J}=\frac{\operatorname{optimalNumerator}(h,M,J)}{2^{J+hM}}\in\mathbb Q.
\]

Equation (7.2) and the weighted deletion theorem show that q equals the real infimum of finite potential failure costs, is a lower bound for every such cost, and is attained by some finite ψ. These are exactly the three clauses of `FiniteOptimizationExact`. See [OptimizationArithmetic.lean](OptimizationArithmetic.lean) and [OptimizationDeletion.lean](OptimizationDeletion.lean).

## 8. Retained mass, discarded mass and summability

Put t=2^{−M}, u=2^{−J}. The finite geometric identities are

\[
 \sum_{r=1}^M2^{-r}=1-t,
 \quad\sum_{r=2}^M2^{-r}=\tfrac12-t,
 \quad\sum_{K=2}^J2^{-K}=\tfrac12-u.
\]

The exact ascending mass has one head in [2,M] and h−1 other coordinates in [1,M]. The exit mass has all h destination coordinates in [1,M] and an independent summation over its labelled K in [2,J]. Finite products therefore give

\[
 T_{h,M,J}=(\tfrac12-t)(1-t)^{h-1}
              +(\tfrac12-u)(1-t)^h. \tag{8.1}
\]

No factor from summing exit labels has been dropped. The finite retained labels are an injective image, so their sum is exactly (8.1). The discarded-label series is nonnegative and dominated by the summable full weight series. Splitting that series into retained and discarded parts proves

\[
 R_{h,M,J}=\sum_{e\ \mathrm{discarded}}w(e)=1-T_{h,M,J}. \tag{8.2}
\]

This includes the summability clause of `TruncationMassIdentity`, rather than assuming a probability measure definition in place of density.

For 0≤t≤1, Bernoulli’s elementary inequality gives 1−(1−t)^m≤mt. Expand (8.2) as

\[
 R=\tfrac12[1-(1-t)^{h-1}]+t(1-t)^{h-1}
   +\tfrac12[1-(1-t)^h]+u(1-t)^h.
\]

Since both powers are at most one,

\[
 0\le R\le(\tfrac{h-1}2+1+\tfrac h2)t+u
       \le(h+1)2^{-M}+2^{-J}=:\tau_{h,M,J}. \tag{8.3}
\]

This proves `DiscardedMassBound`. It accounts for the union of all relevant input/output window requirements through the exact retained mass, not a truncated list of ascent destinations. See [OptimizationMass.lean](OptimizationMass.lean).

## 9. Transfer to the actual infimum and convergence

For any global correction φ, restricting it to decoded finite vertices gives a finite potential. Its cost is exactly the retained part of the symbolic selected-mass series. Nonnegativity and (2.1) imply

\[
 q_{h,M,J}\le F(\phi|_{\mathrm{box}})\le d_h(\phi).
\]

Every achieved literal density has this form and the achieved set is nonempty. Thus q≤p_h.

Conversely choose a finite potential ψ attaining q, and extend it to a global correction φ as in Section 6. All retained corrected gains agree exactly, so their failure cost is q. On discarded labels the selected mass is at most their total weight R, independently of the extension’s values. Summability permits addition of these parts, and the literal density theorem yields

\[
 p_h\le d_h(\phi)\le q_{h,M,J}+R_{h,M,J}
                         \le q_{h,M,J}+\tau_{h,M,J}. \tag{9.1}
\]

This proves `LiteralInfimumSandwich` for the actual achieved-density infimum. It neither defines p_h symbolically nor assumes that every arbitrary graph potential already extends without proof. Equality failures and unbounded global corrections are included by (2.1).

With M=J=n+2, τ=(h+2)2^{−(n+2)}→0 for fixed h. Therefore

\[
 0\le p_h-q_{h,n+2,n+2}\le(h+2)2^{-(n+2)}\longrightarrow0,
\]

proving `DiagonalConvergence`. Monotonicity of q is unnecessary and is not inferred from this squeeze; the optional monotonicity target remains separate. See [OptimizationDensity.lean](OptimizationDensity.lean).

## 10. A total computable exact numerator

The mathematical natural infimum `optimalNumerator` is not used as a program instruction. [OptimizationCode.lean](OptimizationCode.lean) defines a separate natural-number program on every triple p=(h₀,m₀,j₀), with h=h₀+1, M=m₀+2, J=j₀+2. Put N=M^h and E=JN. These parameters always satisfy h≥1 and M,J≥2; no partial parameter-validation branch is needed.

A vertex is encoded little-endian:

\[
 c(v)=\sum_{i=0}^{h-1}v_iM^i<N,
 \qquad v_i=\lfloor c/M^i\rfloor\bmod M.
\]

The actual finite equivalence and both inverse laws are proved in [OptimizationVertexCode.lean](OptimizationVertexCode.lean). The ascending target has code c−1 when the head is positive. The exit source has code M(c mod M^{h−1}), including h=1 when this is zero.

Program IDs are all integers e<E. Their quotient e div N is a tag; the remainder e mod N is a vertex code. Tag zero is valid exactly when the vertex head digit is positive, and encodes an ascending edge. Tags 1,…,J−1 encode exit K=tag+1 and destination vertex e mod N. Thus an ascending edge has ID c(v), and an exit (K,v) has ID (K−1)N+c(v). This is a bijection from canonical **labelled** edges onto valid IDs, not all E slots. Invalid ascending slots contribute neither constraints nor costs. [OptimizationEdgeCode.lean](OptimizationEdgeCode.lean) proves this bijection and exact source, target, K, mass-exponent and common-denominator identities. In particular the program exponent is h+Σdigits on ascent and K+h+Σdigits on exit; the ascending K=1 gain is not mistakenly added to its mass exponent.

A mask m<2^E deletes ID e when (m div 2^e) mod2=1. Every canonical finite deletion set is represented by such a mask: place its characteristic bits at the injective edge IDs and zero at unused slots. Conversely every mask defines exactly its canonical deletion set. Program cost is the finite sum of 2^{B−E(e)} over valid deleted IDs and equals U(D) exactly. Mask bits on invalid slots have no effect.

For n=1,…,N enumerate q=0,…,E^n−1. Its radix-E digits are an arbitrary ordered n-tuple of IDs. A word is surviving and closed precisely when all its IDs are valid, undeleted, and each target equals the next source, with the final source index taken modulo n. Reject a mask if any such word fails

\[
 3^n<2^{\sum_{i=0}^{n-1}K_i}. \tag{10.1}
\]

All tests are exact natural-number operations. Length zero is never tested as a cycle.

Why is this bounded test sufficient? Every surviving elementary canonical cycle has length at most |V|=N. Its edge IDs encode a word q<E^n with the same incidence, deletion bits and sum K, so (10.1) implies negative gain by (7.1). Elementary reduction then gives safety for all cycles. Conversely each surviving tested word decodes to a canonical positive-length cycle with exactly the same sum K and deletion status; canonical safety implies (10.1). These are both directions of

\[
 \operatorname{safe}(p,m)=\mathrm{true}
 \iff\operatorname{CycleSafe}(G_{h,M,J},\operatorname{maskSubset}(p,m)),
\]

proved in [OptimizationCycleCode.lean](OptimizationCycleCode.lean). Loops, repeated-edge words and parallel exits are preserved. It is not merely a finite sample of possible longer obstructions.

The executable optimizer starts at the cost of deleting every valid edge, then scans all masks m<2^E; whenever `safe` is true it replaces the current best by the minimum of it and that mask’s cost. Deleting all valid IDs is itself the bounded mask 2^E−1, which is safe and has exactly the initial cost. A simple induction on the scan proves the returned value is an accepted cost, is no larger than every accepted cost, and has an accepted witness. Thus the fallback cannot create a value lacking a feasible deletion set.

Every canonical minimizing D has a bounded representing mask, so the returned value is ≤optimalNumerator. Conversely its accepted witness defines a safe canonical D with the same units, so optimalNumerator is ≤the returned value. Therefore the program equals the frozen mathematical minimum for every triple. This is [OptimizationJoin.lean](OptimizationJoin.lean), `optimizer_eq_numerator`.

Finally the program is genuinely `Computable`, not merely a classically chosen function on finite instances. [OptimizationAlgorithm.lean](OptimizationAlgorithm.lean) proves primitive recursiveness using natural addition, multiplication, bounded subtraction, comparison, division/remainder, powers, Boolean operations, pairing and primitive-recursive finite folds. Each bound E, N, E^n and 2^E is itself computed from the input, and all loops are bounded natural recursions. No logarithm, real comparison, potential search, cycle-sign oracle or `sInf` is evaluated by the program. Standard natural-product `Primcodable` encodings supply the formal `Computable` type. Taking this concrete `optimizer` proves `ComputableExactOptimizer` uniformly on all natural triples. The search is extremely large; termination is not a useful complexity bound or a claim of practical implementation performance.

## 11. Total computable dyadic brackets

Given h=h₀+1 and requested b≥0, choose M=J=h+b+2. Call the exact numerator program with offsets (h₀,h₀+b+1,h₀+b+1), so its cap parameters are exactly M,J. This input map is primitive recursive, and composition gives a total computable natural numerator A(h₀,b)=optimalNumerator(h,M,M).

Compute the rational lower endpoint

\[
 q=\frac{A(h_0,b)}{2^{M+hM}}.
\]

Natural powers compute its nonzero denominator exactly. From (8.3),

\[
 \tau_{h,M,M}=(h+2)2^{-(h+b+2)}\le2^{-b},
\]

because h+2≤2^{h+2}. Applying the actual-infimum sandwich yields

\[
 q\le p_h\le q+2^{-b}. \tag{11.1}
\]

This proves every clause of `ComputableDyadicApproximation`: genuine total computability, equality with the specified finite numerator, and the literal density bracket at the requested accuracy. The algebraic implication in [OptimizationAccuracy.lean](OptimizationAccuracy.lean) is conditional on the exact optimizer theorem; [OptimizationJoin.lean](OptimizationJoin.lean) supplies that theorem and discharges the premise. No accuracy oracle or nonconstructive stopping criterion remains. This is algorithmic determination by certified rational brackets, not a higher-depth closed formula, a reported numerical run, or a sharp rate constant.

## 12. Required-target map and assurance boundary

| Frozen required target | Proof above | Implementing module(s) |
|---|---|---|
| `GenericStrictCycleCriterion` | §3 | `OptimizationCycles`, `OptimizationPaths` |
| `GenericElementaryReduction` | §4 | `OptimizationCycles`, `OptimizationPaths` |
| `GenericDeletionOptimum` | §5 | `OptimizationDeletion` |
| `VertexEncodingAndExtension` | §6 | `OptimizationEncoding` |
| `EdgeEncodingAndWeights` | §6 | `OptimizationEncoding` |
| `NaturalCycleSigns` | §7 | `OptimizationArithmetic` |
| `CommonDyadicDenominator` | §7 | `OptimizationArithmetic` |
| `NumeratorMinimumWellPosed` | §7 | `OptimizationArithmetic` |
| `FiniteOptimizationExact` | §7 | `OptimizationDeletion` |
| `TruncationMassIdentity` | §8 | `OptimizationMass` |
| `DiscardedMassBound` | §8 | `OptimizationMass` |
| `LiteralInfimumSandwich` | §9 | `OptimizationDensity` |
| `DiagonalConvergence` | §9 | `OptimizationDensity` |
| `ComputableExactOptimizer` | §10 | `OptimizationCode`, `OptimizationAlgorithm`, `OptimizationVertexCode`, `OptimizationEdgeCode`, `OptimizationCycleCode`, `OptimizationJoin` |
| `ComputableDyadicApproximation` | §11 | `OptimizationAccuracy`, `OptimizationJoin` |

The ordinary wrappers are in [OptimizationSolution.lean](OptimizationSolution.lean). The definitions are in [OptimizationDefinitions.lean](OptimizationDefinitions.lean). The standalone [verifier](verify.py), [source and theorem inventory](inventory.json), and [specification pins](specification.json) bind the public build inputs and complete closure coverage. Ordinary compilation remains lower assurance until the separate public full gates pass; this written companion is not an assurance receipt.

The theorem applies to the frozen run-length-only O3′ class, with equality failures, relative-odd natural density and all finite real corrections. It establishes exact finite optima and a total convergent approximation algorithm for its actual infimum. It does not prove optional monotonicity, efficient runtime, a closed form at every depth, a practical numerical table, or a new sharp inverse-depth constant. It does not extend the correction information to exit valuations or identify arbitrary symbolic cycles with actual integer periodic orbits. M4/R8/R9 pressure, entropy and regularity limits, all-seed Collatz capture, independent human refereeing and the separate public assurance gates are not conclusions of these fifteen targets.
