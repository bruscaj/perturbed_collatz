# All-length fixed-reference c=1 count: proof and formal map

Status: all23 exact frozen targets have passed a fresh ordinary private source build, raw proposition/model comparison and exhaustive standard-axiom audit (504 theorem/helper closures). The standalone public source-bound replay, trusted comparator, six checker modes and hostile controls remain pending at this snapshot; ordinary compilation is lower assurance. This written argument preceded the formal freeze; that chronology remains explicit. The result concerns the all-length extension at fixed phase-zero B_r,c=1 only. It does not refute the intended rung-only M4 question, the phase-adapted N*, or a statement at c<1. ChatGPT assisted with the argument, implementation, writing and review; overlapping AI authorship is disclosed, not independent human expert refereeing or a novelty/priority claim.

Primary statements: Polson–Sokolov v1.4.0, commit `5840497a23fc0d64127b850aea68862d7c93f2b7`, [ch10f_missed.tex](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch10f_missed.tex), label `prob:ch20:band` (unrestricted wording), and [ch10h_ratchets.tex](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch10h_ratchets.tex), labels `rrt:sec:exact` / `rrt:sec:m4` (explicit rung scope). The earlier audited finite bridge gives actual unbounded strict rungs and their unique reward maximum. A source-context audit found a general admissibility definition in ch10f:219 and general-length counting in :246, but the M4 status paragraph at :458 and detailed chapter point to rung tables and R8. Therefore this result must be presented as a distinction for the explicit all-length fixed-B_r extension, not an unqualified refutation of the authors’ intended M4 question. All counts here concern ordered positive-letter words, not realizable integer cycles or rotation classes.

## Exact model

Let theta=log(3)/log(2), beta=theta−1, delta_r=ceil(r theta)−r theta, and

- C_t=floor(t theta+delta_r), 0≤t≤r;
- k_t=C_(t+1)−C_t, 0≤t<r;
- B_r=sum_(0≤t<r) 2^(floor(t theta))/3^t;
- Phi(w)=sum_(0≤t<r) 2^(K_t)/3^t.

A source word has positive letters, K_0=0, K_r=ceil(r theta), and K_t≤C_t for t<r. Let N(1,r) count source words with Phi≥B_r. Irrationality gives 0<delta_r<1 for positive r. The canonical word k has prefixes C, so it is admissible at every positive r.

The exact integer comparisons 2^3<3^2 and 3^3<2^5 imply

3/2<theta<5/3, hence 1/2<beta<2/3.

## Two elementary rotation facts

For every phase y in[0,1), its triple y,{y+beta},{y+2 beta} contains a phase≥1/2 and a phase<1/2.

For the high phase: if y≥1/2 it is immediate. Otherwise, if y+beta<1 its next phase is>1/2. If it wraps, the next phase z=y+beta−1 is<beta−1/2<1/6, and z+beta is between1/2 and2 beta−1/2<5/6, with no wrap.

For the low phase: if y<1/2 it is immediate. Otherwise the next phase is z=y+beta−1<beta<2/3. If z is not low, its successor wraps and equals z+beta−1<2 beta−1<1/3.

Partition the indices0,…,r−1 into disjoint triples. There are therefore at least floor(r/3) indices with {t theta}≥1/2. Applying the low-phase fact to arbitrarily late triples and excluding zero phases by irrationality also gives unbounded positive r with delta_r≥1/2. No equidistribution or quantitative Diophantine theorem is needed.

## Many independent admissible swaps

The canonical letters are1 or2. No two consecutive letters equal1: two consecutive increments sum to at least floor(2 theta)≥3. Its number of1 letters is

2r−ceil(r theta)≥2r−ceil(5r/3)=floor(r/3).

Every1 except possibly the first letter is preceded by a2. Thus at least floor(r/3)−1 occurrences of21 are available. Distinct21 occurrences do not overlap. Let m=floor(r/8), for r≥8. Then m≥1 and floor(r/3)≥2m, so at least m disjoint21 pairs are available.

Choose any m of them. For each subset, replace its21 pairs by12. Each swap lowers only the intervening interior prefix by one. It preserves positivity, total endpoint and all upper caps. Different subsets give different prefix vectors, hence distinct source words. This constructs2^m admissible words.

## Reward budget

When delta_r≥1/2, each index with {t theta}≥1/2 has C_t=floor(t theta)+1. At all other indices C_t≥floor(t theta). Thus

Phi(k)−B_r ≥ sum_({t theta}≥1/2) 2^(−{t theta})
              ≥(1/2) floor(r/3)≥m.

The strict inequality 2^(−{t theta})>1/2 also holds, but is not needed for the stated non-strict threshold. A swap at the prefix t loses exactly half its canonical reward term:

(1/2) 2^(C_t−t theta) <1,

because C_t−t theta≤delta_r<1. Disjoint swaps affect separate reward terms, so every subset of the chosen m swaps loses less than m. Consequently every constructed word has Phi≥B_r and

N(1,r)≥2^floor(r/8) whenever r≥8 and delta_r≥1/2.

This inequality is an infinite-family mathematical claim, not a conclusion from the diagnostic program.

## Finite counts and real liminf/limsup

The canonical word has Phi≥B_r at every positive length, so N(1,r)≥1. The finite bridge's unique-rung maximum theorem gives N(1,r)=1 at each positive strict rung, and its rungs are unbounded. Hence the normalized logarithmic count has liminf0. On the unbounded lengths with delta_r≥1/2, the lower bound above gives

limsup_(r→∞) log10 N(1,r)/r ≥ log10(2)/8 >0.

There is no unrestricted all-length limit at c=1 for this precise normalization. This does not settle existence or computation of the rung limit at general c; at c=1 the rung value is already exactly0. Nor does it address the separately normalized phase-adapted N*.

## Finiteness and the formally necessary bounded-count argument

For each r the selected word subtype is finite: it injects into the finite positive source-word population with fixed closing sum. At r=0 the source definition requires0<r, so the selected population is empty and count0=0. At every positive r the raised phase-zero floor word is a genuine source word with reward exactly B_r, proving count>=1 independently of whether r is a rung. Raising its last letter may produce a3 off rungs; positive source words are not restricted to the canonical1/2 alphabet.

Put s=ceil(r theta). Map a selected ordered word to its list of r positive letters. This is a positive composition of s, and the map is injective because the complete list recovers the function on Fin r, including its last letter. The finite type Composition s has exactly2^(s-1) elements, with natural subtraction (at s=0 its one element is the empty composition). Since theta<2, the integer ceiling satisfies s<=2r. Thus

`count r <= 2^((ceil(r theta)).toNat-1) <= 2^(2r)`.

For r=0 this upper comparison is only0<=1; the separate empty-population proof gives the exact value. Natural cardinalities are used only with a proved finite codomain; an infinite subtype's totalized natural card is never used to justify a positive count.

Define a_r=(log(count r)/log10)/r, with the totalized a_0=0. For r>0 positivity makes these ordinary logarithms and divisions legitimate, and the count bound gives

`0 <= a_r <= 2 log2/log10`.

Both real liminf and limsup are consequently well posed and finite. Actual strict rungs are unbounded by `BridgeRungs.source_rungs_unbounded`: the irrational actual slope has arbitrarily small positive ceiling returns, forcing infinitely many strict positive records. This is a proved inherited arithmetic theorem, not a cofinality assumption. At each rung the finite source uniqueness theorem gives count1, so arbitrarily late a_r=0. Combined with nonnegativity this proves liminf a_r=0.

At arbitrarily late high-defect lengths the proved swap injection gives count>=2^floor(r/8). The score `(floor(r/8)/r)*(log2/log10)` tends to `(log2/log10)/8`, using `r%8+8*(r/8)=r` and bounded remainder. Intersecting the frequent high-defect set with any eventual upper bound on a_r proves limsup a_r>=(log2/log10)/8>0. A hypothetical real limit would equal both its liminf0 and its strictly positive limsup, a contradiction. This avoids an unproved exchange of limits or a default value for an unbounded real limsup.

## Formal implementation and exact target map

The frozen definitions and target types are [UnrestrictedDefinitions.lean](UnrestrictedDefinitions.lean) and [UnrestrictedExpectedTypes.lean](UnrestrictedExpectedTypes.lean); [specification.json](specification.json) pins their original meanings, the exact isolated challenge, inherited model files,23 raw propositions and13 raw model definitions. No proof imports the challenge. The seven implementation modules and [UnrestrictedSolution.lean](UnrestrictedSolution.lean) prove the following exact roots:

| Frozen proposition | Root wrapper | Implementation |
|---|---|---|
| `SlopeBounds` | `slopeBounds` | [UnrestrictedRotation.lean](UnrestrictedRotation.lean) |
| `TripleRotationHighLow` | `tripleRotationHighLow` | [UnrestrictedRotation.lean](UnrestrictedRotation.lean) |
| `HighPhaseCountLower` | `highPhaseCountLower` | [UnrestrictedRotation.lean](UnrestrictedRotation.lean) |
| `LargeDefectsUnbounded` | `largeDefectsUnbounded` | [UnrestrictedRotation.lean](UnrestrictedRotation.lean) |
| `CanonicalPrefixLaw` | `canonicalPrefixLaw` | [UnrestrictedCanonical.lean](UnrestrictedCanonical.lean) |
| `CanonicalAllLengthWord` | `canonicalAllLengthWord` | [UnrestrictedCanonical.lean](UnrestrictedCanonical.lean) |
| `CanonicalAlphabetAndSites` | `canonicalAlphabetAndSites` | [UnrestrictedCanonical.lean](UnrestrictedCanonical.lean) |
| `ManyDisjointCanonicalSites` | `manyDisjointCanonicalSites` | [UnrestrictedCanonical.lean](UnrestrictedCanonical.lean) |
| `SwapPrefixLaw` | `swapPrefixLaw` | [UnrestrictedSwaps.lean](UnrestrictedSwaps.lean) |
| `SwapPreservesSource` | `swapPreservesSource` | [UnrestrictedSwaps.lean](UnrestrictedSwaps.lean) |
| `SwapFamilyInjective` | `swapFamilyInjective` | [UnrestrictedSwaps.lean](UnrestrictedSwaps.lean) |
| `SwapCubeCard` | `swapCubeCard` | [UnrestrictedSwaps.lean](UnrestrictedSwaps.lean) |
| `SwapRewardIdentity` | `swapRewardIdentity` | [UnrestrictedSwaps.lean](UnrestrictedSwaps.lean) |
| `CanonicalRewardBudget` | `canonicalRewardBudget` | [UnrestrictedCanonical.lean](UnrestrictedCanonical.lean) |
| `CanonicalSwapLossBound` | `canonicalSwapLossBound` | [UnrestrictedCanonical.lean](UnrestrictedCanonical.lean) |
| `LargeDefectWitnessInjection` | `largeDefectWitnessInjection` | [UnrestrictedInjection.lean](UnrestrictedInjection.lean) |
| `ExponentialCountLower` | `exponentialCountLower` | [UnrestrictedInjection.lean](UnrestrictedInjection.lean) |
| `RungCountOne` | `rungCountOne` | [UnrestrictedCounts.lean](UnrestrictedCounts.lean) |
| `AllLengthCountBounds` | `allLengthCountBounds` | [UnrestrictedCountBound.lean](UnrestrictedCountBound.lean) |
| `NormalizedLogBounds` | `normalizedLogBounds` | [UnrestrictedLimits.lean](UnrestrictedLimits.lean) |
| `NormalizedLogLiminf` | `normalizedLogLiminf` | [UnrestrictedLimits.lean](UnrestrictedLimits.lean) |
| `NormalizedLogLimsup` | `normalizedLogLimsup` | [UnrestrictedLimits.lean](UnrestrictedLimits.lean) |
| `NoAllLengthLimit` | `noAllLengthLimit` | [UnrestrictedLimits.lean](UnrestrictedLimits.lean) |

The subset injection uses one actual canonical site set S of size r/8. Every cube member T is a subset of S, inherits admissible disjoint21 sites and preserves the original source constraints. Its loss is at most cardT<=r/8<=(r/3)/2, while the same canonical word has at least that reserve above B_r. The exact swap reward identity proves every image meets the threshold. Injectivity is proved on this same cube, which has2^cardS members, then mapped into the explicitly finite selected subtype. No finite experimental count supplies the universal lower bound.

The two limit helpers deliberately expose their remaining `ExponentialCountLower` hypothesis. The final `normalizedLogLimsup` and `noAllLengthLimit` wrappers explicitly supply `ExternalM4UnrestrictedInjection.exponential_count_lower`; no such assumption survives in the frozen root statements.

## Evidence and remaining assurance

The full mathematical and statement/assembly reviews were separate AI tasks, with prior implementation overlap explicitly disclosed. The private fresh ordinary integration checked32 owned modules and504 theorem/helper closures, all23 exact frozen proposition bodies and all13 model bodies, allowing only `propext`, `Quot.sound` and `Classical.choice`. No custom axiom, challenge import or unproved exponential bound is accepted. Public reports must state their own exact source hashes and completed gates; private ordinary evidence does not stand in for the public replay/comparator/checker pipeline.

The standalone [verifier](verify.py) distinguishes lower-assurance build mode from full mode. Full success requires a fresh complete source-bound proof export/replay, the exact23-target trusted comparator, and explicit acceptance by Lean default/paranoid, lean4lean, nanoda, con-leche and con-ron in both stages. Hostile controls require a positive full pipeline before semantic rejections. Until those actual Linux receipts pass, this package remains a lower-assurance prepared result. There is no claimed human refereeing, practical complexity bound, priority, M4 rung entropy theorem, phase-adapted theorem, pressure/R8/R9 result, integer Collatz cycle or capture conclusion.
