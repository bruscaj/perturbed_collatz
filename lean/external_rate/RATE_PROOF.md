# Finite-information Syracuse potentials: explicit inverse-depth bounds

**Project owner and author: Jake S. Brusca.** ChatGPT assisted with ideas,
mathematics, Lean proofs, code, writing and separate-context AI review.
Personal research project and work in progress; the author is not an expert
in this field. Corrections and qualified scrutiny are welcome. No human
refereeing, priority certification or external acceptance is claimed.

This written reconstruction, dated 2026-11-28 UTC, matches all 11
required statements in the frozen
[rate specification](RateExpectedTypes.lean). It uses the
finite-moment **Cantelli** route. It does not rely on the earlier optional
Chernoff route or prove the separate optional stronger liminf constant.
Exact source-bound compiler, axiom, replay, comparator and independent
checker receipts remain distinct from this written proof.

The review context authored `RateProductMoments` and earlier general
geometric helpers. The marker, maximum-event, normalization, cycle, lower,
Cantelli, infimum and final assembly modules were developed in other
contexts and reviewed here. This is not wholly separate authorship or
human expert review of every component. Preparing the original review did not alter any frozen or proof file.

## 1. Source question and precise result

The primary source is Polson–Sokolov, edition 1, v1.4.0, commit
`5840497a23fc0d64127b850aea68862d7c93f2b7`,
[`ch11_open.tex`, O3′](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch11_open.tex),
label `prob:ch11:o3p`, with the block convention in
[`ch05c_mmcollatz.tex`](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch05c_mmcollatz.tex).
We use its run-length-only finite-information class. Exit valuations refine
the population events but are not extra information supplied to a correction.

For positive odd integers define

\[
 K(x)=v_2(3x+1),\qquad S(x)=\frac{3x+1}{2^{K(x)}},\qquad R(x)=v_2(x+1).
\]

A remaining block consists of its R(x)−1 valuation-one strides followed by
its first valuation-at-least-two stride. Its next seed is
`B(x)=S^{R(x)}(x)`, including the exit. At fixed positive integer depth h,

\[
 W_h(x)=(R(x),R(Bx),\ldots,R(B^{h-1}x)).
\]

Entry zero is the current remaining length; the other h−1 entries are
complete future blocks. Allow **every** function
`φ : (positive integer)^h → Real`, with no boundedness, regularity, finite
support, additivity or integrability restriction. Put

\[
 V_\varphi(x)=\log x+\varphi(W_h(x)).
\]

Failure means `Vφ(Sx)≥Vφ(x)`, including equality. Let d_h(φ) be its relative
natural density among positive odd launch seeds, which will be proved to
exist. Define the actual achieved-density infimum

\[
 p_h=\inf\{d:\exists\varphi,\ d=d_h(\varphi)\}.
\]

The formal correction domain includes zero-containing natural windows by
totalization. Every function on positive windows extends arbitrarily, and
those unused values do not affect source failures. Thus the whole intended
correction class is retained.

**Theorem.** For every positive integer h,

\[
 \boxed{\frac1{4(h+33)}\le p_h\le\frac5{2h}.} \tag{1}
\]

In particular the required weaker lower bound
`127/(32768h)≤p_h` holds and `p_h→0` as h tends to infinity. For h≥2 the
upper bound is witnessed by an explicit correction with actual density

\[
 d_h(\varphi_h)\le
 \min\left(\frac12,\frac1{h-1}+\frac1{2h}\right). \tag{2}
\]

These bounds give order 1/h for the optimized failure density in this
precise information class. They do not give exact p_h for each h≥2, optimal
constants, the optional stronger asymptotic lower constant, or Collatz
convergence. The stronger lower side of (1) is an actual supporting theorem;
the frozen required rate uses the smaller rational constant above.

## 2. Literal blocks and the exact population law

Write x=2^r q−1 with q positive odd, r=R(x)≥1. Its within-run states are
`x_i=3^i 2^{r-i}q−1`, 0≤i≤r−1. For i<r−1,

    3x_i+1 = 2(3^(i+1) 2^(r-i-1)q−1)

has valuation exactly one. At i=r−1 it equals `2(3^r q−1)`, of valuation
at least two. Every finite stride and block iterate remains positive odd.
Deleting an ascending stride therefore decreases the current remaining
length by one while preserving all future block entries. At an exit the
window shifts

    (1,s₁,…,s_{h−1}) → (s₁,…,s_h).

No termination theorem for the whole orbit is required. At x=1 the literal
map continues with S(1)=1 and every block length one; all corrections fail
there by equality. This singleton is included in the counts.

We establish the finite-population laws used below rather than assume iid
symbols along positive integer trajectories. Write each seed as x=2n+1.
For k≥1, e≥0 and 0≤d<2^e, an exact successor condition has the identity

\[
\begin{split}
 &K(2n+1)=k,\quad S(2n+1)=2m+1,\quad m\equiv d\pmod{2^e}\\
 &\qquad\Longleftrightarrow\quad
 3n+2\equiv2^{k-1}(2d+1)\pmod{2^{k+e}},
 \quad\text{for some }m\ge0. \tag{3}
\end{split}
\]

Forward, substitute `3n+2=2^{k−1}(2m+1)` and `m=d+2^e q`. Reverse, the
quotient/remainder identity constructs `m=d+2^e q` from the congruence;
then `3(2n+1)+1=2^k(2m+1)` proves both exact valuation and division. The
right residue is strictly below the modulus. Multiplication by three is
invertible modulo a power of two, so (3) specifies one unique normalized
residue class in n. This includes k=1 and the modulus-one auxiliary case
e=0; no invalid subtraction of two from a target-one residue is needed.

The terminal length condition is

\[
 R(2n+1)=r\quad\Longleftrightarrow\quad
 n\equiv2^{r-1}-1\pmod{2^r},\qquad r\ge1. \tag{4}
\]

Thus a finite prescribed valuation word with total exponent A, followed
by terminal remaining length r, is exactly one class modulo `2^{A+r}` in n,
by repeated backward use of (3). The empty word is (4).

For m completed blocks with positive lengths ℓ₀,…,ℓ_{m−1}, exit valuations
κ₀,…,κ_{m−1}≥2, and terminal length ℓ_m≥1, the word is each block's ℓ_i−1
ones followed by κ_i. The first-exit characterization above proves both
directions of this block/word equivalence, including ℓ_i=1 and m=0. Its
exact cylinder exponent is

\[
 E=\sum_{i<m}(\ell_i-1+\kappa_i)+\ell_m. \tag{5}
\]

A normalized class d modulo M has exactly
`floor((N+M−1−d)/M)` representatives among 0≤n<N, differing from N/M by
at most one. Hence the class in (5) has relative odd natural density 2^-E.
The refined masses are positive, summable and total one because

\[
 2^{-E}=\prod_{i=0}^{m}2^{-\ell_i}
          \prod_{i=0}^{m-1}2^{-(\kappa_i-1)},
\]

and every displayed one-coordinate geometric factor sums to one.

Here is the finite-tail principle needed to combine such classes. For an
actual exhaustive label partition with coordinate masses w_i summing to
one, and a selected event P, every finite label set F gives

\[
 \sum_{i\in F}\operatorname{freq}_N(i\cap P)
 \le\operatorname{freq}_N(P)
 \le\sum_{i\in F}\operatorname{freq}_N(i\cap P)
                  +1-\sum_{i\in F}\operatorname{freq}_N(i). \tag{6}
\]

If the decision of P eventually agrees with a fixed decision on each
label, its selected coordinate limit is w_i times that decision: finite
prefixes have density zero. First take limits for finite F in (6), then
choose F with arbitrarily small omitted weight. The full event has the
sum of the selected masses. This requires no common cutoff over infinitely
many labels and no countable-additivity assertion for natural density.

For fixed h take refinements with m=h. Marginalize their unused hidden
exits and terminal length to obtain the following coarse label masses:

\[
 \begin{array}{ll}
 \text{ascending window }(r,s_2,\ldots,s_h),\ r\ge2:
   &w_A=2^{-(r+s_2+\cdots+s_h)},\\
 \text{exit }K\ge2\text{ and successor }(s_1,\ldots,s_h):
   &w_E=2^{-(K+s_1+\cdots+s_h)}.
 \end{array} \tag{7}
\]

For the exit, fixing the old length one and first exit K contributes
`2^-1 2^-(K−1)=2^-K`; all remaining hidden exits sum to one. For the ascent,
all exits and the last unused length sum to one. Applying (6) to the exact
refinement projection proves the **literal** coarse label densities in (7).
Each branch's full mass is 1/2.

Let a=log(3/2), b=log 2. The corresponding symbolic gains are

\[
 \begin{split}
 g_A&=a+\varphi(r-1,s_2,\ldots,s_h)-\varphi(r,s_2,\ldots,s_h),\\
 g_E&=\log3-Kb+\varphi(s_1,\ldots,s_h)
                    -\varphi(1,s_1,\ldots,s_{h-1}).
 \end{split} \tag{8}
\]

The exact literal increment is the appropriate g plus

\[
 \epsilon(x)=\log\left(1+\frac1{3x}\right)>0,\qquad\epsilon(x)\to0. \tag{9}
\]

On a fixed cell g is a fixed real number, however unbounded φ may be over
other windows. For g≥0, including zero, failure occurs; for g<0, eventually
ε<−g and the stride succeeds. Apply (6) a second time, now to the coarse
partition and literal failure. Every d_h(φ) exists and is exactly

\[
 d_h(\varphi)=A(\varphi)+\sum_{K\ge2}E_K(\varphi), \tag{10}
\]

where A and E_K sum (7) over gains (8) that are ≥0. All selected masses
are nonnegative and dominated by total mass one. This proves existence,
uniqueness and 0≤d_h(φ)≤1 for the full correction class.

The odd integers ≤X are precisely `2n+1` for
`0≤n<floor((X+1)/2)`. Thus the source cutoff frequency equals the first-N-odds
frequency at that exact cutoff. The cutoff tends to infinity, and X=2N
gives the converse implication. This confirms the source's normalization.
The achieved-density set is nonempty by choosing φ=0 and bounded below
by zero, so its real sInf p_h is a genuine infimum. No attainment is assumed.

These arithmetic and density foundations are implemented in the general
finite-depth package; its complete reconstruction is
[GENERAL_DENSITY_PROOF.md](../external_population/GENERAL_DENSITY_PROOF.md).
The argument above states the steps needed here explicitly.

## 3. The explicit first-maximum marker

For h≥2 and a positive window w=(w₀,…,w_{h−1}), let j(w) be the **first**
index attaining the maximum among future entries 1,…,h−1. Equivalently,

\[
 1\le j<h,\quad w_i\le w_j\ (1\le i<h),\quad
 w_i<w_j\ (1\le i<j).
\]

Scanning the ordered future indices and replacing the candidate only on
a strict improvement gives exactly this selector. Define

\[
 D_h(w)=\sum_{i<j(w)}w_i,\qquad\varphi_h(w)=bD_h(w). \tag{11}
\]

This correction reads only the allowed h run lengths. It can be unbounded,
which is permitted. For h=1 the formal selector is totalized to zero and
D₁=0; the future-marker argument below is used only for h≥2.

On an ascending edge, only the head decreases by one. The selected future
index is unchanged and positive, so D decreases by one. Its symbolic gain
is `a−b=log(3/4)<0`. Therefore all ascending selected masses vanish, and
the actual density of this explicit correction is at most the exit mass
1/2 by (10). This is already an achieved literal density cap.

At an exit write the old and new windows as

    old = (1,s₁,…,s_{h−1}),   new = (s₁,…,s_h).

Let j be the old marker. If j≥2 and incoming s_h is no larger than its
value, the old chosen future block remains the first maximum among new
future entries, now at index j−1. An incoming **tie** does not displace
the earlier marker. Consequently `D(old)=1+D(new)`. For every K≥2 the
symbolic exit gain is then

    log 3 − Kb − b ≤ log(3/8) < 0.

Thus a symbolically failed exit must lie in at least one of two events:

1. The old marker departs the future set: j=1. This means s₁ is a weak
   maximum among the old future entries s₁,…,s_{h−1}.
2. The incoming entry is strictly larger than the old maximum. Then s_h
   is the strict maximum among **all h** successor entries s₁,…,s_h.

The first event imposes no condition on the incoming last entry. It
compares h−1 old future entries, not all h successor entries. For h=n+2
this is frozen `WeakPrefix n` on n+2 offsets, involving its first n+1
entries; the remaining final offset is summed out.

The first-tie rule is essential. At h=3, successor `(1,2,2)` has old window
`(1,1,2)`. The retained first maximum moves from old index two to new
index one, giving K=2 gain ratio 3/8. Choosing the latest tie instead would
give ratio 3/2 even though neither stated exception occurs.

## 4. Maximum-event masses and the marker upper bound

Use the explicit independent **finite product weights** of geometric
lengths, `P(R=m)=2^-m`, m≥1, which describe the coarse masses (7). No
independence along an individual integer trajectory is asserted.

For h exchangeable entries, strict-maximum events at the different indices
have equal masses and are disjoint. Ties for the maximum produce no strict maximum and
are not treated as a probability-zero event. Hence the strict incoming
event has mass at most 1/h.

For a first entry competing weakly against m others, use offsets A=R−1
with atom `t_a=2^-(a+1)` and exact CDF `P(A≤a)=1−t_a`. The weak-head mass is

\[
 S_m=\sum_{a\ge0}t_a(1-t_a)^m. \tag{12}
\]

It satisfies `S_m≤2/(m+1)`. To prove this without a continuous or tie-free
approximation, note that for 0≤x≤y,

\[
 y^{m+1}-x^{m+1}
   =(y-x)\sum_{j=0}^{m}y^{m-j}x^j
   \ge(m+1)x^m(y-x).
\]

Set x=1−t, y=1−t/2 for 0≤t≤1. Then

\[
 t(1-t)^m\le\frac2{m+1}
       \big((1-t/2)^{m+1}-(1-t)^{m+1}\big).
\]

Since `t_{a+1}=t_a/2`, summing over a finite range telescopes and is at
most 2/(m+1). The summands are nonnegative and bounded by t_a, so their
series converges and the same bound holds. For departure, m=h−2. The
unused incoming coordinate has total mass one, giving departure mass
at most 2/(h−1).

These two events need not be disjoint; a union bound suffices. They depend
only on the successor window, not on K. The full actual exit factor is

\[
 \sum_{K\ge2}2^{-K}=\frac12.
\]

Consequently (7)–(10) yield an actual density for (11) satisfying

\[
 d_h(\varphi_h)\le\frac12
       \left(\frac2{h-1}+\frac1h\right)
       =\frac1{h-1}+\frac1{2h}.
\]

Combining the preceding cap 1/2 proves (2), exactly `MarkerUpperBound`.
The full exit factor 1/2 here is distinct from the fixed-K=2 factor 1/4
used later in the lower bound.

Since this d is actually achieved, `p_h≤d_h(φ_h)`. For h≥2,
`1/(h−1)≤2/h`, so `p_h≤5/(2h)`. For h=1, the achieved-density bound
`p₁≤1≤5/2` supplies the required exception without inventing a future
marker at depth one.

## 5. Auxiliary cyclic histories and pointwise forcing

For the lower bound fix any correction φ, still completely unrestricted,
and put n=h+1. Use n positive lengths R₀,…,R_{n−1} with weight

\[
 w(R)=\prod_{i=0}^{n-1}2^{-R_i},\qquad\sum_R w(R)=1.
\]

Their h-entry windows are repeated cyclically, with the current remaining
length s at the head. Each block has R_i−1 ascent gains (8) and one exit
gain with **fixed K=2**. This is an auxiliary finite cycle in the information
graph, not a periodicity claim about any integer orbit. The use of n=h+1
provides all h successor entries while keeping the current length separate.

The ascent corrections telescope within each block. Its total gain is

\[
 R_i a-b+\varphi(W_{i+1}(R_{i+1}))-\varphi(W_i(R_i)).
\]

The full h-entry window closes after n positions, so the total correction
telescopes pointwise around the finite cycle. Its gain is

\[
 G(R)=a\sum_iR_i-nb. \tag{13}
\]

If G>0, at least one constituent stride has gain ≥0 and hence is a failed
symbolic edge. Let B_i(R) count failed edges in block i and let
`Cφ(R)=Σ_i B_i(R)`. Then

    0≤B_i≤R_i,    G>0 implies Cφ≥1.

This gives `CyclicTelescoping` and `CyclicForcing`. The telescoping is
finite and precedes any weighted sum. No expectation of φ or of its
possibly nonintegrable differences is taken.

## 6. Exact block-to-odd-seed normalization

Let A=A(φ) and E₂=E₂(φ) in (10). The precise normalization is

\[
 E[B_0]=2A+4E_2. \tag{14}
\]

For the ascent part, condition on the h−1 future offsets c and let q_j(c)
be its failure bit at remaining length j+2. If the current length offset
is t=R₀−1, its ascent count is `Σ_{j<t}q_j(c)`. With
`atom(t)=2^-(t+1)`, the geometric tail identity is

\[
 \sum_{t\ge0}\operatorname{atom}(t)\sum_{j<t}q_j(c)
   =\sum_{j\ge0}\operatorname{atom}(j)q_j(c),
 \qquad\sum_{t>j}\operatorname{atom}(t)=\operatorname{atom}(j).
\]

The corresponding source ascending mass has the extra factor 1/2 in
(7), because its head is j+2. The unused final history slot sums to one.
Hence the expected ascent count is 2A. Prefix counts are bounded by t,
so their sums are justified by the finite geometric first moment.

For the K=2 exit, the old exit head is one. Its gain depends only on
the h successor lengths and not on R₀; summing R₀ gives one. But its
source mass (7) has factor `2^-2=1/4`. Thus the expected exit failure bit
is four E₂, proving (14). The factors are not obtained by dividing by an
average block length. For all failure bits set to one, expected ascent
count is E[R−1]=1 and exit count one, whereas A=1/2 and E₂=1/4; both sides
of (14) are two.

All counts are dominated by finite sums of geometric lengths. This proves
their summability for **every** φ, regardless of correction integrability.
The history product is invariant under finite cyclic permutations. Rotation
identifies the full windows and block gains, so each E[B_i]=E[B₀]. There
are exactly n=h+1 blocks. Therefore

\[
 E[C_\varphi]=n(2A+4E_2).
\]

Writing `P_h=Σ_R w(R)1_{G(R)>0}`, pointwise forcing and nonnegative summation
give `P_h≤E[Cφ]`. For any achieved literal density d=d_h(φ), (10) and
positivity give `A+E₂≤d`, hence `2A+4E₂≤4d`. We conclude

\[
 \boxed{\frac{P_h}{4(h+1)}\le d_h(\varphi)}. \tag{15}
\]

This is `CyclicNormalization` and `CyclicDensityLowerBound`. The identification
of d with (10) is justified by actual density existence and uniqueness, not
an assumed Bernoulli surrogate. The auxiliary cyclic histories themselves
are not asserted to be literal repeated trajectories.

## 7. Product moments and the one-sided Cantelli estimate

For a single positive geometric length,

\[
 E[R]=2,\qquad E[R^2]=6,\qquad E[R-2]=0,\quad E[(R-2)^2]=2.
\]

For completeness, `P(R≥j)=2^{-(j−1)}` gives
`E[R]=Σ_{j≥1}2^{-(j−1)}=2` and
`E[R²]=Σ_{j≥1}(2j−1)2^{-(j−1)}=6`. The latter uses
`Σ_{j≥1}j2^{-(j−1)}=4`, obtained by subtracting its half-shifted geometric
series. Nonnegative finite partial sums justify these identities and their
limits.

For the finite product let `L=Σ_iR_i` and `Z=L−2n`. Factoring the finite
product sums gives

\[
 E[L]=2n,\qquad E[L^2]=6n+4n(n-1)=4n^2+2n,
 \qquad E[Z]=0,\quad E[Z^2]=2n. \tag{16}
\]

These are identities for the explicit finite product, not independence
assumptions about an integer orbit. The implementation derives the raw
nonnegative moments first and then centers by finite algebraic combinations,
so no signed-product summability premise is omitted.

The exact integer inequality `3^7=2187>2048=2^11` implies `7a>4b`.
Since n=h+1>0, if `Z≥−n/4` then `L≥7n/4` and (13) gives strictly G>0.
Hence G≤0 implies `Z<−n/4`.

Set `D=8+n/4>0`. On the complement of the positive-cycle event,

    8−Z>D>0,    so 1≤(8−Z)²/D².

Thus pointwise

\[
 w(R)\le w(R)\mathbf1_{G>0}+w(R)(8-Z)^2/D^2.
\]

By (16), the square is summable and

\[
 E[(8-Z)^2]=64+2n,\qquad
 \frac{64+2n}{(8+n/4)^2}=\frac{32}{n+32}.
\]

Sum the pointwise inequality and use total mass one. This proves

\[
 \boxed{P_h\ge\frac n{n+32}=\frac{h+1}{h+33}}. \tag{17}
\]

This is the required `PositiveCycleMassLowerBound`. The one-sided event
and positive denominator are essential; no Gaussian approximation or
two-sided variance estimate with a misplaced sign is used. The closed
threshold Z≥−n/4 is valid because the logarithmic comparison is strict.

## 8. Actual infimum lower bound and unconditional limit

Combining (15) and (17), every correction has actual density

\[
 d_h(\varphi)\ge\frac1{4(h+33)}.
\]

The achieved-density set is nonempty and bounded below, as proved in
Section 2. A lower bound on every member is a lower bound on its sInf,
without assuming a minimizer. This proves the stronger lower side of (1).

For h≥1, `h+33≤34h`, so

\[
 \frac1{136h}\le\frac1{4(h+33)}.
\]

Also `127·136=17272≤32768`, so
`127/(32768h)≤1/(136h)`. Thus the frozen rational lower constant is met
for all positive integer depths. Section 4 supplies the required upper
constant 5/(2h), including its h=1 exception.

Both sides are now unconditional: the final assembly uses the **proved**
marker upper theorem, not an assumption bearing its name. This is
`ExplicitInverseDepthRate`. Finally

    0≤p_h≤5/(2h) → 0

proves `InfimumTendsToZero` by squeezing the real sequence along h=1,2,….
It does not exchange h with the population limit or assert uniform
stabilization over corrections or windows. Each literal density was first
established at its own fixed h.

## 9. All required target mappings and assurance scope

| Frozen target | Proof content / implementation |
| --- | --- |
| `InfimumWellPosed` | Actual existence, uniqueness, nonempty achieved set and [0,1] bounds; `RateInfimum`. |
| `MarkerSelectorLaw` | First future argmax with strict earlier-tie inequality; `RateMarker`. |
| `MarkerUpperBound` | Actual marker density, half cap and weak/strict maximum estimate; `RateMarkerUpper`, `RateMaxMass`, `RateMarkerEvents`. |
| `HistoryWeightLaw` | Exact normalized geometric product; `RateMoments`. |
| `CyclicNormalization` | The exact 2A+4E₂ identity; `RateNormalization`. |
| `CyclicTelescoping` | Full-window pointwise cyclic cancellation; `RateCycles`. |
| `CyclicForcing` | Counts bounded by lengths and a forced failure when G>0; `RateCycles`. |
| `CyclicDensityLowerBound` | Rotation, normalization and actual d from the general density law; `RateLower`. |
| `PositiveCycleMassLowerBound` | Exact centered moments and one-sided square; `RateProductMoments`, `RateCantelli`. |
| `ExplicitInverseDepthRate` | Strong actual lower bound, rational weakening and achieved marker upper bound; `RateBounds`, `RateMain`. |
| `InfimumTendsToZero` | Nonnegative scalar squeeze using the unconditional rate; `RateInfimum`, `RateMain`. |

[RateSolution.lean](RateSolution.lean) supplies all 11
matching required wrappers. The optional stronger asymptotic target is
separate and is not discharged here. Exact higher-depth optima and optimal
constants are not determined by these inequalities.

The separate-context AI semantic review included bounded exact-rational
checks and the first-versus-last marker tie counterexample. Such finite checks
do not prove an infinite theorem. The canonical implementation passed an ordinary
fresh source build and an exhaustive audit of 765 theorem closures before this
standalone packaging. Ordinary compilation and axiom assurance remain distinct
from successful source-bound replay, frozen-statement comparison and independent
checker coverage. The public [inventory](inventory.json) binds the exact files,
targets and every generated helper; the [README](README.md) describes the gates.
Project-specific Linux full-mode and hostile-control receipts remain required
before full assurance is claimed. No human expert review or Collatz convergence
claim follows.
