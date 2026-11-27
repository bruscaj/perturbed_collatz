# Proportional intervals and basin boundaries

## 2. Two inverse loops and a fixed-clock B1 connector

Use positive normalized height z and phase p, H=(0,0,0,1,0,0,1),
physical n=z-1+H[p]. A reverse tick from phase p to q=p-1 mod7 is

    S(z)=2z-(1-H[q]),
    G(z)=(2z-H[q])/3, when its numerator is divisible by 3.

Both are positive, integral, actual inverses on their stated domains. Indeed the
G numerator forces z=0 mod3 for H[q]=0 or z=2 mod3 for H[q]=1; the new height
has the prescribed growing parity. The S branch always has the other parity.
Any inverse word with k ticks and g grows has endpoint

    (2^k z-N)/3^g,

with a nonnegative integer N. Starting at (N,d)=(0,1), update N to
`2N+c*d`, c=H[q] for G, c=1-H[q] for S, and multiply d by 3 for G.
Final integrality implies every intermediate integrality: once a positive
power of three appears in a reduced denominator it cannot be canceled by
multiplying by two, subtracting an integer, or dividing by three. Thus the
whole-word guard is one ternary residue. For an integral word starting positive,
positivity follows step by step from the inverse formulas, not from an extrapolation.

Align any target to phase one using at most six S steps. At phase one, seven
shrinks give

    S0(z)=128z-91,       a=91/127,
    S0(z)-a=128(z-a).

For each z mod3 there is a seven-step inverse lap with exactly one G, whose
position is selected from the seven possibilities. For every one of those
possible words, if legal,

    S1(z)-a = L(z-a)+c,     L=128/3,  |c|<30.

The verifier checks all three residues and every offset inequality. It also
checks that exactly two grows in seven ticks can be attained on every residue
mod9, using nine whole-ray certificates. The latter is available for optimizing
the construction; the proof below uses only S0 and S1.

**New fixed-count B1 adapter.** From every phase-one z>0, exactly 28 reverse
steps with exactly three G letters can produce a phase-one height divisible
by six. Enumerate the words with the final (slot 27) G and two other G slots
in 0..26. Their offset N is even. To ensure output divisible by six impose

    2^28 z = N mod81.

Of the 351 candidate words, choose one minimizing N for each of the 81
residues; all 81 exist. Their endpoint is B(t)=(6t,1), with

    t = K(z-N/2^28),      K=2^28/162=2^27/81.

The table has max |a-N/2^28| = 1367344085/17045651456 < 1/10.
The checker replays the 81 entire affine rays through the independent signed
physical forward update, including all parity guards, safety, phase, and exactly
three grows. This is a fixed-clock, fixed-count interface, not a smaller-parameter
reduction; its size factor is large. It complements PR19's entry proof.

## 3. Unconditional local inverse hitting: any fixed proportional interval

For a given target, write z0 for the aligned phase-one height and C=z0-a>0
(C>=36/127). Execute j S0 laps, then g S1 laps, then the 28-tick adapter.
The chosen S1 words may depend on the current residue. The uniform error bound
above yields an exact real representation of the resulting integer parameter:

    t = K L^g (128^j C + e),        |e|<1.                (1)

Indeed the normalized accumulated S1 offset is bounded by the geometric
sum 30/(L-1)=18/25, and the normalized adapter offset by 1/10, since L^g>=1.
The exact total reverse clock is a0+7(j+g)+28, a0<=6 for alignment, with g+3
grows. The leading scale in (1) is `K C 128^(j+g)/3^g`.

Fix 0<delta<=1. Because log_128(3) is irrational by prime factorization,
the fractional parts of -g log_128(3) are dense modulo one. Thus for some
finite G=G(delta), the mantissas of 3^(-g), g=0..G, modulo powers of 128,
form a circular multiplicative net of maximum successive ratio <=1+delta/4.
This is elementary irrational rotation density; it also follows directly by
choosing a nonzero rotation return arbitrarily close to zero and stepping by
it around the circle. The same property holds with g constrained to any fixed
residue mod m (replace the rotation by m times that irrational number).

Choose J with 128^J*(36/127)>=16/delta. Given X>=K*C*L^G*128^J, let
Y=(1+delta/4)X. Some g in the net and j>=J give

    Y <= K*C*L^g*128^j <= (1+delta/4)Y.

The lower constraint on X ensures every selected power index can be at least
J. The relative error in (1) is <delta/16. For 0<delta<=1, both inequalities

    (1-delta/16)(1+delta/4)>1,
    (1+delta/16)(1+delta/4)^2<1+delta

hold (expand the polynomials; for the upper bound use delta<=1). Therefore

    X < t < (1+delta)X,    F^clock(B(t))=original target.    (2)

Since z0<=64z for original height z, this proves the following UNCONDITIONAL
written theorem:

**Uniform proportional interval hitting.** For every fixed delta>0 there is an
effective M_delta such that every positive phased target of height z has a B1
ancestor in every (X,(1+delta)X) with X>=M_delta*z. For delta>1 use delta=1.
One sufficient constant is `64*K*L^G*128^J`, rounded up. The constructor uses
only exact inverse steps, with additional clock O_delta(1+log(X/z)). Constants
from this elementary construction are enormous; this is a proof of existence
and a constructive scale control, not a practical assertion at moderate X.

The verifier certifies six rational rotation nets, unrestricted and with g
even/odd, at delta=1/2 and 1/10, plus 42 literal phase-correct inverse-band
witnesses across all phases and eight further index-spread witnesses. No
floating-point calculation is used to establish a net or witness. Examples
can require thousands of bits. 

### Quantitative gap and what existing Diophantine theory can give

Let alpha=log(3)/log(128). For consecutive continued-fraction convergents
p/q, p'/q', the usual estimate |q alpha-p|<1/q' and the integer gap
|3^q-128^p|>=1 give, since p<=q alpha+1,

    |q alpha-p| >= 1/(128 log(128) 3^q).

Hence q'<128 log(128) 3^q. For large M, take the largest convergent denominator
q<=M. It satisfies q>=c log M. The first q orbit points of the irrational
rotation have maximal circular gap <=3/q: compare with the q equally spaced
points k*p/q, using the error <1/q'<=1/q at k<q. For a fixed target and large
X, choose M of order (log X)/(2 log L); the growth factor L^M then leaves
ample space for the initial all-shrink laps J=O(log log log X). Apply (1)-(2)
with delta of order 1/log M. This proves the largest gap in [X,2X] between
B1 ancestors of that fixed target is O(X/log log X). No analytic inverse-floor
premise is needed, unlike PR25's homogeneity-based gap estimate. At the same
scale both a known target and any hypothetical exceptional target satisfy this
bound, with sufficiently large X depending on the targets.

Existing Baker/Matveev lower bounds on nonzero linear forms in log 3, log 128
(for example Matveev, *Izvestiya Math.* 64 (2000), 1217-1269,
https://doi.org/10.1070/IM2000v064n06ABEH000314) give |q alpha-p|>=c q^(-A)
for some effective finite A. This changes the convergent bound to q'<=C q^A
and the maximal rotation gap to O(M^(-1/A)). The same constructor therefore
improves the relative gap to O((log X)^(-1/A)). Constants and exponent have
not been optimized here. A better irrationality measure improves that
exponent but cannot by itself reach subpolynomial absolute block widths.
We rely on the established linear-forms theorem, not the very recent
claims of sharper logarithmic irrationality measures that need independent review.

## 4. Local power-law inverse count using a prefix-free cut

The finite positive potential at exponent gamma=17/20, precision 14, was
checked in the seven-step potential checker in the [potential directory](../potential/). Recall the actual constructive statement:
with inverse edge inflation factors A_S=2001/1000 and A_G=667/1000 and
finite positive potential f, the probability of a legal inverse path of
artificial product P is <=(f_max/f_min) P^(-gamma). Both edge factors dominate
the actual raw z ratio by a uniform factor >1. At a nonperiodic root y,
stop on first crossing T>1 of the artificial product. Every path stops:
P grows at least (1+epsilon)^k/y since actual positive height is >=1.
The stopping cut is prefix-free, all leaf heights are <= A_max*T*y, and
its cardinality is at least (f_min/f_max)T^gamma.

Choose T=X/(M_delta*A_max*y). At each cut leaf apply the new interval
constructor, with target that leaf. The leaves are <=X/M_delta. The outputs
are distinct: in a nonperiodic inverse tree a phase-tagged positive state
has exactly one path and clock to its root; different prefix-free leaves
cannot have intersecting descendant trees. This removes the logarithmic
multiplicity loss of merely transporting a cumulative count.
For a periodic original target, take one of two distinct same-clock ancestors
within six inverse ticks that is off-cycle, using the inherited branching
lemma. Its height is <=64z. The nonperiodic inverse tree is contained in the
original target's inverse set.

Consequently the checked potential theorem plus our new interval steering
prove the local bound

    # { t in (X,(1+delta)X): B(t) is an ancestor of (z,p) }
        >= c_delta (X/z)^(17/20),        X/z sufficiently large.       (3)

The constant is uniform in the target once the finite potential min/max and
mantissa constants are fixed; it can be made explicit from them. The huge
precision-14 vector is inherited evidence, not regenerated here. No linear
inverse-floor argument is used. One can similarly use shrinking relative
widths delta(X)=(log X)^(-eta) for fixed targets if eta<1/A: the rotation-net
size grows O(delta^(-A)), so M_delta=X^o(1). The cut bound then gives
X^(17/20-o(1)) ancestors per such interval, with constants understood from the
uniform constructor and Matveev bound. This is a genuine local count, not a
lower bound on the known basin proportion tending to one. Neither it nor
macroscopic homogeneity bridges the very large scale gap to the synchronized
blocks exp((log X)^gamma) from PR24.

## 5. A new completion criterion without linear inverse density

Let f(t)=1 if B(t) is captured by the known cycle, 0 otherwise, and
D={t>=1: f(t)!=f(t+1)}. If any target is uncaptured, (2) applied to that
target and to the known B1(1) shows that BOTH labels occur in every sufficiently
large fixed proportional interval. In particular D intersects every such interval:
choose both labels strictly inside a slightly narrower interval and take an
adjacent change between them. This is unconditional; it needs neither the
linear inverse count, the pair density theorem, nor a premise of positive
natural density for both basins. Conversely if every t is captured then D is empty.

**Cone criterion.** Global capture is equivalent to the existence of some
fixed delta>0 and an unbounded sequence X_i such that all B1 labels in
[X_i,(1+delta)X_i] agree. The label need not be known in advance: it must
be one by inverse hitting of B1(1). This is potentially easier to target than
finding a pointwise smaller partner for every t, but does not make it easy.
A finite verified interval alone does not establish the premise. A uniform
bound o(log log X) on the number of actual label changes in [X,2X] along
an unbounded sequence is another sufficient condition, by subdividing into
small proportional intervals using the quantitative gap theorem. With
Matveev replace log log X by a positive power of log X. These are sufficient
conditions on actual labels or sound covers of label boundaries, not on
minimum-representative candidates.

**Regular separator criterion.** Suppose a finite base-b DFA accepts a sound
overapproximation L of D, using canonical positive integer representations
without leading zeros. If some nonzero leading prefix u cannot be extended to
any accepted word, all adjacent links in the prefix cone
[u*b^k,(u+1)*b^k) are proved equal, for every k. The cone criterion implies
global capture. This is a finite automaton acceptance test (coaccessibility),
provided the inclusion D subset L has been proved on the actual integer system.
It also suffices that L has zero lower natural density. Indeed if every prefix
extends to acceptance, from each state reached by a k-digit legal prefix a
shortest accepted continuation has length at most Q-1, for a Q-state DFA.
Distinct k-digit prefixes have distinct extensions. At least (b-1)b^(k-1)
accepted integers are then below b^(k+Q), yielding positive lower density by
choosing k for each cutoff. Hence a regular zero-density overapproximation of
D cannot be prefix-dense. Equivalently, a nontrivial true basin boundary is
not contained in ANY regular zero-density language, in any base. No automaticity
assumption about f or D is made in the theorem; constructing a sound L remains
open. Standard automata closure and graph checking are enough once L exists.
See Allouche-Shallit, *Automatic Sequences*, chapter 11 (right-dense languages
and the multiplicatively independent base argument), for related classical ideas.
The proof here is elementary and tailored to this inverse hitting result.

## 6. A rigorous negative control: same-count comparisons cannot meet the cone target

PR25 defines the eventual excess-grow index I(t) of a captured B1 start:
`I(t)=lim_(m->infinity)(g_(7m)(B(t))-2m)`. It is an integer, since the
known cycle has two grows per lap. The verifier checks I(1)=2. For (1) applied
to B1(1), alignment is zero and the exact inverse history has g+3 grows
and j+g+4 laps. Thus every constructed t is already captured and

    I(t) = 2 + g+3 - 2(j+g+4) = -3-2j-g.                 (4)

Choose g even or odd using the two irrational rotation nets: every sufficiently
large proportional interval contains captured B1 parameters of BOTH index
parities. More strongly, it contains Omega_delta(log X) distinct captured
indices. To see this, let `ell=log_128(X/(K*C))`, and write the leading scale
in the band proof as `j+(1-alpha)g=ell+xi`, where xi ranges in an interval of
length <1. A translated finite g-net has the same maximum gap. Use many
disjoint blocks of G+1 consecutive g values, spaced by at least 4, through
g<=ell/2. Each block supplies a band witness and j>=J at large X. By (4),
`I=-3-2ell+(1-2alpha)g-2xi`; since 3^4<128, 1-2alpha>1/2. Distinct chosen
g's separated by >=4 give distinct I (xi difference has magnitude <1).
There are Omega_delta(log X) such blocks. Eight sample witnesses with distinct
indices in a single 50% band were independently replayed.

A same-clock equal-grow-count merger preserves I for captured inputs. Thus if
every adjacent edge between two of these distinct-index captured representatives
had such a witness, capture and equal I would propagate along the entire chain,
a contradiction. Ordering the selected representatives by size gives at least
Omega_delta(log X) distinct adjacent failures per proportional interval. This
is true whether or not global capture holds. In particular the equal-count
failure set is prefix-dense in every base and CANNOT have a regular zero-density
superset. PR24's density-one symbolic coalescence can still be true; thinness
and prefix density are compatible for nonregular languages.

There is a further format constraint. Two adjacent B1 affine rays with equal
source stride can have a uniform fixed-clock merger on an infinite ray only
if their leading multipliers agree. By unique factorization, equality of
3^g/2^k on both sides forces both clocks AND grow counts equal. The same
argument applies after any finite affine subdivision, and to any finite
composition with fixed histories after aligning the clocks. Unequal clocks
alone do not help a uniform affine comparison of equal-slope adjacent sources.
We need parameter-dependent histories, different-scale partners, or a proof
of capture-status equivalence via a justified induction (rather than a single
uniform endpoint equality). The existing R(n) relation may be useful for
this latter task, but its recursive calls must be controlled. Do not spend
resources trying to prove the cone criterion with just a flat equal-count
symbolic merger bank.

**Two-basin control.** For the separate `UTT` forcing, both known cycles
(length 3 and 9) are verified. At phase zero every residue mod3 has an
inverse three-tick lap with exactly one grow; the all-shrink lap has slope
8, fixed rational anchor <1, and the one-grow lap slope 8/3. The same
rotation proof (without the B1 adapter, using phase-zero positive heights)
gives proportional interval hitting for BOTH disjoint basins. Thus even our
stronger local theorem is not a basin-selection theorem by itself. A future
claim of much finer universal hitting must pass this control.

## 7. A finite abstraction obstruction: an exact graph test at every precision

For phase-one seven-tick sampling, take the unrestricted dyadic residue graph
modulo 2^r, r>=1, with an edge if a positive start in the source residue can
reach the target residue in seven updates. A finite excluded terminal height
region has no effect: any finite legal parity word can be lifted arbitrarily
high, keeping its full finite trace outside that region.

Every row has exactly 2^min(r,7) outputs. For r>=7, the first seven parity
bits are fixed by the input residue and the output stride is an odd integer
times 2^(r-7); for r<7, choose any compatible seven-bit cylinder and vary its
odd free output coefficient, hitting every target residue. For any r, take
k a multiple of seven with k>=r. A compatible full k-bit cylinder from any
input residue has an odd endpoint stride, so reaches every target residue
mod 2^r. The literal path proves that the graph is a single SCC. It has
branching at every vertex and an expanding self-edge at the all-grow rational
fixed point z=-420/2059, read modulo 2^r (take a lift of sufficient precision
to realize seven grow steps). This follows from the exact phase-one map
z'=(2187z+420)/128 on that branch. The verifier enumerates complete finite
row graphs through r=10 and independently checks connectivity in both
directions and the growing self-edge. The proof is for all r.

Hence a proof architecture requiring an unrestricted fixed dyadic SCC to
be unbranched or free of expanding cycles will fail at every precision. The
recent Nashida preprint on disentangled generalized Collatz maps
(https://doi.org/10.5281/zenodo.23081447; author-reported partial Lean formalization,
not independently audited here) proposes a positive criterion excluding SCCs
with both properties. This graph fails the stated positive criterion; do not
infer every claimed negative theorem of that preprint without checking its
exact definitions and hypotheses. This obstruction is independently proved
for our specific abstraction and does not prohibit mixed-adic, reachability-
conditioned, size-aware, or relational abstractions. It explains why a
larger fixed residue modulus alone is not an architecture for completion.
