# The literal finite source bridge: dictionary, reward and unique maximum

**Project owner and author: Jake S. Brusca.** ChatGPT assisted with ideas,
mathematics, Lean proofs, code, writing and separate-context AI review. This is
a personal research project and work in progress; qualified scrutiny is welcome.
No human refereeing, priority certification or external acceptance is claimed.

This written reconstruction matches all 25 frozen finite bridge targets
in [BridgeExpectedTypes](BridgeExpectedTypes.lean). It covers the
finite source-word model, exact bijections, literal rewards and finite threshold
counts. Compilation, transitive axiom checks, trusted statement comparison,
source-bound proof replay and independent checker receipts remain distinct.
No pressure, entropy, differentiability or asymptotic theorem is proved here;
in particular this package does not resolve M4, R8 or R9.

The AI context preparing this document also authored the reward and extremizer
modules. Other arithmetic, encoding, transport, recurrence and finite-count
components were developed in other contexts and reviewed here. This is not
independent authorship or independent review of every component.

## 1. Source, chronology and finite objects

The primary source is Polson–Sokolov, edition1 v1.4.0, commit
`5840497a23fc0d64127b850aea68862d7c93f2b7`,
[`book/chapters/ch10h_ratchets.tex`](https://github.com/VadimSokolov/collatz/blob/5840497a23fc0d64127b850aea68862d7c93f2b7/book/chapters/ch10h_ratchets.tex),
sections `rrt:sec:exact` and `rrt:sec:m4`, especially the admissibility paragraph
and depth recursion. The reviewed source snapshot has SHA-256
`ac6d988a18a8756897e098d768094dc8da926707fd1986e1ac90b988d565d755`
and upstream Git blob `c490d1c3da0ffe06f2a76a4f09020c60b5484015`.
These pins locate the source convention; they do not certify novelty or
transfer finite conclusions to the source's separate limiting questions.

Earlier exploratory proofs of abstract rung/endpoint and depth statements
predate this finite-target freeze. The new finite specification was separately
reviewed, revised to add unique extremality, and frozen before its accepted
finite-word implementations. Later proofs deliberately reuse selected earlier
abstract prefix, irrationality and rung lemmas after checking their interfaces.
It would be inaccurate to describe all underlying mathematical work as first
conceived after the freeze. The frozen definitions themselves import no
implementation or challenge proof. Historical UNFROZEN comments describe their
preserved preimplementation stage.

Fix a natural length r. A word is exactly an ordered tuple

    w : Fin r → Nat,      w_i≥1.

Its integer prefixes have domain Fin(r+1):

    K_t = Σ_(0≤i<t) w_i,   0≤t≤r.

There are no arbitrary values beyond r. Source words are not restricted to the
alphabet{1,2}; that alphabet arises only for the floor increments below.
The inverse prefix encoding is

    w_i = (K_(i+1)−K_i).toNat.

A positive prefix means K_0=0 and K_(i+1)≥K_i+1. Consequently differences are
positive integers, `.toNat` loses no information, and both encodings are exact
inverses. The prefix increment identity

    K_(i+1)=K_i+w_i

proves the word-to-prefix inverse. Induction on t proves the other inverse.
In fact decoding the prefix of a raw Nat-valued word recovers that word even
without positive letters; this stronger helper is useful for uniqueness.

For comparison with the earlier abstract infinite-profile predicates, extend a
finite prefix by zero outside0,...,r. Restricting the abstract conditions back
to these indices gives exactly the finite predicates used here. This zero
extension serves only predicate compatibility. It does not create infinitely
many words through irrelevant tails, and such tails are never counted.

## 2. Slope, defects, caps and strict rungs

The actual slope is

    θ = log3/log2,       1<θ<2.

The inequalities follow from2<3<4 and log2>0. The slope is irrational: a rational
relation between log3 and log2 would, after clearing denominators and applying
exponentials, give equality of a positive power of3 and a power of2, contrary
to prime divisibility. Positivity handles the signs of the cleared exponents.
Thus rθ is nonintegral at every positive integer r.

For any real θ define

    F_t = floor(tθ),
    δ_r = ceil(rθ)−rθ,
    C_(r,t) = floor(tθ+δ_r).

Always0≤δ_r<1. A strict rung is a positive r such that

    δ_r<δ_t    for every integer0<t<r.

Only POSITIVE earlier indices occur. Including t=0, whose defect is0, would
eliminate every strict rung at an irrational slope. Nor is this a record of a
normalized error or a nearest-integer distance.

At a strict rung, C_(r,t)=F_t for every0≤t<r. For t=0, this follows from
0≤δ_r<1. For0<t<r, write x=tθ and use

    x+δ_r < x+δ_t = ceil(x) ≤ floor(x)+1,
    floor(x) ≤ x ≤ x+δ_r.

Hence the two expressions have the same floor. This cap argument does not need
irrationality. In contrast, the endpoint identity

    ceil(rθ)=F_r+1

DOES require nonintegrality. A strict rung by itself is insufficient: θ=3/2,
r=2 is a strict rung with δ_2=0 and ceil(3)=floor(3).

For θ≥1, F_(t+1)≥F_t+1. Indeed F_t+1≤tθ+1≤(t+1)θ, so taking the floor gives
the inequality. If also θ≤2 then F_(t+1)≤F_t+2. Thus floor increments are in
{1,2}, although unrestricted source letters need not be.

### Unbounded strict rungs at the actual slope

For completeness, irrationality supplies arbitrarily small positive upper
ceiling gaps. Pigeonhole approximation of the fractional parts of multiples of
an irrational θ gives q≥1 and an integer p with nonzero

    d=qθ−p,       |d| arbitrarily small.

If d<0 and |d|<1, then ceil(qθ)−qθ=−d. If d>0, choose d<1/2 and let
m=floor(1/d). Irrationality makes m*d≠1. Therefore

    0<1−m*d<d,
    ceil(m*q*θ)−m*q*θ=1−m*d.

This gives the required upper gap in either sign case. The formal dependency
proves a stronger positive-return statement with index at least2; no limiting
frequency or typical-orbit assumption is used here.

Now fix a bound R. Every defect δ_t for1≤t≤R is positive, so this finite set
has a positive lower bound ε (take ε=1 if R=0). There is a positive index with
defect<ε. Let r be the least such positive index. It exceeds R, and every
positive t<r has δ_t≥ε>δ_r. Thus r is a strict rung beyond R. This proves
unbounded actual strict records, not just existence of finitely many examples.

## 3. Literal source words and their closing depth

For r>0 a literal source word is a positive word satisfying

    K_r=ceil(rθ),
    K_t≤C_(r,t),       0≤t<r.

The t=0 condition is redundant but retained. The closing endpoint r is NOT
subject to an interior-cap inequality. At EVERY positive actual length, nonintegrality gives the closing prefix
F_r+1. The literal closing-depth conclusion therefore needs no rung hypothesis.
A strict rung additionally makes all interior caps equal F_t. The literal depth

    F_t−K_t

ends at−1, not0. The original source word must not be called a zero-endpoint
floor bridge without an adjustment.

For the more general transport theorem assume θ≥1, r is a strict rung, and
rθ is nonintegral. Let the final letter be w_(r−1). The penultimate prefix is
at most F_(r−1), and the endpoint is F_r+1. Hence

    w_(r−1) =K_r−K_(r−1)
              ≥F_r+1−F_(r−1) ≥2.

This proves that subtracting1 from the last Nat letter leaves a positive
letter. Natural subtraction is total in the definitions, but its positivity
is established rather than presumed. The lower slope condition matters:
θ=1/2,r=1 is a vacuous strict record with source word(1), whose lowering
would give0 and fail positivity.

Let L(w) lower only the last letter by1, and U(w) raise it by1. On a source
word, L preserves each K_t for t<r and changes the endpoint to F_r. It gives a
positive FLOOR word satisfying

    K_r=F_r,        K_t≤F_t for all0≤t≤r.

Conversely U raises a floor word's endpoint to F_r+1=ceil(rθ) and preserves
every interior prefix/cap. Both operations preserve positive letters in the
appropriate direction. Their exact inverses are

    U(L(w))=w    on source words,
    L(U(v))=v    on floor words.

Thus they give a genuine equivalence of the finite source-word and floor-word
subtypes, with the specified maps, not merely an equality of cardinalities.
At the actual slope, its assumptions follow from the separately proved slope,
nonintegrality and rung facts.

## 4. Zero-endpoint depth bridges and the second bijection

For a floor word define

    J_t=F_t−K_t.

Then J_0=J_r=0, J_t≥0, and positivity of each letter is equivalent to

    J_(t+1)≤J_t+F_(t+1)−F_t−1.                 (1)

These are exactly the finite depth-bridge conditions. Conversely, given such a
finite integer J, put K_t=F_t−J_t. Equation(1) says K increases by at least1;
K_0=0, K_r=F_r, and J≥0 says K≤F. Its positive differences decode a floor
word. The two maps

    v ↦ (F−prefix(v)),
    J ↦ differences(F−J)

are exact inverses, for every real θ and every positive r where the respective
predicates hold. No independent feasibility or {1,2}-letter assumption is
needed for J: the inequalities themselves give positive decoded letters.

Composing with L/U yields the actual source-depth bijection at every strict
actual rung:

    source word w ↦ sourceBridgeDepth(w)=F−prefix(L(w)),
    depth bridge J ↦ U(differences(F−J)).

The lowering is part of the prescribed map. It is what repairs the source's
literal−1 closing depth; it is not a silent reinterpretation of that depth.

### Why all counted populations really are finite

For a fixed integer endpoint s, any raw Nat word with Σ_i w_i=s has each
letter between0 and s.toNat. It therefore injects into the finite tuple space
of r entries in Fin(s.toNat+1). If s<0 no such word exists, and if r=0 only the
empty word needs consideration. Source/floor words are subtypes of these
endpoint-bounded words with endpoints ceil(rθ) and F_r respectively, so they
are finite for EVERY real θ and natural r.

Every depth bridge injects into the floor-endpoint word space via
J↦differences(F−J), with inverse recovered by subtracting prefixes from F.
This also proves depth-population finiteness at r=0. Consequently the use of
Nat.card in the three counts cannot conceal an infinite set through its
zero-cardinality convention. The equivalences genuinely compare finite sets.

## 5. Exact literal reward, depth reward and rung reference

The source reward is exactly

    R(w)=Σ_(0≤t<r) 2^(K_t)/3^t.

It excludes the closing endpoint t=r. Thus both L and U preserve the reward
for EVERY raw Nat word, even one whose last letter is0, and also at r=0.
There is no factor depending on the closing defect in this invariance.

Since 2^θ=3, for every integer K and natural t,

    2^(K−tθ)=2^K/3^t.

So the literal reward equals its real-power expression term by term. For any
real θ and prefix K, the depth factorization is exactly

    2^(F_t−tθ) *2^(-(F_t−K)) =2^(K−tθ).

Apply this to the lowered word and then use endpoint reward invariance:

    R(w)=Σ_(t<r) 2^(F_t−tθ)*2^(-sourceBridgeDepth(w)_t).

This is the frozen source-depth reward identity for every raw finite word.
No source admissibility, rung condition or asymptotic correction is needed
for this algebraic identity at the actual slope.

Define

    B_r=Σ_(t<r) 2^(F_t−tθ),
    B_r^literal=Σ_(t<r) 2^(C_(r,t)−tθ).

At strict rungs the cap equality makes B_r^literal=B_r. Off rungs these are
different objects; no unrestricted equality is asserted. In particular R is
NOT divided by2^δ_r, and no closing summand is inserted.

## 6. Mechanical word, exact maximum and uniqueness

The floor increment word is v_i=F_(i+1)−F_i. At the actual slope each v_i is1
or2. Raise its last letter:

    w*=U(v).

Its open prefixes are exactly F_t. Its endpoint is F_r+1=ceil(rθ). At every
strict actual rung it is therefore source-admissible and has reward B_r.
Every other source word has K_t≤F_t for t<r. Because base2 real powers are
increasing, each of its reward terms is at most the corresponding term of B_r.
Hence R(w)≤B_r.

For uniqueness, suppose a source word has R(w)=B_r. All termwise deficits are
nonnegative, so equality of finite sums forces equality in every summand.
Strict injectivity of the base2 real exponential gives K_t=F_t for every
open prefix t<r. Reward alone cannot determine the last letter: both source
words' common closing value ceil(rθ) is also used. All r+1 prefixes consequently
agree with w*. Taking consecutive differences recovers w=w*.

Thus, among source-admissible words at a strict actual rung,

    R(w)=B_r  iff  w=w*.

This is a finite maximum/uniqueness theorem. It is not an extremal-pressure
statement, a cyclic-necklace result or an integer Collatz cycle classification.

## 7. Every real threshold is preserved exactly

The source-floor equivalence preserves reward because L changes no open
prefix. The source-depth equivalence preserves reward by the exact identity
in section5. For any real threshold q, each equivalence therefore restricts
to an equivalence of the selected subtypes satisfying q≤reward. Their finite
cardinalities are equal:

    sourceCount(r,q)=floorCount(r,q)=depthCount(r,q).

There is no restriction on q and no hidden limiting interpretation. Substituting
q=c*B_r gives the corresponding finite source N(c,r) convention at strict
rungs, with the original literal normalization. The sets contain ordered
finite words; no quotient by rotations is taken. No claim that a word is
realized by an integer periodic orbit is used or concluded.

## 8. Length-one and length-zero boundaries

At r=1, the strict-record comparison has no earlier positive index, so1 is a
strict rung. Since1<θ<2, F_1=1 and ceil(θ)=2. A source word is precisely(2), a
floor word precisely(1). Every raw length-one word has reward1, because the
only summand reads K_0=0. The source word's literal depth is(0,−1), while
its sourceBridgeDepth after lowering is(0,0). B_1=1 and sourceCount(1,1)=1.
These facts form an explicit frozen target rather than an omitted exception.

At r=0, both source and floor predicates are false because they demand r>0.
The empty reward is0. A depth profile has the one-point domain Fin1; J_0=0
forces it to be exactly the zero profile, which satisfies the depth conditions.
Thus the depth population is a singleton even though the source/floor word
populations are empty. Bijection and threshold-count claims apply at strict
positive rungs, so no zero-length equality of these populations is asserted.

A useful off-rung warning is r=2 at the actual slope. The source words(1,3)
and(2,2) have rewards5/3 and7/3. The phase-zero reference is5/3, whereas the
shifted-cap reference is7/3. This finite mismatch is why the formal reference,
bijection and count statements retain their strict-rung conditions. It is not
by itself a counterexample to any proposed asymptotic limit.

## 9. All25 frozen target mappings and assurance boundary

| Frozen target | Mathematical content / module |
|---|---|
| FiniteWordPrefixEncoding | Exact positive finite prefix/letter inverses; BridgeEncoding. |
| AbstractPrefixCompatibility | Canonical zero extension compared with the earlier predicates; BridgeEncoding. |
| DefectBounds | 0≤δ<1 for every real slope/index; BridgeArithmetic. |
| NonintegralEndpoint | Ceiling=floor+1 with explicit nonintegrality; BridgeArithmetic. |
| StrictRungCaps | All literal open caps equal floor at a strict rung; BridgeArithmetic. |
| UnitFloorIncrements | θ≥1 gives increments≥1; BridgeArithmetic. |
| FloorIncrementAlphabet | 1≤θ≤2 gives increments in{1,2}; BridgeArithmetic. |
| SourceSlopeFacts | Actual slope in(1,2), irrational; BridgeArithmetic. |
| SourceSlopeNonintegral | Every positive actual multiple is nonintegral; BridgeArithmetic. |
| SourceRungsUnbounded | Positive upper-gap returns and least new records; BridgeRungs. |
| LiteralClosingDepth | Original source word depth ends−1; BridgeArithmetic. |
| SourceLastLetterLowerable | Final source letter≥2 under stated transport hypotheses; BridgeTransport. |
| LowerRaiseTransport | Source/floor admissibility in both directions and exact inverses; BridgeTransport. |
| FinitePopulations | Endpoint bounding and depth injection, not empty Nat.card conventions; BridgeFinite. |
| SourceFloorBijection | Actual finite subtype equivalence with L/U maps; BridgeTransport. |
| SourceDepthBijection | Composition with the depth dictionary and prescribed inverse; BridgeFinite. |
| RewardEndpointInvariant | Last-letter changes preserve all open reward terms; BridgeRewards. |
| RewardRealPower | Exact integer-power/real-power identity; BridgeRewards. |
| SourceDepthReward | Exact literal-to-depth reward, without rescaling; BridgeRewards. |
| ReferenceAtRungs | Literal and phase-zero references coincide at rungs; BridgeRewards. |
| PhaseZeroExtremizer | Mechanical word admissibility, attainment and finite maximum; BridgeExtremal. |
| UniqueExtremizer | Equality forces all open prefixes plus the fixed closing endpoint; BridgeExtremal. |
| ThresholdCountPreservation | Reward-preserving selected-subtype equivalences for every real q; BridgeFinite. |
| LengthOneBoundary | Source(2), floor(1), both depths, reward/reference/count1; BridgeBoundary. |
| ZeroLengthConvention | No source/floor words, empty reward, unique zero depth; BridgeExtremal. |

[BridgeSolution](BridgeSolution.lean) supplies exactly these25
required wrappers. The independently pinned specification is the boundary of
what the formal statements assert. A fresh integration receipt must identify
all source bytes, every target and every generated-helper theorem closure;
ordinary compilation and axiom assurance are lower assurance than accepted
source-bound replay, trusted statement comparison and independent checking.
The canonical ordinary fresh integration has passed all25 target/type checks
and an exhaustive source/axiom audit of357 theorem closures. This remains
lower assurance: source-bound replay, trusted comparison and independent
project-specific checker gates are separate and pending at preparation time.
No local development check is represented here as a successful Linux gate.

Earlier written exploratory pressure/entropy/large-tilt notes and finite
computational diagnostics remain separate evidence. This finite dictionary,
even with all25 targets proved, supplies no partition-function limit,
microcanonical/variational formula, differentiability result, M4 entropy limit,
R8 resolution, R9 asymptotic or all-phase analytic transport. Those require
separate source semantics, frozen quantified statements, proofs and assurance
receipts. No such conclusion follows by renaming this finite theorem package.
