# Affine-pair coalescence and minimum representatives

The pair-chain idea and ordinary-Collatz density-one coalescence are prior art,
not a novelty claim of this continuation. Relevant references:

- Garner (1985), [On heights in the Collatz 3n+1 problem](https://doi.org/10.1016/S0012-365X(85)80020-0).
- Gao (1993), [On consecutive numbers of the same height in the Collatz problem](https://doi.org/10.1016/0012-365X(93)90240-T).
- Said Duran (27 September 2026), [Consecutive integers coalesce with density one under the Collatz map](https://doi.org/10.5281/zenodo.23003524), and reported Lean archive [23003500](https://doi.org/10.5281/zenodo.23003500).
- Leen (9 October 2026), [Exact rates in Collatz synchronization](https://doi.org/10.5281/zenodo.23268751), [Quantitative synchronization of Collatz trajectories](https://doi.org/10.5281/zenodo.23268755), and [Late synchronization and the geometry of Collatz families](https://doi.org/10.5281/zenodo.23268753).
- Lyapunov Weaver (9 November 2026), [Synchronization of growing Collatz blocks and selected references](https://rstation.ai/problems/collatz/papers/124/v1), especially the stopped-prefix numerator representative argument, prefix conditioning, and telescoping family tail. The [attribution correction](https://rstation.ai/r/collatz/posts/20) credits the ordinary-map square-root tails to Leen.

The last manuscript and its attribution discussion were read. The direct DOI
records of the recent Duran/Leen preprints were inaccessible in this environment;
we did not independently rebuild their formal artifacts or assert peer-review
status. The phase-dependent proof below is self-contained in its arithmetic and
probability steps. Its quantitative bounds are deliberately weaker than the
reported ordinary-map rates. The stopped-prefix block argument is adapted from
the cited manuscript, with a separate phased B1 numerator and modulus. No claim
of literature priority for the phase extension is made.

## 1. Exact normalized pair chain

For a finite periodic binary schedule H, define physical impulses
`d[p]=H[p+1]-H[p]`, with phase advanced modulo the period. Normalize by
`z=n+1-H[p]`. For z>0 the normalized rule is

    G_p(z) = (3z+H[p])/2   when z mod 2 = H[p],
             (z+1-H[p])/2 otherwise.

Equivalently the branch with z parity s has form `(m*z+s)/2`, m=3 if
s=H[p], otherwise m=1. Our main H is `(0,0,0,1,0,0,1)`. The control H is
`(0,1,1)`, giving impulses `(+1,0,-1)`. H=(1,) is ordinary shortcut Collatz
in the positive z coordinate. The argument will use a small terminal table
for these three schedules, not assert a theorem for every binary word.

A canonical type is `(p,e,b)` representing the pair `(x,a*x+b)`, a=3^e,
e>=0; when e=0 require b>=0. Canonicalization orders the two affine slopes
and, if they agree, their intercepts. Negative offsets for e>0 are allowed;
for each finite word the free parameter can be taken large enough that
both coordinates are positive. At a parity s of x the other parity is
r=(s+b) mod 2. Write m,n for the two branch multipliers (1 or 3). Before
canonicalization the new ratio and offset are

    a' = n*a/m,
    b' = (n*b+r-a'*s)/2.                         (1)

If a'<1, swap sides, replacing (a',b') by (1/a',-b'/a'). If a'=1 and
b'<0, swap to make the offset nonnegative. Formula (1) follows by writing
x=2v+s and subtracting a' times the first output from the second. The
canonical endpoint's free coefficient is odd and positive on every
minimal parity cylinder, as in PR23. Every finite sequence of canonical
base parities fixes exactly one residue modulo 2^k of any initial free
parameter with odd coefficient. Its next free coefficient is odd.

Thus we can put the uniform binary-cylinder measure on the infinite word
space. Conditional on any finite history the next canonical parity is
fair. This constructs a countable-state Markov chain of *types*. It is
not an assumption that the parity sequence of an individual positive
integer is independent. Both slope and intercept must coincide for
symbolic merger: the absorbing type is e=b=0 (any phase). Isolated point
equalities with unequal slopes are deliberately not counted. The chain
may be continued as an absorbed process after merger.

## 2. A uniform contracting offset moment

Define the orientation-invariant normalized offset and its square root

    M = |b|/(1+a),       Y = sqrt(M).

Even before canonicalization the same formula is invariant under
swapping the pair. Equation (1) gives

    M' <= f_s M + 1/2,
    f_s = n*(1+a)/(2*(1+a')).                    (2)

The additive bound follows from |r-a's| <= 1+a'. If b is even, m=n and
f_s is one of 1/2,3/2, each with probability 1/2. If b is odd, the two
factors are

    f_+ = 3*(a+1)/(2*(3*a+1)),
    f_- = 3*(a+1)/(2*(a+3)).

Their sum is 6(a+1)^2/((a+3)(3a+1)) <= 2 and their product equals
3/8 times their sum. Therefore

    ((sqrt(f_+)+sqrt(f_-))/2)^2 <= (2+sqrt(3))/4.

The same bound is exact for the even-offset pair of factors. Use
sqrt(u+v)<=sqrt(u)+sqrt(v), sqrt(1/2)<=1 and
sqrt((2+sqrt(3))/4)<97/100 to obtain the uniform one-tick estimate

    E[Y' | current type] <= rho*Y + 1,    rho=97/100.      (3)

All constants are independent of phase and exponent. This alone does
not give recurrence to a finite set because e can wander arbitrarily high.

## 3. Embed at changes of the ratio exponent

An even offset leaves e unchanged. An odd offset changes e by +1 or -1
with equal probability for e>0; at e=0 it moves to e=1. If a downward
move produces e=b=0, the pair is absorbed. The next such move occurs
almost surely in finite time from every nonabsorbed type, as follows.

At e>0 let L=v2(3^e-1) (L=1 for odd e and L=2+v2(e) for even e, by the
factorization of powers of 3). While b is even, formula (1) specializes to

    2b' = m*b + s*(1-3^e).

If 0<v2(b)<L, either parity reduces v2(b) by one. If v2(b)>=L,
including v2(0)=infinity, at least one choice (s=0 at equality, s=1
strictly above) enters valuation L-1. The waiting time to enter below L
is stochastically bounded by geometric(1/2), mean two. It then takes
at most L-1 ticks to make b odd, plus one tick to change e. For tau the
number of ticks through the next exponent change,

    E tau <= L+2 <= e+3   (e>0).                          (4)

At e=0 and b>0, the even-offset formula is b'=m*b/2, so exactly v2(b)
unchanged-level ticks precede the next change; tau=v2(b)+1.

The sign of the next level change at e>0 is fair conditional on the
starting history, by conditioning at its final odd-offset tick. It need
not be independent of the offset or of its holding time. For the embedded
chain, sum (3) through tau capped at N. Since at least one tick is taken,
we keep the first contraction term and drop the subsequent nonpositive
terms. Fatou as N tends to infinity gives

    E[Y_embedded_next] <= rho*Y + E tau.                 (5)

No independence between the holding time, the exponent direction and
Y is assumed in this bound.

## 4. A proper Lyapunov function with a finite hitting-time bound

For the embedded chain use

    V(e,b) = sqrt(e+256) + Y/(e+256)^3.

This is proper on the countable state space (finite phase set): if V is
bounded, e is bounded and then so is |b|. For e>=1 write x=e+255>=256.
The conditional mean change of f(e)=sqrt(e+256) is at most
`-1/(8*(x+2)^(3/2))`, by the second derivative bound over [e-1,e+1].
The offset weight at either new level is at most 1/x^3. From (4)-(5),
`rho*(257/256)^3<1`, so the coefficient of the old Y in the expected
increment of V is nonpositive. The additive contribution is at most
(e+3)/x^3<=1/x^2. Since x>=256, x+2<=5x/4 and
`(32/3)^2*(5/4)^3<256`, we have

    E[V_next - V] <= -1/(32*(e+257)^(3/2))    (e>=1).     (6)

For e=0 and b>=2^60, let m=floor(log2 b). Then Y=sqrt(b/2)>=2^29,
and tau<=m+1<=Y/100. The latter holds at m=60 and persists because
sqrt(2)>(m+2)/(m+1). The level increases to one, the weight of Y decreases,
and sqrt(257)-16<1/32. Thus

    E[V_next - V] <= 1/32 - Y/(50*256^3) < -1/2.         (7)

Define the finite set K0 to be e=0, 0<=b<2^60, at all phases. It includes
absorption. The large finite bound is a proof convenience, not a proposed
enumeration. Stop the embedded chain at K0 or V>=R, R>=17. Outside those
sets the expected drift is at most `-1/(64*R^3)` by (6)-(7), since
V<R implies e+257<R^2+1. Summing the drift up to the stopped index
truncated at N gives expected index <=64*R^3*V_initial in the limit and
probability of reaching V>=R before K0 <=V_initial/R. These follow from
nonnegativity of V and the stopped expectation inequality; unbounded
optional stopping is not assumed. In particular this stopping index is
finite almost surely.

Before the stop, the expected number of physical ticks per embedded step
is at most J(R)=50+2*ceil(log2 R). For e>0 use L+2<=4+log2 e and e<R^2;
for e=0, b=2Y^2<=2^49 R^2, so v2(b)+1<=50+2 log2 R. Summing conditional
holding times (the event of not having stopped is known at the start of
each step) bounds expected tick time to the stop by
`64*R^3*J(R)*V_initial`. Hence the first tick time tau_K to K0 satisfies

    P(tau_K > n) <= V_initial/R + 64*R^3*J(R)*V_initial/n. (8)

For R<=V_initial the right hand side already exceeds one; if starting
in K0 the claim is trivial. Choosing R of order (n/log(n+2))^(1/4), with
small n absorbed in the constant, proves

    P(tau_K > n) <= C*V_initial*(log(n+2)/(n+1))^(1/4).     (9)

This both proves almost sure hitting and gives a uniform tail in terms
of V. It is a deliberately elementary, nonoptimal estimate.

## 5. Every type admits an explicit finite merging word

This is an accessibility statement: the word determines a residue ray,
not a freely chosen parity history for a fixed integer.

First, from e>0 use the valuation rule of section 3 to choose bits making
b odd, then choose the parity for which the first side grows and the
second shrinks, decreasing e by one. Repeat to reach e=0 (or merger).
At e=0 an even b>0 is halved by choosing both shrinking branches.
For odd b>=7, one tick gives e=1 and offset of magnitude at most
(3b+3)/2. While that offset is even with magnitude >=4, choose both
shrinking branches: b' = b/2-s, strictly decreasing magnitude. When it
is even with magnitude <=2, choose s=0 for b=+/-2 or s=1 for b=0;
this makes it odd of magnitude at most three. At the first odd offset,
choose the downward exponent move. Its canonical equal-slope offset
is at most (|b'|+1)/2, thus at most (3b+5)/4 < b. The entire excursion
strictly decreases the original positive equal-slope offset. Induction
reduces to b<=5. No choice of H is needed in this descent argument.

The following are the canonical parity words for 1<=b<=5. They were
constructed by finite search and independently verified on whole signed
physical affine rays; the long-offset descent above is a proof, not an
extrapolation from these terminal checks.

| H | phase | b=1 | b=2 | b=3 | b=4 | b=5 |
|---|---:|---|---|---|---|---|
| UUUTUUT | 0 | 110 | 10010 | 10110 | 11110 | 11110 |
| UUUTUUT | 1 | 0010 | 1110 | 0100010 | 1110 | 0001110 |
| UUUTUUT | 2 | 110 | 110 | 000110 | 100010 | 100110 |
| UUUTUUT | 3 | 10 | 00010 | 11010 | 01110 | 0100110 |
| UUUTUUT | 4 | 0010 | 1110 | 100110 | 1110 | 110100 |
| UUUTUUT | 5 | 110 | 110 | 11110 | 10110 | 0111110 |
| UUUTUUT | 6 | 10 | 0110 | 010110 | 010010 | 010110 |
| UTT | 0 | 1010 | 1010110 | 1110 | 1010 | 11011 |
| UTT | 1 | 010110 | 010 | 00000001 | 001010 | 0011 |
| UTT | 2 | 10 | 01010 | 01110 | 01010110 | 01110 |
| T | 0 | 001 | 0001 | 010001 | 00001 | 00001 |

Every state of K0 has a finite word; there is therefore a uniform finite
maximum length L0, and a positive probability epsilon=2^-L0 to absorb
within L0 ticks from every K0 state. One need not enumerate K0 to justify
existence of L0; the constructive descent supplies each word. After a
failed trial of length L0 the possible types form a finite set K1 (each
state has two successors); its maximum V is finite. By (9) the next visit
to K0 is almost surely finite. Repeat trials using the Markov property.
The probability of failing N trials is <=(1-epsilon)^N. This proves
absorption almost surely. For a quantitative bound take N of order
log(n+2), with the implicit constant at least 1/epsilon, so N*L0<=n/2
for large n. Use (9) on each of the N waits with cutoff n/(2N). A union
bound on long waits and failed trials gives, with a finite constant C
uniform in the initial type s,

    P_s(sigma>n) <= min(1,
       C*(1+V(s))*(log(n+2))^(3/2)/(n+1)^(1/4)).         (10)

Constants in this proof may be very large. This is a theoretical tail,
not a calibrated practical cutoff. The ordinary-map literature reports
stronger square-root tails; (10) is a self-contained phased extension.

## 6. Natural-density-one symbolic merger and B1 reduction

Finite successful paths are exact dyadic cylinders. Every finite union
has the density given by its cylinder weights. By (10) the lower density
of their union is at least 1-epsilon for every epsilon>0, so its natural
density is one. A fixed progression with even stride forces finitely many
parity bits; after removing those powers of two the free coefficient is
odd. Odd factors only permute residues. Thus the result holds in every
fixed arithmetic progression of the free parameter, for any fixed
positive affine source slope and slope ratio a power of three (reorder
slopes if necessary), with a common phase. The finite path may discard a
finite nonpositive boundary when a negative offset is used. It applies
to all PR23 initializers, including B1 neighbors on t=128v+19. The complete
symbolic merger language has density one; the earlier 19.254724 percent
was the density of a particular truncated/restarting grammar only.

For B(t)=(6t,phase 1) in normalized coordinates, B(t-1) and B(t), t>=2,
become (9(t-1),9t) at phase two after one tick. The root is (2,0,9) with
odd coefficient in t. Consequently for density-almost every t>=2,
there is a finite true same-clock merger with the strictly smaller B1
launch t-1. This is a smaller-parameter reduction, **not unconditional
capture**. The same result holds for any fixed number of B1 neighbors by
intersecting their density-one guards and appending ticks to align their
meeting clocks. In particular the number of guard types no longer
measures how far we are from exhaustive almost-everywhere coverage.

The verifier computes rigorous finite-horizon lower bounds as a diagnostic:
propagate exact integer cylinder masses, keep at most 12,000 live types,
and never credit discarded mass. At 14 ticks (no discarded mass) the
B1-neighbor, 19-mod128 neighbor initializer and A3 difference-two root
fractions are respectively 8.313%, 14.026%, 25.677%. At 128 ticks the
certified lower bounds are 32.217%, 35.630%, 44.888%. The latter are not
exact full-horizon fractions and not comparable as net novelty against
all earlier banks. The density-one proof is not extrapolation from these
finite values.

## 7. A separate deterministic prefix attack: O(X^(29/30)) minimum candidates

This argument does not need the probability recurrence theorem. Work
after B1's mandatory initial step, so the source is x=9t, phase two.
For any length k bit word w (actual parity bits of this source), let g_j
be the number of growing branches before step j, g=g_k, and s_j its bit.
Then the exact endpoint is

    z_k = (9*3^g*t + N(w))/2^k,
    N(w)=sum_{j=0}^{k-1} 2^j*s_j*3^(g-g_{j+1}).            (11)

Every word is one residue of t mod 2^k, by odd free coefficient; also
`t=-N(w)*(9*3^g)^(-1) mod2^k`. Distinct words of the same (k,g) have
distinct N. Group all words at k by `(g, N mod (9*3^g))`. Choose the
maximum numerator Nmax in each group. For every nonmaximum word let

    d=(Nmax-N)/(9*3^g)>0.

Equation (11) proves counted fusion with B(t-d) after k+1 ticks, because
substituting t-d satisfies the unique alternate residue for the maximum
word. This is a whole-affine identity wherever t-d is positive. Since
`N/3^g <= sum_{j<k}2^j < 2^k`, every d<2^k/9. In particular all t>=2^k
with nonmaximum prefix have a positive strictly smaller partner. This is
also a usable finite selector; it may be expensive at large k.

The maximum-representative language is prefix-closed: if a prefix is not
maximum, its smaller partner has the identical phased endpoint and growth
count. Appending the same suffix to both histories preserves equality and
the positive displacement. The new numerator gap is `9*3^(new g)*d`, so
no extension of the original prefix is maximum. A hypothetical minimum
uncaptured B1 parameter t must lie in this tree through every depth k
with 2^k<=t. The complete complementary language is an arithmetic object,
not a finite list of frontier labels.

The number of representatives at length k is at most

    9*sum_{g<=17k/28}3^g + sum_{g>17k/28} binomial(k,g).

The first sum is <=(27/2)*3^(17k/28) < (27/2)*2^(29k/30), using
`3^510<2^812`. For the second, all words have fair growth bits because H
is fixed and parity bits give every word. With tilt z=17/11, the binomial
Chernoff bound is `2^k * (((1+z)/2) / z^(17/28))^k`.
The exact rational inequality
`2^28*((14/11)^28/(17/11)^17)^30 < 1` bounds this by 2^(29k/30).
Thus fewer than `15*2^(29k/30)` maximum representatives suffice.
On the dyadic shell 2^M<=t<2^(M+1), take k=M. All residues occur exactly
once, and d<t. Summing shells proves

    # {t<=X with no certified positive smaller same-clock
          equal-count B1 partner by 1+floor(log2 t)} = O(X^(29/30)).    (12)

For k=floor(c*M), any fixed 0<c<=1, the bound becomes
O(X^(1-c/30)), and a certified partner differs by less than t^c/9.
All of these bounds count failure of a sufficient selector, not failure
of capture. Other ranks, unequal clocks and isolated equalities are not
included in its complement. No novelty claim relative to every prior
bounded certificate is made.

Exact word counts (k excludes the mandatory initial tick):

| k | all words | maxima | nonmaxima |
|---:|---:|---:|---:|
| 7 | 128 | 125 | 3 |
| 10 | 1024 | 946 | 78 |
| 14 | 16384 | 13479 | 2905 |
| 18 | 262144 | 179935 | 82209 |
| 20 | 1048576 | 656092 | 392484 |

The consumer independently replays every source ray and every nonzero
smaller-partner witness through k=14. Larger horizons use the exact
numerator formula and residue bijection, with no separate physical
replay claim. At k=20, 3393/8192 of the residue lifts of t=19 mod128 and
134/4096 of t=17 mod256 are nonmaxima; all lifts with t>=2^20 have the
stated strict B1 progress. These figures are scoped to this selector only.
The verifier also tests prefix containment across the reported depths.

**Unavoidable delay.** For any h>=1, every positive t satisfying

    2059*t+70 = 0 mod 2^(7h-1)

has an all-growing history of 7h physical ticks from B(t). Indeed the
seven-step all-grow map from phase one is `(2187*z+420)/128`; the
counter 2059*z+420 is multiplied by 2187/128. The congruence ensures
integrality of the final affine formula, hence of every previous grow
step (a noninteger dyadic denominator cannot be canceled by multiplication
by an odd integer and a further division by two). Thus all parity guards
hold. For every smaller same-phase positive launch y<6t, at each such
tick its actual output is at most its affine grow envelope, strictly
less than that of the source. So no smaller same-phase seed, even one
chosen adaptively, can meet the source synchronously during that prefix.
This is an entire infinite ray for every h, not a diverging orbit.
The all-grow infinite periodic parity ray has a negative rational fixed
point in the dyadics; it does not supply a positive integer exception.
No fixed synchronous horizon can prove universal progress by these
comparisons alone. Unequal-clock reductions are not excluded by this
obstruction.

### Exact max-plus query, without enumerating the cover

For a given group `(k,g,r)`, with `0<=r<9*3^g`, let M(k,g,r) be its maximum
numerator, or undefined when the group is empty. At k=0 the only defined
value is M(0,0,0)=0. For h=H[(2+k-1) mod7] and d=2^(k-1), there are at most
two possible predecessor candidates:

    shrink: M(k-1,g,(r-d*(1-h)) mod (9*3^g)) + d*(1-h),
    grow:   3*M(k-1,g-1,((r-d*h)/3) mod (9*3^(g-1))) + d*h.

The first requires g<k; the second requires g>0 and r-d*h divisible by
three. Ignore undefined predecessor values and take the maximum of the
remaining candidates. This is an exact recurrence: within a branch the
modular map is injective on its predecessor residue classes, and its
numerator map is increasing. The maximum candidate therefore suffices.
Induction gives the group maximum without enumerating all 2^k words.

`prefix_selector.py` queries only the states needed for a given B1 parity
prefix, memoizes values, and stops at the first positive smaller partner.
It respects k<=floor(log2 t), imposes a finite 400-depth implementation
cap and a configurable node budget, and independently replays every
successful witness on its entire affine source/partner ray. A failed or
resource-limited query is explicitly unresolved. The consumer matches
7,425 independently enumerated group maxima through k=12. It is not
claimed polynomial-time or universally successful.

A concrete result on the named difficult t=17 mod256 family:

    t=131072v+148753, u=t-1, v>=0,
    F^18 B(t)=F^18 B(u)=(177147v+201045,phase5).

This is one of four accepted residue rays at depth k=17 inside that
progression. The other three bases (with the same stride) are 231441,
234257, and 247825, with partner drops 6, 1, and 5. All are outside the
five-way PR19 guard, as every t=17 mod256 is. No complete comparison to
PR22's larger selector is made. On t=2^128+19, the query constructs the
partner t-12 at clock 46 using 92,596 memoized nodes. This also proves the
whole affine ray of stride 2^45; t=2^256+19 belongs to that ray. The
similarly sized t=2^128+17 and 2^256+17 reached the 250,000-node cap
without a certified result; these are honest implementation limits,
not counterexamples. Use `python3 prefix_selector.py --t INTEGER` to
query a new seed, or run without arguments to reproduce the receipt.

## 8. Growing blocks and the local hitting bridge

We adapt the stopped-prefix method of the cited growing-block manuscript
to the phased B1 numerator. First obtain a prefix-conditional bound
from (10). From (2), each individual f_s<=3/2, so Y after m ticks is at
most C0*(sqrt(3/2))^m starting at the fixed B1-neighbor type; e<=m.
Allow a further 8m ticks of burn-in using (3). Since
`rho^16*(3/2)<1`, the conditional expected Y is bounded uniformly,
and e<=9m. Thus the conditional expected V is O(sqrt(m+1)). For every
actual prefix of length m, by the cylinder lemma and (10), and n>=20(m+1),

    P(sigma>n | prefix) <= C*sqrt(m+1)*log(n+2)^(3/2)/(n+1)^(1/4). (13)

Conditioning on the source's actual first m parity bits is legitimate:
it fixes its residue modulo 2^m, also fixes the paired-type prefix, and
leaves the fresh free coordinate odd. The bound holds on each prefix,
so it holds under arbitrary prefix selection without an independence
assumption.

For block width D sufficiently large put m=128*ceil(log2 D),
L=(D-1)/m>1. Stop the source bit word at the first k with
`R_k=2^k/3^g >= L`, or fail if not reached by m. At first crossing
L<=R_k<2L, hence at a fixed k there is at most one possible g. Formula
(11) gives N/3^g <=sum_{j<k} R_j <=mL. In each group of stopped words
with fixed k,g and N modulo9*3^g choose the **minimum** numerator (not
maximum as in section 7). Every other word has a counted-fused
*larger* B1 sibling B(t+d), with integer 0<d<mL/9<D, by tick k+1.
Representatives at each k have mass at most 9/R_k<=9/L.
If g_m<=7m/12 then R_m>=2^(m/16) (use 3^28<2^45), which exceeds L.
For the binomial upper tail use the exact tilt 7/5:
`8*((6/5)^12/(7/5)^7)^16<1` proves P(failed crossing)<=2^(-m/64)<=D^-2.
Thus the prefix event F_D of no such guaranteed right sibling satisfies

    P(F_D) <= D^-2 + 9*m^2/(D-1).                        (14)

This event is measurable in the first m input bits. Every counted
fusion claim is an exact integer identity on its entire positive ray.

Let theta_D(n) be the probability that the D B1 starts t,...,t+D-1
have not symbolically fused at common physical time 1+n, under Haar
measure on t. By translation invariance of the binary-cylinder measure
and persistence of counted fusion,

    theta_D - theta_(D-1)
     = P(first adjacent edge not fused, suffix of D-1 starts fused).

When n>=m the event on the right is contained in F_D: if the first
start has a right sibling already fused by m, and the suffix is fused
by n, transitivity forces fusion of the full block. For n>=20(m+1),
apply the prefix-conditional adjacent bound (13) on every prefix in
F_D and use (14). This gives an increment at most
`C*(1+log D)^(5/2)*log(n+2)^(3/2)/(D*(n+1)^(1/4))`.
Telescope for 2<=j<=D. The finitely many small widths use the scalar
bound; for n below the required constant times log D the resulting
bound is trivial after enlarging C. The result is

    theta_D(n) <= min(1,
       C*(1+log D)^(7/2)*log(n+2)^(3/2)/(n+1)^(1/4)).     (15)

This is an adapted growing-block theorem, weaker than the reported
ordinary-map bound but proved with this phased chain. On the shell
2^M<=t<2^(M+1), use n=M and the maximum prescribed width over the shell.
All parity cylinders of length M have their exact Haar frequencies there.
If D(t)<=exp((log t)^gamma) with any fixed 0<gamma<1/14, the right-hand
side of (15) tends to zero. Summing shells (also bounding the last partial
shell by the entire shell) proves that a natural-density-one set of B1
anchors has all its D(t) starts coalesce by common clock 1+floor(log2 t).
This is a deterministic statement about a set of integer starts, not a
randomness assumption about any one integer.
