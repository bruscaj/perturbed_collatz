# Legal packets and the renewal grammar

Physical update: apply the shortcut Collatz step and then the periodic impulse
`d=(0,0,1,-1,0,1,-1)`. Set `H=(0,0,0,1,0,0,1)`, `z=n+1-H[p]`; the
positive normalized coordinate obeys `UUUTUUT`. The phase advances mod 7.
The safe domain is z>0. A pair type `(p,e,b)` denotes `(x,3^e*x+b)` at common
phase p, both coordinates positive. For e=0 use b>=0. Canonical orientation
orders the two affine slopes, breaking ties by their intercepts; it is not
necessarily numerical order at every small input. All mergers are symmetric.

## 2. Exact transition algebra and a cylinder lemma

At parity s of x, write x=2v+s. Let a=3^e, s2=(a*s+b) mod 2. Set m=3 if
s=H[p], otherwise 1, and n=3 if s2=H[p], otherwise 1. The normalized
one-tick outputs in input order are

    m*v + (m*s+s)/2,
    n*a*v + (n*(a*s+b)+s2)/2.

The two slopes are powers of three. Canonicalize as `(A*v+B,C*v+F)`
with (A,B)<=(C,F) lexicographically. Then the new type is
`(p+1 mod7, e', F-3^e'*B)` where `3^e'=C/A`, and its base coordinate is
`A*v+B`. A is an odd positive integer. The formula follows directly from
normalized U/T. The independent replay uses signed physical n instead.

**Cylinder lemma.** Start with x=a0*u+b0, a0 positive odd, restricting u to
an integer half-line on which both paired coordinates are positive. Every
finite word of canonical base parities of length k determines exactly one
residue of u modulo 2^k. On that ray the endpoint base is an affine function
of the new free parameter with positive odd coefficient. In particular each
word is feasible for arbitrarily large positive u. Proof: at each step
split the current free parameter according to the required parity. Because
its slope is odd, exactly one bit works. The two in that substitution is
canceled by the division by two in the next tick, and the new slope is odd.
Positivity follows from the physical recurrence. Any initial finite-domain
exceptions are irrelevant to density and excluded by the stated positivity.

This gives exact cylinder probabilities 2^-k for finite parity histories.
It is not an assumption of independence on the infinite trajectory of a
particular natural number. At a typed macro endpoint, conditional future
cylinder weights are again the same because the free coefficient is odd.

## 3. Repeated switching with a decreasing measure

Let D(x) be the difference-two pair at phase 2. The following whole-affine
identities hold on the full displayed domain v>=0. Word bits refer to the
canonical base parity, including orientation changes.

| Letter | Input x | Output base | Updates | Output type | Orientation | Word |
|---|---|---|---:|---|---|---|
| E | 128v+36 | 243v+72 | 7 | D | same | 0010100 |
| K | 128v+111 | 81v+72 | 7 | D | same | 1000110 |
| A | 16384v+15227 | 2187v+2034 | 14 | D | reversed | 10100001100000 |
| B | 16384v+10695 | 729v+477 | 14 | D | reversed | 10010101101000 |
| T | 8v+5 | 3v+3 | 3 | equal at phase 5 | irrelevant | 110 |

E, K and T are inherited shared-component primitives. A and B are the
new excursions: A passes through homogeneous ratio three at phase 5, B
through homogeneous ratio nine at phase 6. Both return to D, and both swap
which original trajectory is the canonical first side. The verifier checks
both signed physical whole-affine trajectories, not just numerical examples.
The five guards are mutually disjoint. A/B contract relative to the original
pair coordinate, not merely an intermediate stage.

Put C(x)=115x+468>0. For E the exact identity is

    C(E(x)) = (243/128)*C(x),
    128 | C(x) iff x=36 mod128.

It consumes exactly seven binary factors, hence a maximal consecutive E run
is finite for any positive integer. For A and B,

    7*C(A(x)) < C(x),   7*C(B(x)) < C(x).

The affine slope inequalities are 7*2187<16384 and 7*729<16384; the
constant inequalities are checked by substituting respectively r=15227
and r=10695. They hold for all v>=0. K directly strictly decreases x.

**Multi-packet theorem.** Any legal packet consisting of h>=1 E laps
followed by j>=ceil(h/3) A/B laps strictly reduces the starting x, regardless
of the order of the A and B laps. Indeed `(243/128)^3<7` and
`C_end < (243/128)^h * 7^-j C_start < C_start`. The affine coordinate C is
strictly increasing in x. The argument permits any finite number of packets
in arbitrary order (including standalone A/B/K contractions). No rank
reset between packets is assumed; x is the outer well-founded measure.

The deterministic `packet_decode` is total on x>0:

1. At each anchor take the maximal consecutive E run. It terminates by the
   positive binary counter. If zero E laps, accept T, execute one K/A/B, or
   reject as unresolved.
2. If h>0, require ceil(h/3) consecutive A/B laps (accept T earlier if its
   guard holds). Any other guard before repayment returns unresolved.
3. After a successful repayment or standalone contraction restart with a
   strictly smaller anchor x. T is a true equal phased future.

Each inner stage has a finite counter, and every completed packet decreases
the positive integer outer anchor. Thus the whole procedure returns either
`merge` with the exact clock or `unresolved` in finite time. It does NOT claim
that a successful packet is available for every x. On an arbitrary input
a refused transition is not a nonmerger or noncapture conclusion. The rank
used here establishes pair coalescence when T is reached; it does not
establish capture of the pair unless an original smaller-launch comparison
is supplied separately.

The cylinder lemma constructs infinitely many positive x for **every finite
sequence of arbitrary positive-depth packets**, choosing either A or B at
each contraction, followed by T. For example, every finite word formed by
concatenating E^h times ceil(h/3) letters A/B, and optional standalone
K/A/B, then T, is valid on a unique dyadic residue ray. Every guard in the
word holds, E-runs are maximal when followed by a non-E letter, and every
packet boundary is strictly descending. This establishes arbitrary numbers
of expansion/repayment restarts and of ratio-type changes, not just one
switch or a fixed count of stages. The arbitrary number of packets is
realized by different inputs; no single integer can execute infinitely many
successful packets.

### Exact packet-guard density

Write e=k=1/128 for the E and K guard masses, c=2/16384 for the A/B union,
and m=1/8 for T. Each successful macro transports the free coordinate with
odd coefficient, so cylinder masses multiply. For h>=1 the restart weight
of E^h followed by ceil(h/3) contractions is e^h*c^ceil(h/3). The sum is

    R = (e+e^2+e^3)*c/(1-e^3*c).

Earlier terminal success within these packets has total weight
`m/(1-c)*(e/(1-e)-R)`. At the anchor, direct success has mass m and
zero-E contraction restart mass k+c. Thus the natural density of the
successful decoder is exactly

    (m + m*(e/(1-e)-R)/(1-c))/(1-k-c-R)
    = 450359962711040 / 3546364804023923
    = 0.1269920009921241...

To justify natural density, truncate to at most N packets and H E laps per
packet. These are finite unions of cylinders. Long initial E runs have mass
at most e^H, and among N packet attempts the excluded long-run mass is at
most N*e^H by conditioning on each finite preceding prefix. After N
successful restarts the remaining mass is at most (k+c+R)^N, justified by
the convergent geometric series or its finite truncations. Let H then N
tend to infinity. This is a guard density, not known-cycle basin density.

## 4. A new B1-internal reduction on the named residual progression

Use B(t)=(6t,phase 1) in normalized coordinates, physically (6t-1,1).
Its original section rank is 8t. For t>=2 the alternate B(t-1) is positive
and strictly smaller. The first U tick initializes the difference-nine pair
`(9(t-1),9t)` at phase 2. This avoids any divisibility-by-three condition
on t. On the PR19 complement progression t=128v+19 the stronger exact
8-tick initialization is

    F^8 B(128v+18) = (243v+35,2),
    F^8 B(128v+19) = (243v+38,2).

Now the pair is type (2,0,3). Its parity word 1000110 gives a seven-tick
return to D(x), on base 128a+111, with output base 81a+72. Since
243v+35=128a+111 iff v=128w+4 and a=243w+7, the exact physical adapter is

    t=16384w+531,
    F^15 B(t-1) = (19683w+639,2),
    F^15 B(t)   = (19683w+641,2),   w>=0.

Every packet word ending in T therefore proves a genuine B1-internal
reduction with partner t-1 (rank gap 8), and equal source and alternate
clocks 15+word length in ticks. For a prescribed parity word of length l,
compute its initial D residue r modulo 2^l via the cylinder lemma, take
`w0=(r-639)*19683^-1 mod 2^l`, and w=w0+2^l*v. This gives a complete
infinite progression for every finite packet program. The verifier checks
examples on their whole affine rays, not isolated seeds. Example program
`EEE A EEEEEE B A E B T` (three positive-depth packets) merges at 144 ticks,
with the displayed first source and stride in verification.json.

Every t=128v+19 lies outside PR19's five B1 guards. The reductions proved
here are consequently disjoint from that named formal sufficient menu,
not necessarily disjoint from PR22 or other historical banks. They supply
progress, not independent capture of the alternate. One can add the new
accepted guard to the existing B1 strong-induction interface after
formalization. Failure to satisfy the guard does not mean noncapture.

## 5. The broader 28-type renewal grammar

Take as core types the seven shared modes of PR21, their five
nonhomogeneous exit types, the homogeneous ratio-three and ratio-nine types
at all seven phases, and (2,0,9),(2,0,3) for the B1 neighbor adapters. This
is 28 distinct types. The horizon is 14 ticks, matching the prior terminal
bank. From a core, take at least one tick; stop at the first equal affine
pair, the first core reentry, or after 14 ticks. A noncore endpoint at the
horizon is explicitly unresolved. A core reentry restarts with horizon 14,
with no restriction on the number or direction of such reentries. A
symbolic equality `(e,b)=(0,0)` is the success condition; isolated equality
at particular small values of x is not counted in the language.

For source s, let N(s,t), M(s), X(s) be counts of the 2^14 residues classified
as first reentry at t, merge, or unresolved. The whole-affine row verifier
reconstructs these counts independently by starting on x=2^14*v+2^14+r
for every r, and applying literal signed physical dynamics to both sides.
It checks 28*2^14 = 458752 entire rays, including phases and positivity. The
other implementation counts parity paths with unused-bit multiplicities.
The two matrices agree exactly. Because minimal-prefix branches have odd
endpoint stride, the transition fractions can be multiplied on successive
visits, even when the macro lengths differ.

The exact successful-language natural densities solve the rational system

    2^14 P(s) = M(s) + sum_t N(s,t)*P(t).

The finite matrix calculation proves that, from any core, the probability
mass of still being live after two macro visits is at most

    alpha = 26837/32768 < 1.

Consequently the density of surviving 2N macro visits is at most alpha^N.
Every finite truncation consists of finitely many binary cylinders. Squeezing
the limiting merge set between finite accepted and finite accepted plus
surviving sets proves existence of the natural density, equal to the unique
rational solution above. It also proves that the permanently live inputs
have upper natural density zero. **It does not show that set is empty.**
The computation is an exact infinite-language density calculation, not a
finite seed census or a claim of deterministic convergence of the general
renewal decoder. A finite accepted path is a merger witness; a bounded
execution returning live is not a rejection theorem.

The following exact fractions are in verification.json. Decimal percentages
are rounded for interpretation.

| Initialization | Parameter domain | Successful grammar density |
|---|---|---:|
| B1: ratio-three, original W comparison | all t>=1 | 40.739851% |
| A3 difference-two, t=16u+4 | u>=0 | 31.523435% |
| N03 difference-three, s=512v+145 | v>=0 | 20.526638% |
| B1 neighbor t-1 | t>=2 | 14.165421% |
| B1 neighbor on t=128v+19 | v>=0 | 19.254724% |

For B1 ratio three, the alternate is (z,p)=(3t,2), with rank gap t, not
a B1-internal reduction unless 3 divides t. On those divisible parameters,
B(t/3) reaches the alternate in one tick and gives a strictly smaller B1
partner. The neighbor comparison has no such restriction. A3 and N03 retain
the original smaller-W launches from PR19/21 (gaps t+2 and 28s+6). Their
initializations are replayed in the consumer. All densities concern only
this grammar's merger guard on the listed parameter, not basin density or
union coverage over all prior certificates.

On the named t=128v+19 class, the fraction 19.254724% is disjoint from the
five-way PR19 guard. Its contribution in the full B1 parameter is
P((2,0,3))/128, about 0.15043 percentage points. The broader grammar also
contains the packet decoder's successful language because its individual
macros last at most 14 ticks between core states. These two densities must
not be added. No net novelty comparison against PR22's complete selector
has been performed.

### All seven shared exits: full composition and explicit unbounded rays

The shared modes in cyclic order are
`(2,0,2),(3,0,3),(4,1,5),(5,2,3),(6,1,2),(0,1,2),(1,1,3)`.
The internal parities are `(0,0,1,0,1,0,0)`; the counter is `115x+c_i`
with offsets `(468,702,351,118,177,208,312)`. Every internal tick halves
this positive counter times an odd integer, so its exact valuation is the
internal-run length. The full seven-exit adapter now uses the renewal
continuation at each exit, including the full homogeneous ratio-three and
ratio-nine terminal languages of horizon 14 and arbitrary common even
prefixes (all homogeneous phases are core). A prior uniform terminal
within 14 ticks cannot fail this grammar: stopping at intermediate core
states only restarts the horizon. Singleton corrections are excluded.
In particular exit 6 gives ratio nine at phase two, as requested in PR22.

| Exit mode | Explicit terminal pre-exit x | Ticks from exit | Conditional renewal success after exit |
|---|---|---:|---:|
| 0 | 8a+5 | 3 | 42.520232% |
| 1 | 32a+27 | 5 | 20.749177% |
| 2 | 64a+46 | 6 | 19.997349% |
| 3 | 128a+97 | 7 | 7.273294% |
| 4 | 16a+14 | 4 | 31.928379% |
| 5 | 8a+5 | 3 | 49.915115% |
| 6 | 128a+117 | 7 | 12.520071% |

Each row's physical equality is checked over a>=0. Since A3/N03
initialization base has odd parameter coefficient, for **every** exact
internal-run length j, its appropriate mode's terminal congruence is
realized on an infinite input ray (cylinder lemma). At least one
arbitrary-depth merger construction is therefore available at every
possible shared-component exit, not just the previously studied exits 5/6.
The clocks from the original two launches are the original initialization
clocks (6/4 for A3, 12/9 for N03) plus j plus the terminal clock in the
row. For an arbitrary renewal continuation, use j+1+its own accepted
clock instead. Original rank gaps never change.

The exact solution also satisfies the independent geometric formula for
all shared modes i:

    P_i = sum_{j=0}^6 2^(-j-1) P(exit_target(i+j)) / (1-2^-7).

The proof conditions on the exact first exit depth; the endpoint after
that exit has odd free coefficient on its parity cylinder. This is a new
all-depth adapter including all seven exit types. It is not exhaustive
successful exit coverage; every conditional percentage is less than 100.
