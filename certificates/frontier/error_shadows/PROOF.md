# New attack: integer-specific error elimination and contracting rational shadows

Let P(z) denote eventual known-cycle capture at phase 2, A(n)=27n-22, and e(n)=P(n) XOR P(A(n)). Work with f(u)=P(u+1), u>=0, and h0(v)=f(v), h1(v)=f(3v+1), h2(v)=f(3v+2), h3(v)=f(9v+7). These have captured bases h_q(0)=1. The pinned identities read

    h_q(3v+d) = h_delta(q,d)(v) XOR XOR_{(a,b) in S[q,d]} e(av+b).

All a,b are positive. The phase advance is p -> p+1 mod 7; H=(0,0,0,1,0,0,1), signed impulses (0,0,1,-1,0,1,-1), and normalized z=physical n+1-H[p]. The normalized tick is (m*z+s)/2 with s=z mod 2, m=3 iff s=H[p], otherwise m=1. The cycle in normalized coordinates is (1,1,1,1,2,3,2). Never apply the ordinary Collatz map in place of this model. PR27 proves that elimination of all e errors implies capture (using the digit identities and bases).

## 1. Closed form of the state machine

The twelve transitions are exactly delta(q,d)=floor((4d+q)/3). Therefore reading the j least-significant ternary digits of b, 0<=b<3^j, sends initial state q to

    floor((4b+q)/3^j).

Proof: induction by the integer floor-of-floor identity. The case j=0 is the identity. This does not assert that the associated error support vanishes. It allows us to compare final digit states without enumerating every possible prefix. 39,364 exact finite checks cover j=0,...,8 and all initial states and suffixes.

For j>=1, at most three suffixes b can make the resulting state depend on q: the cells containing an interior quarter boundary, since 3^j is odd and q ranges from 0 to 3. In particular, starting in state zero, adjacent inputs u,u+1 have the same j-step quotient and final state except at the three quarter crossings and the single carry residue modulo 3^j. Their labels coincide when neither digit path encounters an actual nonzero error dependency.

Conditional boundary-count upgrade. Suppose E(X)=#{n<=X:e(n)=1}=O(X^theta), 0<=theta<1. Let D be the union over the finite dependency maps of {v>=0:e(av+b)=1}. Each map is injective, so #D intersect [0,Y]=O((Y+1)^theta). For 1<=3^j<=X, adjacent disagreements for f are bounded by

    O(X/3^j + X^theta * 3^(j*(1-theta))).

Indeed the four exceptional residues account for at most 4(X/3^j+1); for each i=1,...,j, a defective quotient floor(u/3^i) or floor((u+1)/3^i) accounts for at most 2*3^i O((X/3^i+1)^theta) inputs. Sum the geometric series. Choosing 3^j within a constant factor of X^((1-theta)/(2-theta)) yields boundary count O(X^(1/(2-theta))). This is a conditional improvement of the boundary-count route, not a proof of the premise on actual invariant errors and not by itself a capture proof.

## 2. Contracting rational-shadow reduction theorem

This is an all-depth local result, extending the single all-shrink-shadow direction of PR27. Use a rational center c=a/D>22/27 in lowest terms, D>1 coprime to 6. For a rational z=N/D, use s=N mod 2 and rational tick numerator (m*N+D*s)/2. Suppose c and A(c) both follow positive eventually periodic phase-augmented rational trajectories, each cycle containing at least one growing step and having multiplier 3^g/2^period<1. They need not be in the same rational cycle.

Take a sufficiently large multiple L of 7, M=2^L, and the unique j in {1,...,D-1} with jM=-a mod D. Let r=(a+jM)/D. Then 1<=r<=M (for M>a) and r>=M/D. On the integer ray n=Mv+r, v>=0, the first L physical branches for n and A(n) match their corresponding rational shadows. This follows from the congruence modulo 2^L in the odd-denominator rational lattice; each common-parity tick scales the difference by an odd numerator divided by 2, preserving the remaining parity congruence. Inductively the normalized endpoints are positive and at phase 2, and are

    z_i = U_i*v + b_i,  b_i=U_i*j/D+y_i,
    U_1=3^g1(L), U_2=27*3^g2(L),

where y_i are the two rational endpoints. Let K bound both |y_i-1| over the finite preperiods and periods. Since D is odd, j/D lies at distance >=1/(4D) from each of 0,1/4,1/2,3/4,1. Both U_i tend to infinity by the positive grow assumption. If U_i>4DK, then 0<=b_i-1<U_i and floor(4(b_i-1)/U_i)=floor(4j/D). Put ell_i=log_3 U_i (integer). Applying the exact digit identities to z_i-1 through ell_i digits ends at the same h_q(v) for both sides by Section 1. Cancel those common terms. Physical invariance and GF(2) cancellation give an exact expression of e(n) as the XOR of a finite set of affine errors in v.

For a digit quotient m*v+c' with m a power of 3 and 0<=c'<m, the error av'+b at v'=m*v+c' has ratio to n at most D(am+b)/M, uniformly for v>=0. Put S=max_{q,d} sum a and B=max_{q,d} sum b over the pinned support. Exact values: S=8,001,983,337 and B=7,255,734,239. At each digit, sum the bound over its row. Since sum of the quotient slopes is (U_i-1)/2 and ell_i<=(U_i-1)/2, the sum of the individual supremum ratios of *all* error terms after cancellation is at most

    Q_L = D(S+B)(U_1+U_2)/(2M).

Both U_i/M tend to zero exponentially under the stated cycle multipliers. Thus for every sufficiently large phase-aligned L, all dependencies have positive integer arguments strictly less than n. Indeed Q_L tends to zero. For a proper source ray the same bound controls incoming harmonic weight, since each affine dependency is injective, though dependencies may overlap. No sum over other rays is justified without checking column loads and overlaps.

Effectivity: enumerate the rational preperiods/cycles exactly; at an aligned L0 beyond both transients check U thresholds and Q_L over every phase-aligned residue of the common period. Over another common period U_i increases, U_i/M strictly contracts, and the denominator-distance bound is uniform even if j changes. Also ensure M>a. This proves the result for all L>=L0 divisible by seven, not merely the sampled depths.

### Verified instances

| center | sufficient L0 | common period | different rational cycles | surviving support count at four sampled depths |
|---|---:|---:|---|---:|
|14/17|140|7|no|354|
|15/17|98|7|yes|98|
|16/17|140|7|no|354|
|18/17|161|7|no|354|
|61/71|133|49|no|412|
|72/47|532|7|yes|78|
|166/47|532|7|yes|146|

All seven have Q_L<1/100 for the indicated all-depth range. The verifier independently replays signed numerator dynamics and whole affine integer trajectories for L0,L0+period,L0+10period,L0+30period; it checks the exact GF(2) supports, coefficient positivity, strict smaller-root inequalities and actual sum of supremum ratios at each of those depths. Thresholds are conservative. See rational_shadows.json for exact numbers. The all-depth assertion follows from the proof, not sampling. A minimal actual error cannot be on these rays, assuming the pinned identities. They are nested within each center as depth increases; do not add their densities. The different-cycle instances do not equate rational labels: at the rational center v=-j/D<0, outside the positive-integer ray. Nor does this give an exhaustive smaller-root selector; a finite family of such rays leaves a residual, and the earlier peak obstruction rules out the finite linearly bounded full architecture.

Run `node rational_shadows.mjs` here and compare its JSON to `rational_shadows.json`.
