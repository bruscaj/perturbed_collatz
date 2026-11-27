# Obstructions and two-clock reductions

## 1. Model and the genuine remaining objective

Let H=(0,0,0,1,0,0,1), p mod 7, and F(n,p)=(T(n)+d_p,p+1), with T the shortcut Collatz map and d=(0,0,1,-1,0,1,-1). Normalize z=n+1-H_p>0. A grow is chosen when z mod 2=H_p, otherwise shrink. Each tick is z'=(m z+s)/2 with s=z mod 2, m=3 on a grow and 1 on a shrink. B(t)=(6t,1) in normalized coordinates, t>=1. The first tick is always a grow to (9t,2). The known cycle has phase-indexed z=(1,1,1,1,2,3,2) and exactly two grows per seven ticks. B(1) is captured (clock 18 reaches (3,5)).

PR19 reduces global capture to capture of all B(t). A witness consists of positive u<t and nonnegative k,l with k=l mod 7 and F^k B(t)=F^l B(u), or direct capture. Strong induction on t closes if every t is covered. An equivalent reduction obligation may be restricted to the explicit PR19 complement, or to residuals of any sound smaller-partner selector. Requiring a decrease in some *other* parameter at the meeting point is not enough. B1 rank gap is 8(t-u). No arbitrary switching of the physical schedule is allowed.

This is not a problem of showing that almost every t admits a smaller partner: PR24 already establishes that even for adjacent B1 parameters. The quantitative O(X^(29/30)) maximum-prefix residual is a count of possible minimum representatives only, not a count of noncaptured seeds. A nonempty invariant exceptional component can have large inverse fibers attached to sparse minimum representatives. A local basin-density argument must estimate the actual exceptional set.

## 2. Equal-count induction is intrinsically incomplete

### 2.1 Universal elementary embeddings

Consider identities between B(t) and B(A t+b), A a positive integer, b an integer, on all sufficiently large integer t, with fixed clocks k,l and a FIXED parity word on each side (the entire unpartitioned source family). The first B1 tick has odd free coefficient 9, so if k>=2 the next parity varies; hence k<=1. For k=0, l>0 would require A*3^g=2^l, impossible because a positive-clock B1 history has at least one grow. With k=l=0 the identity is trivial. For k=1, l=1 mod 7 and leading-coefficient equality gives A=2^(l-1) 3^(1-g). Since A is integral, g=1 and the partner must shrink after its mandatory grow. The case l=1 is the identity. (This does not classify piecewise words, rational-slope embeddings on subfamilies, or variable clocks.)

At phase two the seven all-shrink parity bits are 1,0,1,1,0,1,1, so their numerator is 109. For h shrink laps, S_h=109(128^h-1)/127. Therefore the necessary and sufficient affine relation is

    A=128^h,   9b=-S_h.

The integer condition is h=0 mod 6: modulo 9, 109 and 127 are units and 128 has order six. Define

    E_j(t)=2^(42j)t - 109(2^(42j)-1)/1143,     j>=0.

Then for all t>=1,

    F^(42j+1) B(E_j(t)) = F B(t).

Legality is also obtained directly: invert 42j shrinking ticks from (9t,2) and then the mandatory grow. Shrink inverses are 2z-s with their required fixed parity; S_h divisible by 9 ensures B1 divisibility after the inverse grow. All states are positive. E_j expands for j>0. These maps are powers of one affine map with common rational fixed point 109/1143. Their compositions commute, so no new translation arises by commuting these elementary universal embeddings. In the reverse direction E_j(t) reduces to t; this is a valid infinite rule on a thin congruence class, not a general smaller-partner theorem.

### 2.2 The excess-growth index gives infinitely many unavoidable equal-count roots

For each *captured* B1 parameter define the integer

    I(t) = lim_(m -> infinity) (g_(7m)(B(t)) - 2m),

where g_k counts grows in the first k ticks. The limit stabilizes exactly because the known cycle has two grows per lap. For t=1 the index is 2 (at clock 21, g=8 and the cycle state is (1,1)). The embedding has just one grow before its join, so

    I(E_j(t))=I(t)-12j.

For every j>=0 the index class 2-12j is nonempty in the known basin. Choose its least positive B1 parameter a_j. If there were a smaller u with a synchronous meeting and the same grow count, u would be captured too and I(u)=I(a_j). This contradicts minimality. Thus every a_j has NO smaller equal-count synchronous B1 partner, at ANY clock. They are distinct and a_j<=E_j(1)<=2^(42j). There are at least 1+floor(log_2 X/42) such captured roots through X. This lower bound is existential; it does not enumerate the actual minima a_j.

Consequences:

1. A selector restricted to equal-count synchronous comparisons, even if allowed unbounded clocks, cannot cover all but finitely many B1 parameters. In particular the previous plan of eliminating every maximum-prefix survivor with more equal-count comparisons alone is not feasible. Finite captured exceptions do not fix this. It could work in conjunction with direct capture of an infinite base family or edges changing the index.
2. For a general phased meeting of captured parameters with source clock k, partner clock l, source grows g_s and partner grows g_u,

       I(t)-I(u)=g_s-g_u+2(l-k)/7.

   To prove this, append a common tail to the join, taking source elapsed time a large multiple of seven. Partner elapsed time is then a multiple of seven as well; subtract the two stabilized expressions. The index identity is conditional on capture, not an index assigned to a hypothetical divergent orbit.
3. A complete decreasing-parameter induction using only edges with nonnegative right-hand index difference and a finite captured base is impossible: all captured parameters would have index bounded below by the minimum base index, whereas E_j(1) makes it unbounded below. A complete bank with finite exceptions MUST allow negative index differences (or another independent capture mechanism). This gives an exact design test for new rule families. It does not assert every state requires a negative-index edge. A larger partner clock can change the index, but unequal growth counts at equal clock can also change it.

`obstructions.py` checks the baseline, the first 121 shrink-lap integer tests, and whole affine replays of three embeddings in the signed model. The argument for unbounded j is the arithmetic proof, not those checks.

## 3. Sparse shrink words resist *all* smaller synchronous partners

This is a different obstruction: it extends the all-growing-prefix barrier to histories containing arbitrarily many shrink steps. It bounds a specified comparison horizon, not the eventual behavior of a seed.

### 3.1 Center and offsets

Set D=3^7-2^7=2059 and C=(280,420,630,945,388,582,873), satisfying 2C_(p+1)=3C_p-D H_p and C_p mod 2=H_p. Let W=Dz+C_p. The centered recurrence is

    G: W' = 3W/2,    S: W'=(W+Q_p)/2,
    Q=(2619,2899,3319,-169,2835,3223,-313).

All Q are odd; max |Q|=3319 and max v_3(Q)=4. This center is inherited from the earlier all-growth analysis. The new application concerns sparse cancellation of offsets.

Work after the mandatory initial B1 grow: W_0=9D t+C_2. For k more ticks with g grows, r=k-g shrinks at positions j_i (0-indexed, i=0,...,r-1), let a_i=j_i-i be the number of preceding grows. The affine numerator A in W_k=(3^g W_0+A)/2^k satisfies

    A/3^g = sum_i 2^i Q_(2+j_i mod 7) (2/3)^a_i.     (1)

For a synchronous B1 partner with g' >= g grows after its initial tick, r'<=r, meeting implies

    A/3^g - 3^(g'-g) A'/3^g' = 3^(g'-g) W'_0 - W_0 in Z.   (2)

The left side contains at most 2r terms c(2/3)^a, |c| <= 3^r 2^(r-1)3319. Set c0=3r+8 and B_r=2r c0=6r^2+16r. The sum of absolute coefficient bounds is strictly less than 3^c0.

### 3.2 Sparse 3-adic cancellation lemma

Let P=sum of at most L nonzero terms c_i(2/3)^a_i, a_i nonnegative integers, |c_i|<=M, and LM<3^c0. If P is integral in Z_3, then every term whose exponent exceeds L c0 belongs to an exact zero cluster of terms of exponent diameter at most (L-1)c0. These clusters are disjoint. Terms with the same exponent may be grouped together.

Proof: start at the largest remaining exponent m, accumulate a cluster containing its terms, and denote its exponent diameter by d. Its sum is (2/3)^m 2^(-d) S, where S=sum c_i 3^(m-a_i) 2^(d-(m-a_i)) is an integer with |S|<3^(d+c0). If S=0, remove the zero cluster and start again. Otherwise its 3-adic valuation is < -m+d+c0. If no further term exists, or the next term has exponent m-e with e>d+c0, the current nonzero sum has strictly smaller valuation than every remaining term. Hence it is also the valuation of P, contradicting integrality whenever m>L c0 and d<=(L-1)c0. If that next term exists with e<=d+c0, add the entire next exponent group. The diameter increases by at most c0, and at most L groups can be added. When m>L c0 a zero cluster must therefore be removed before reaching the end. Iterate until no large exponent remains. QED.

### 3.3 Obstructed words and their size

Suppose r>=1, a_0>B_r, and all successive gaps a_(i+1)-a_i>B_r. Each of the r source terms in (1) must occur in a separate exact zero cluster of (2). A source term cannot cancel alone. At most r alternate terms are available, so there must be exactly r alternate terms and precisely one in each source cluster. Thus r'=r, g'=g. Pairwise equal rational terms have equal 2-adic valuation; since Q is odd, the valuation of 2^i Q (2/3)^a_i is j_i. Matching shrink positions implies identical complete parity words, and meeting then forces t=u. This rules out all smaller partners with g'>=g.

For g'<g, use the uncentered endpoint after k ticks from 9t:

    z_k=(9*3^g*t+N)/2^k,    0<=N/3^g<2^k.

The identity with partner u gives u>=3^(g-g')t-2^k/9>t for t>=2^k. So no smaller partner exists in this case either. We conclude:

**For every r, every word with the stated grow gaps before its r shrinks, and any all-grow tail, there is NO smaller synchronous B1 partner at clock k+1 on the whole source ray t>=2^k.** A meeting at an earlier clock would persist to k+1, so that too is excluded. Each word is realized by a unique residue modulo 2^k (odd multiplier), with infinitely many positive lifts. It need not be realized by a small representative or by an infinite positive orbit.

The number of these distinct surviving words is at least binomial(k-r(B_r+1),r) when the upper entry is >=r, by allocating the obligatory grow gaps before each shrink. For k>=2r(B_r+2) this is >=(k/(2r))^r. Choosing r=floor((k/100)^(1/3)) for large k gives exp(Omega(k^(1/3) log k)) obstructed words. This is a lower bound on surviving *words* at the indicated horizon, not a lower bound on the size of the never-captured set or a nonregularity theorem.

### 3.4 Complete single-shrink comparison

For one-shrink words at positions j<j', let d=j'-j. Equal grow count and a meeting of B1 parameters would require

    v3(3^d Q_(2+j) - 2^d Q_(2+j')) >= j'+2.

For d>=5 the left valuation is <=4 because the second term has valuation <=4. For d<=4 all 28 phase/gap cases have valuation <=4. The three pairs with j'<=2 are checked directly and do not meet the required threshold. Therefore all distinct one-shrink words have distinct same-count B1 numerator residues, at all horizons. For an all-grow partner, (2) gives 3W'_0=W_0+2^j Q_(2+j)/3^j. Integrality and the B1 color W_0=9Dt+C_2 exclude j>=5 and all j=0,...,4 except j=2, where the offset equals 2C_2=1260. Hence 3u=t. The one-shrink prefix guard there is t=2 mod 8, so the exception is exactly t=24v+18, u=8v+6, which meet at clock 4 and then stay together. With t>=2^k the lower-grow-count case is excluded as before. Apart from this already known ratio-three exception, all one-shrink prefixes resist smaller synchronous B1 comparisons, irrespective of their all-grow tail.

This proves a reason for unequal-clock (or genuinely different rank/capture) attacks, not a proof that such attacks succeed. `obstructions.py` checks the seven centered phase formulas on 1,400 literal signed states, 210 small one-shrink words, the exact valuation conditions, and eight sparse whole-affine examples through 4,624 postinitial ticks. The all-word exclusion is the written sparse lemma, not enumeration of all alternate histories.

## 4. Inverse-only and bounded-source-clock ceilings

A smaller-ancestor-only induction (source clock zero) cannot cover all B1 parameters outside finitely many captured bases. Indeed repeated reduction of t to a smaller B1 ancestor terminates at one of those bases, and t lies on the forward orbit of that base. A finite union of captured forward orbits is finite, contradiction. This also explains why arbitrary-depth inverse-only search cannot provide the universal proof by itself.

An independent quantitative ceiling holds for ANY FINITE bank of fixed inverse return words. For a B1-to-B1 return of length l=7m and total grows g, an eventual smaller B1 ancestor requires forward slope 3^g/2^l>1. If slope <1, a fixed affine word can give a smaller ancestor for only finitely many target parameters (offset fixed). Equality of slopes is impossible for l>0. After the mandatory initial grow, each such word has target equation

    2^l t = 3^g u+N/3.

N is the uncentered numerator after l-1 ticks. If N/3 is not integral the word is incompatible; otherwise the target occupies at most one residue class modulo 3^g. The union bound for expanding words is therefore

    U = sum_(m>=1) sum_(g:3^g>2^(7m)) binomial(7m-1,g-1) 3^(-g).

The first 80 summands have exact rational sum <251437/10^6. For the tail, g>5l/8 follows from 3^5<2^8. Tilt by 5 to get an upper bound (5/8)*((8/3)/5^(5/8))^l < (5/8)*(49/50)^l. Summing l=567,574,... gives <51/10^6 (all comparisons checked in rational arithmetic by raising to integer powers). Hence U<63/250=0.252. Every finite inverse-return bank misses MORE than 74.8% of B1 parameters in natural density, including if it adds finitely many captured bases. The union of expanding guards also has ternary Haar measure <=U; a countable union on positive integers need not have that natural-density bound, so do not infer one. For l<=21 the exact compatible expanding-word union has natural density 40028177/387420489 (about 10.33%); 2,169 whole-ray replays through l=14 check the arithmetic construction, not all 21-step rays.

The bounded-original-side-horizon obstruction (prior METHOD-06) has a simple B1 consequence. If all t outside a finite captured base have a smaller common-future partner with original clock k<=K, then strong induction bounds every peak of B(t) by max(M_base, (3/2)^K(6t+1)), using z+1 and the fact that all later states lie on the smaller orbit. But the centered integer 2059t+70 gives exactly the initial all-grow valuation v2(2059t+70)+1: W at phase 1 is 6(2059t+70), and each grow decrements its binary valuation by one. Arbitrarily long initial grows occur on positive dyadic rays and force unbounded peak/input ratios. Hence no uniform source clock cap can suffice, even if the partner clock is unrestricted. More quantitatively, if K_max(X) is the largest selected source clock for t<=X outside the finite base, take a residue lift in [2^L,2^(L+1)) with at least L+1 initial grows. The same induction bound for t<=2^(L+1) gives K_max(2^(L+1))>=L-O(1). In particular a universal o(log t) source horizon is impossible. This is not an obstruction to finite descriptions of parameter-dependent unbounded clocks.

## 5. A valid replacement: exact two-clock short-partner enumeration

A first heuristic beam (`selector.py`) generated valid certificates but can discard good ancestors. Replace it by an exact bounded search (`two_clock.py`). For each positive partner clock l<=18 (default cap 14), enumerate all 2^(l-1) parity words after its mandatory initial grow. Group by (g,N mod 9*3^g), where g counts postinitial grows and N is the numerator. In each group sort the possible N. For a source endpoint (z,p) reached at clock k, only l=k mod7 is relevant. For a proposed partner total growth g_u>=1, the exact B1 parameter is

    u = (2^(l-1) z-N)/(9*3^(g_u-1)).

Select the largest N in the matching residue group subject to u>=1, i.e. N<=2^(l-1)z-9*3^(g_u-1). This is the minimum positive u at that clock and grow count. No beam pruning. The numerator congruence and integrality imply the whole inverse word is legal: integrality of the final inverse excludes an uncancelled factor of 3 in any preceding denominator, and the fixed parity conditions follow from the inverse branch formulas. Alternatively the forward parity-cylinder uniqueness gives legality from the integer affine endpoint identity. All inverse steps from a positive endpoint are positive on their integer guards. At l=0 simply test whether p=1 and z is divisible by six.

For source total grows g_s and a candidate u<t, require the nonexpanding partner-stride condition 2^l 3^g_s <= 2^k 3^g_u; this ensures an unbounded affine ray of strict rank decrease rather than an isolated point. Define

    A=2^k 3^max(g_u-g_s,0), B=2^l 3^max(g_s-g_u,0).

Then A>=B and the two endpoint slopes are equal. Backshift to a positive base pair with strict inequality, and independently replay both full rays in the signed physical dynamics. Every accepted witness proves a sound whole-ray reduction for all nonnegative lifts. The method is exhaustive for the two specified clock caps and this slope condition, not for arbitrary isolated witnesses or arbitrary clocks. It is an algorithmic certificate selector, not a universal decision procedure for convergence. The table grows exponentially in the partner cap, but a long source history only requires forward simulation and lookups. This is why keeping one clock short can be effective.

### 5.1 New explicit rays against named difficult parameters

The following certificates were generated by the exact selector, then independently replayed in signed coordinates. Endpoints listed are normalized (z,p).

    t=549755813888 v+17 = 2^39 v+17,
    u=55788550416 v+2 = 16*3^20 v+2,
    F^39 B(t)=F^4 B(u)=(564859072962 v+21,5).

For every v>=0, t>u>0. This covers t=2^b+17 for all b>=39, including all of the previous resource-limited 128- and 256-bit examples and the 512-bit extension. It is a reduction to a smaller B1 launch, not a claim that the smaller launch is independently verified captured for every v. Source grows=23, partner grows=3, index difference (if captured)=10.

    t=268435456 v+19 = 2^28 v+19,
    u=204073344 v+16,
    F^28 B(t)=F^7 B(u)=(2324522934 v+183,1).

This covers t=2^b+19 for all b>=28. Source grows=18, partner grows=5, index difference (if captured)=7. Both rays are entirely in the named PR19 five-guard complement (17 mod 256, respectively 19 mod128). No claim of disjointness from every later or historical bank. Note that these particular certificates have positive index differences; a universally complete bank still needs negative-index rules or another mechanism, as section 2 shows.

### 5.2 Long initial growing runs

For h in {4,8,16,32,64,128,256,512}, choose M=2^(7h-1) and t=(-70*2059^(-1) mod M)+M. The centered identity proves at least 7h initial grows. The exact selector with partner cap 14 found the following accepted source/partner clocks:

| h | initial grows (at least) | t bit length | source clock | partner clock |
|---:|---:|---:|---:|---:|
|4|28|28|91|0|
|8|56|56|196|0|
|16|112|112|520|9|
|32|224|224|1133|6|
|64|448|448|1815|9|
|128|896|896|3430|0|
|256|1792|1792|6637|1|
|512|3584|3584|13643|7|

Every row certifies an entire affine ray, not just the sampled integer. The full large integers, strides and endpoint coefficients are in `two_clock_verification.json`. This is finite evidence that the approach can handle long histories with very short partners; it is not an arbitrary-h theorem, a complexity guarantee, or evidence that every t admits a partner of clock <=14. A bounded original-side search can still miss infinitely many inputs. No failed query is a noncapture certificate.

## 6. Basin homogeneity: a new analytical consequence, not yet the needed local hitting

The following argument uses PR24's adjacent synchronization for each phase and, for its quantitative version, the stated polynomial tail (both written proofs). Let f_p(z) in {0,1} be ANY forward-invariant label, f_p(z)=f_(p+1)(G_p(z)). In particular the label of the known basin is invariant in both directions along an edge. Put

    D_p(X)=sum_(1<=z<X) |f_p(z+1)-f_p(z)|.

A boundary requires an adjacent pair that never coalesces. By PR24's exact parity-cylinder argument for type (p,0,1), D_p(X)=o(X). With the tail bound at n=floor(log2 X) on dyadic shells (discard the finitely small shells or sum the geometric error),

    D_p(X)/X = O((log log X)^(3/2)/(log X)^(1/4)).    (3)

The constants can be chosen over the seven phases. This concerns *all* invariant labels, regardless of which basin they represent.

### 6.1 Transport of logarithmic interval mass

For bounded log interval J let

    L_(p,X)(J)=integral_J f_p(floor(X exp(s))) ds.

On compact log ranges this differs from the sum of f_p(n)/n over X exp(J) by O_R(1/X), with boundary rounding included. Summing over only one parity and multiplying by two makes error O_R(eta(C_R X)), where eta(Y)=max_p D_p(Y)/Y+1/Y; group adjacent integers and use the 1/n weight variation. For the selected parity the branch maps n to y=(mn+s)/2 with m=1 or3, and consecutive n in that parity yield a progression in y of stride m. The identity 2/n=m/y+O_R(X^-2) and grouping consecutive blocks of m integers replace that progression by all y with error O_R(eta(C_R X)). Invariance of f along the branch now gives, for either m,

    L_(p,X)(J) = L_(p+1,X)(J+log(m/2)) + O_R(eta(C_R X)).   (4)

All estimates are uniform for intervals in a fixed compact range; constants may depend on that range. The same block grouping works with any fixed arithmetic progression and with phase-dependent labels.

Comparing the two branch choices gives approximate same-phase translation by a=log 3. Seven shrink branches give b=7log 2. Their negatives are obtained by translating the interval back. Take any X_i tending to infinity and a weak-* convergent subsequence on compact ranges for the bounded rescaled labels at each phase (diagonal extraction). Equation (4) forces the limiting measures to be translation invariant under a and b, and hence their dense additive group, since 3^q=2^(7p) has no nonzero integer solution. Continuity of translation on compactly supported continuous tests extends the invariance to every real translation. The limiting density must be constant almost everywhere; (4) equates the constants at all phases.

Consequently, for every fixed 0<a0<b0, phase p,p', the ordinary mean of f_p over [a0 X,b0 X] differs by o(1) from the mean of f_p' on [1,X]. For the first use the log-variable test with the weight exp(s); for the second cut off z<epsilon X and let epsilon decrease. A contradiction subsequence proves the difference tends to zero, without needing a unique global limiting density. The same holds for sampling fixed residue classes by block grouping. This gives macroscopic asymptotic homogeneity, not convergence of the global mean to a specific value.

### 6.2 Quantitative, elementary transport and gap bound

Equation (3) allows a weak quantitative improvement. By Dirichlet approximation, for Q>=2 there are q,p with 1<=q<=Q, p=O(Q), and 0<theta=|q a-p b|<=b/Q. The lower bound theta>=exp(-C Q) follows by comparing the distinct integers 3^q and 2^(7p) and taking logs (with C an absolute constant). Approximate any shift of bounded magnitude by an integer multiple r theta to error O(1/Q), with |r|=O_R(exp(CQ)). The total number of a and b translations required is O_R(Q exp(CQ)). Order positive and negative steps greedily, taking a step opposing the sign of the partial sum while both signs remain; the partial sums stay in a bounded range, and the final monotone remainder ends at a bounded total shift. Thus (4) can be iterated with a single compact-range constant, yielding

    |L_(p,X)(J+d)-L_(p,X)(J)|
        = O_R(1/Q+Q exp(CQ) eta(C'_R X)),    |d|<=R.

The endpoint error from approximating the shift is <=2|error| since 0<=f<=1. Take Q=floor(c log log X) with c>0 sufficiently small. Equation (3) gives the uniform log-interval shift error O_R(1/log log X).

Assume the label has positive lower natural density in one fixed compatible progression (e.g. the known basin under the reviewed linear inverse theorem). By macroscopic homogeneity it has positive lower global mean at every phase, say >=c1>0 eventually. Choose R so exp(-R)<c1/4. The logarithmic mass on [-R,0] is then bounded below by a positive constant c2, because the ordinary count in [X exp(-R),X] is >=(c1/2)X and the weights are >=1/X. If an interval inside [X,2X] has zero basin mass, let h be its log width. Take a subinterval of log width h'=min(h,c2/4) (and allow O(1/X) endpoint rounding). Tile [-R,0] by at most R/h' translates and a remainder of length <h'. Each translated interval has mass O_R(1/log log X); hence c2<=O_R(1/(h' log log X))+h'. This forces h=O(1/log log X). For a gap in a fixed residue progression instead, its log mass differs from zero by O_R(eta), which is smaller than the same bound, by block grouping. Returning to linear coordinates, every such gap inside [X,2X] has length O(X/log log X). This gives a conditional upper bound on maximum B1 basin gaps, with uncomputed constants.

The scale is dramatically larger than PR24's synchronized-block width exp((log X)^gamma), gamma<1/14. Thus this transport theorem does not yield the local hitting property needed for the capture proof. Improving the elementary Diophantine bound alone will not bridge this difference: the present boundary error is only a negative power of log X. Stronger fine-scale estimates must actually select the known basin, or use a new mechanism at the much shorter synchronization scale. The three-step UTT two-cycle control is consistent with this theorem: both basins can have macroscopic homogeneity and sublinear gaps. Neither density-one adjacency nor macroscopic homogeneity selects one basin.

### 6.3 A failed boundary-amplification approach

It is tempting to take one nonmerging adjacent pair and use inverse counts to create a positive-density family of nonmerging adjacent pairs. Synchronous inverse lifting of a FIXED distinct target pair cannot do this. For any fixed K, finitely many adjacent ancestors can reach that pair at common clock <K (finite inverse branching). All remaining ancestors have not merged by K, since coalescence persists and the target pair is distinct. PR24 bounds the upper density of those starts by the K-tick nonmerger tail, tending to zero. Thus the union over all common-clock inverse depths has density zero. This argument holds even when the target pair eventually merges. Separate one-state inverse floors do not produce a joint synchronous inverse floor of positive density. A target-specific local hitting estimate or a different unequal-clock geometry is needed.

## 7. A quantitative criterion which really would imply capture

Write E for the invariant set of states not captured by the known cycle. The reviewed analytic inverse argument gives, for each fixed compatible B1 progression, a positive constant c_P such that a fixed noncaptured target of normalized height m has at least c_P X/m inverse ancestors in that progression up to X for sufficiently large X/m. We use this only conditionally; the analytic constants remain uncomputed, and the full uniform-in-target version must be established before using a uniform cutoff. A target-specific positive lower density already suffices for the density-zero contradiction.

Let A(M) be the B1 parameters whose entire forward orbit avoids normalized heights <=M (all phases). If E is nonempty, choose a least normalized height m among all E states. Every inverse ancestor of that target belongs to E, hence never visits height <m. Therefore

    lower natural density of A(m-1) >= c/m,

with c independent of target if the uniform inverse theorem is available. This also lower bounds lower logarithmic density (partial summation). Thus an upper logarithmic density estimate upper_d_log(A(M))<=Phi(M) with explicit m Phi(m-1)<c for all m>M0, together with verified capture of every state of height <=M0, would prove global capture. In particular a power bound Phi(M)<=C M^(-1-epsilon) with explicit positive epsilon and constants is sufficient for a finite cutoff. No assumption about independent successive descents is permitted. The condition concerns *entire avoidance of a fixed region*, not visiting a source-dependent shrinking threshold.

Even more directly, for any fixed M verified captured, density zero of A(M) in one fixed B1 progression contradicts the target-specific positive inverse density of any exceptional state. If the region is not known captured, a zero-density avoidance theorem plus the inverse floor first forces every state to hit that region, and applying it to every forward tail gives infinitely many visits; then finiteness gives periodicity and a finite check of the low region identifies the known cycle. This avoids an a priori no-other-cycles assumption.

Tao's ordinary-Collatz first-passage theorem ([arXiv:1909.03562](https://arxiv.org/abs/1909.03562), published Annals 2022) is an important methodological benchmark, not a theorem for this forced schedule. A conclusion with a threshold tending arbitrarily slowly to infinity with the input is not a fixed-height avoidance bound. Likewise total-variation stabilization estimates of order a negative power of log of the threshold do not directly give the above polynomial-in-M avoidance bound; they must be combined with a basin-specific hitting estimate and checked conditioning. Earlier reciprocal-square exceptional-mass and marked-descent estimates in this repo do not establish zero density of permanent exceptions. No new avoidance estimate is claimed in this package.
