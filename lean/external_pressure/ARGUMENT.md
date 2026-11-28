# Finite dictionaries and actual phase pressure

This companion derives the 64 helper statements. It does not establish the full M4, R8 or R9 candidates. Every symbol denotes the literal included Lean definition; target_map.json maps all 30 WORD and 34 analytic goals to their proofs.

## Finite populations and phase conventions

Write theta=log(3)/log(2). Included arithmetic proves 1<theta<2, irrationality and the positive rotation-return facts. Pressure logarithms are natural.

For auxiliary x in [0,1], C_t(x)=floor(x+t*theta), with no subtraction of floor(x). At positive length n, an auxiliary word consists of positive integer letters, total prefix C_n(x), and proper prefixes S_t<=C_t(x). Its reward is A_x(w)=sum_(t<n) 2^(-x)*2^(S_t)/3^t.

The canonical prefix starts at zero, even at x=1, then follows the caps. Cap increments are one or two. Adjacent differences therefore give a positive canonical word. Every legal letter is at most 2n. An injection into positive compositions bounds the population by 4^n. The box of letters 0,...,2n thus enumerates the same finite population exactly.

Each reward summand is 2^(S_t-x-t*theta), in (0,1], so 0<=A_x<=n. At n=0 the auxiliary-word type is empty, while the partition is assigned one and its log/normalized log zero. This assigned partition is not an empty sum.

Auxiliary x=1 is not physical phase zero. At length one, the x=0 and x=1 auxiliary words are (1) and (2), with partitions exp(lambda) and exp(lambda/2). The physical phase-1 partition instead equals exp(lambda). The endpoint witness prevents folding auxiliary endpoints through the physical circle convention.

For physical x in [0,1), define j_t=C_t(x)-S_t. Prefix legality gives nonnegative depths, zero endpoints and j_(t+1)<=j_t+phaseIncrement(x,t)-1. Conversely adjacent differences of C_t-j_t recover positive letters. Natural depth bounds j_t<=n are proved before the finite Path box or its toNat/modulo totalizations are used. The maps are inverse and preserve reward, now written sum_(t<n) 2^(-fract(x+t*theta))*2^(-j_t). Thus auxiliary and physical reward partitions agree on physical phases, with zero lengths handled separately.

## Exact finite comparisons

For 0<=x<=y<=1, cap differences are zero or one, with a crossing exactly when fract(t*theta) belongs to [1-y,1-x). Let D count crossings before n. Raising phase changes only the last letter by the nonnegative closing-cap difference. Proper prefixes and unnormalized reward stay unchanged; normalized reward is multiplied by 2^(-(y-x)). The map is injective, including x=0,y=1.

The reverse map clamps each prefix by the lower cap. Both increasing sequences have positive increments, so their minimum retains a legal positive-prefix word. One bit at each crossing records whether the old prefix exceeded the lower cap. These bits, the clamped word and the old closing cap recover the original prefixes; the time-zero bit is forced false. Fibers have at most 2^D elements, and normalized reward loss is at most D.

For lambda>=0, writing Z_x(n,lambda) for the auxiliary partition, the exact maps imply

    log Z_x - lambda*log(2)*(y-x)*n <= log Z_y
    log Z_y <= log Z_x + (log(2)+lambda)*D.

Completion preserves prefixes through n then follows canonical caps. It is injective and preserves all old reward terms. Truncation preserves proper prefixes before n and replaces the closing prefix by C_n(x); it preserves all n preclosing reward terms and removes at most m reward. A record of the old letters n-1,...,n+m-1 recovers the longer word. Its m+1 entries lie in 1,...,2(n+m). Consequently, for n>=1,

    Z_x(n,lambda) <= Z_x(n+m,lambda)
    Z_x(n+m,lambda) <= (2(n+m)+1)^(m+1)*exp(lambda*m)*Z_x(n,lambda).

After dividing logarithms by n, fixed-m completion errors tend uniformly to zero. Reward bounds also give |log Z_x(n,lambda)-log Z_x(n,mu)|<=n*|lambda-mu| for nonnegative tilts.

Concatenation at physical x uses the second block at R^m(x)=fract(x+m*theta). Its map from pairs is injective, legality is preserved and normalized rewards add. Therefore log Z_x(m,lambda)+log Z_R^m(x)(n,lambda)<=log Z_x(m+n,lambda), including separately proved zero cases. This cocycle is not asserted at auxiliary x=1.

## Rotation discrepancy and compactness

Irrationality supplies a positive return r with r*theta equal to an integer plus arbitrarily small delta>0. Set T=ceil(1/delta). Half-open counts of j*delta, 0<=j<T, are differences of ceilings, with unnormalized error less than two. A translated circular interval splits into at most two intervals, giving frequency error bounded by 4/T+2*delta.

Averaging an orbit indicator over shifts 0,r,...,(T-1)r changes its length-n sum by at most r*T through boundary terms. Divide by n, first choose delta, then choose n. This proves discrepancy tending to zero uniformly in starting phase and half-open interval endpoints. The exact cap-crossing identity transfers that estimate to D/n.

The finite partition comparisons now give eventual uniform oscillation bounded by (log(2)+lambda)*|x-y|+epsilon. The family n^(-1)log Z_x(n,lambda) is uniformly bounded by log(4)+lambda and eventually equicontinuous on [0,1]. Individual finite-volume functions need not be continuous.

Compactness is proved by diagonal extraction on finite rational grids. Boundedness yields grid subsequences. Eventual oscillation turns grid Cauchy estimates into uniform Cauchy estimates. Completeness gives a uniform limit, and the same bounds make that limit continuous. No continuity assumption is made on the approximants.

## An actual candidate and full uniform convergence

Let a_n(lambda) be the infimum of log Z_x(n,lambda) over physical x in [0,1). These sets are nonempty and bounded, with 0<=a_n<=n*(log(4)+lambda). The physical cocycle implies a_(m+n)>=a_m+a_n. The finite-roof Fekete argument therefore applies to the actual infima and proves a_n/n tends to P(lambda)=sup_(L>=1) a_L(lambda)/L. No pressure law is assumed to define P. Its negative-tilt extension has no asserted pressure meaning.

Take any continuous uniform subsequential limit f. The cocycle and vanishing completion error give f(R^m x)<=f(x) for positive m. Every positive irrational rotation orbit approximates every closed phase, so continuity forces f constant, including the auxiliary endpoint 1. Uniform convergence to that constant identifies it with the same limit of a_n/n, namely P.

If full uniform convergence failed, bad volume/phase pairs would have a further uniformly convergent subsequence, contradicting its now identified constant limit. Thus convergence is uniform over closed auxiliary phase for every nonnegative tilt. Passing the finite tilt Lipschitz bound to limits gives the same bound for P; a finite tilt mesh and a three-error triangle inequality make convergence uniform on every compact nonnegative tilt interval.

## Physical/source transports and cost normalization

The exact word/path dictionary transfers convergence to physical reward pressure. On strict source rungs, the literal source partition equals the phase-zero auxiliary partition. Such rungs are unbounded, giving fixed-tilt convergence there. At arbitrary source lengths the correct closing transport instead uses phase defect d_r and tilt lambda*2^(d_r), where 0<=d_r<1. Compact-tilt convergence shows the source pressure tracks P(lambda*2^(d_r)). Replacing that argument by P(lambda) would change the result.

For paths, let B_x(n)=sum_(t<n)2^(-fract(x+t*theta)). Literal summands give reward+cost=B_x(n), hence rewardPartition=exp(lambda*B_x(n))*costPartition. The zero-depth path makes costPartition positive, justifying logarithms rather than using their total value at zero.

Reference averaging uses monotone bin envelopes for u->2^(-u). Rotation discrepancy controls all bins uniformly. Upper and lower Riemann sums differ exactly by 1/(2M), while the antiderivative -2^(-u)/log(2) gives mean b=1/(2log(2)). Thus B_x(n)/n tends uniformly to b and physical cost pressure tends to p(lambda)=P(lambda)-lambda*b, also uniformly on compact tilt ranges. These are the candidate core convergence components, not the complete canonical pressure-bounds/model package.

## Qualitative laws and integrated lower brackets

Normalize finite exponential-sum weights and apply convexity of exp to prove convexity of the finite log partition. Limits give convexity of P and p. Nonnegative rewards make P nondecreasing; nonnegative costs make p nonincreasing. The zero-cost path gives p>=0 and p<=P(0). With b<=1 these prove the stated one-Lipschitz bound for p. Neither P(0)=baselineEntropy nor p(lambda)->0 is established here.

Finite physical log partitions are measurable: legal cells use measurable floors, phase weights are measurable and sums are finite. Zero-depth lower bounds and finite exponential upper bounds give an integrable uniform roof over one phase period.

Let I_L be the phase integral of log rewardPartition at length L. Exact physical periodicity and rotation-invariance of a full-period integral turn the physical cocycle into I_(m+n)>=I_m+I_n. Hence k*I_L<=I_(kL). Uniform physical pressure convergence, removing endpoint 1 only as a null point, gives I_n/n->P. Applying this along kL yields I_L/L<=P and cofinality I_L/L->P. No infimum/integral reversal or Gibbs limiting law is used.

## Meaning preservation, assurance and limits

All 63 mathematical source files are unchanged. The new aliases have exactly the original goal constants and frozen raw propositions. All 77 canonical model-origin types and available/null values are retained. Seventeen historical legacy WORD bodies belong to currently opaque origins; their metadata is preserved separately, never substituted into the current body register.

The audit checks every owned declaration, including generated helpers and data, rejects custom owned axioms/nonstandard transitive dependencies and forbids Challenge imports. The isolated Challenge has only the 64 designated holes. Full assurance additionally requires fresh complete export/replay, trusted isolated comparison and all six modes in both stages. Hostile tests require a positive full rerun and actual rejection of a True wrapper, hidden imported axiom and modified literal concatenation with the same proposition.

This layout was introduced as a release candidate requiring separate independent assurance. Even eventual full assurance certifies these helper meanings only. Baseline/infinite-tilt bounds and a complete actual source model, all-c entropy/Legendre, critical/localized regularity, rigorous effective algorithms and the executed certified table remain separate requirements. No full M4/R8/R9, capture, novelty or human expert acceptance follows.


## Classical background

The superadditive step is the classical Fekete argument; historical background is M. Fekete, *Über die Verteilung der Wurzeln bei gewissen algebraischen Gleichungen mit ganzzahligen Koeffizienten*, Mathematische Zeitschrift17,228–249(1923), [publisher record](https://link.springer.com/article/10.1007/BF01504345). Equidistribution background includes H. Weyl, *Über die Gleichverteilung von Zahlen mod. Eins*, Mathematische Annalen77,313–352(1916), [publisher record](https://link.springer.com/article/10.1007/BF01475864). The required uniform forms have their complete proofs above and in Lean. Publisher bibliographic metadata was checked; no original theorem-location or priority conclusion is inferred from unavailable full text.
