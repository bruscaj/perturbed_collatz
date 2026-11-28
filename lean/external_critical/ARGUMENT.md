# Critical-space support: model and derivations

This project supplies twelve supporting theorems. It does not establish the full critical Gibbs law, critical differentiability, M4, R8, R9 or integer Collatz capture. Jake S. Brusca is the author; this ChatGPT-assisted work remains a personal research draft. AI implementation/review roles overlap. No human expert review or novelty certification is asserted.

The definitions and propositions were fixed before implementation. Public aliases retain the exact original goal constants and raw bodies; historical `Draft` names/comments are source provenance. The specification and frozen raw registers give the exact meanings. No custom axiom or desired pressure law is inserted into the model.

## Space, shifts and roof

Let theta=log(3)/log(2). The physical phase is `Phase = AddCircle 1`. Heights are `Height = OnePoint Nat`, with the genuine one-point compactification: finite heights are isolated and neighborhoods of infinity omit only finitely many natural heights. This is not the discrete option topology.

`Config = Phase × (Int → Height)` has its product topology and Borel sigma algebra. Write s(x) for the literal circle representative in[0,1). Integer shifts and the local roof are

    T_r(x,h) = (x+r*theta mod1, (t ↦ h(t+r))),
    w(infinity)=0, w(j)=2^(-j),
    v(x,h)=2^(-s(x))*w(h(0)).

Thus0<=v<=1. The height weight is continuous at infinity; the phase representative has an actual seam at0. The roof is continuous off that seam, not globally continuous. Physical circle1 equals0; this does not identify a different closed auxiliary word phase1 with phase0.

`SpaceTopology` embeds Height continuously and injectively into `{0} ∪ {1/(j+1)}`. Compactness makes this embedding closed, giving metrizability and second countability. Circle and countable-product instances give these properties for Config. `PhaseRepresentativeLaw` fixes the representative/coercion/fractional-part identities. `ShiftGroupAndContinuity` proves T_0=id and T_s∘T_t=T_(s+t), with continuous measurable shifts. `RewardRoofAndRegularity` proves the measurable roof, its bounds and off-seam continuity.

## Literal finite rooted law

For actual real phase x in[0,1), length n and t<n, put

    g_t=floor(x+(t+1)theta)-floor(x+t*theta),
    a_t=2^(-fract(x+t*theta)).

The increments belong to{1,2}. A legal path has natural heights j_0=j_n=0 and j_(t+1)<=j_t+g_t-1. Its exact finite representation bounds heights by n. Set

    R_n(x,j)=sum_(t<n) a_t*2^(-j_t),
    Z_n(x,lambda)=sum_(legal j) exp(lambda*R_n(x,j)).

The zero path is legal and Z_n>0. Sampling proceeds in this order: normalized Haar phase, then the **normalized quenched** Gibbs path mass exp(lambda R_n)/Z_n at that phase, then a uniform root i in0,...,n-1. Rooting shifts phase by i*theta and the path by i, using finite height0 outside[0,n]. This is `rootedMeasure n lambda`; it is not a phase law weighted by Z_n. The n=0 root sum is empty; normalization is asserted only for n>0 and nonnegative tilt.

`RootedNormalization` proves measurability of this actual kernel, mass1 and a Haar phase marginal. Path masses sum to1 separately at each phase. Each root phase is a Haar translation, and averaging roots preserves Haar measure.

For continuous f bounded everywhere by |f|<=B, the sum of f(T_1 root_i)-f(root_i) telescopes to two end-root values. Therefore

    |integral f∘T_1 dmu_n-integral f dmu_n| <= 2B/n.

`RootShiftError` proves this literal boundary estimate. Its bounded-real kernel integration lemma is derived from nonnegative bind integration and positive/negative parts, not assumed.

`RootedStationarySubsequence` takes arbitrary n_k>=k+1 and arbitrary nonnegative tilts. Compactness of probability laws on compact Config gives a strictly indexed weakly convergent subsequence. The2B/n estimate makes its limit stationary; the continuous phase projection retains its Haar marginal. This permits infinite-height mass. No finite-height tightness, Gibbs property or critical law follows here.

## Weak passage of the discontinuous roof

`WeakRewardPassage` assumes weak probability convergence and a Haar phase marginal for the **limit**. The approximating laws need no Haar premise. Haar measure makes the seam null.

Set chi_k(x)=min(1,(k+1)*dist(x,0)). The product chi_k*v is globally continuous: at the seam its absolute value is bounded by (k+1)*dist(x,0). Moreover

    |v-chi_k*v| <= 1-chi_k.

Weak convergence passes the integrals of these bounded continuous cutoffs and error bounds. Under the limit, dominated convergence makes the error integral tend to0. An epsilon triangle then passes the original roof expectation, preserving the actual seam rather than replacing its value.

## Conditional finite/infinite sector separation

`FiniteInfinityExclusion` additionally assumes that, for every natural a, the cylinder h(0)=a with h(1) outside{0,...,a+1} has probability zero. This project does not assert those hypotheses for the constructed limit.

The premise implies `h(0) finite => h(1) finite` almost surely. Stationarity gives equal masses, upgrading inclusion to almost-sure equality. All-integer transport and a countable intersection force almost every path into either the all-finite or the all-infinite sector. A mixture remains possible; the all-infinite component is not excluded. Borel cylinder and stationary transport lemmas are proved in `StationaryEvents.lean`.

## Weighted gaps and excursions

For cutoff H let a low event mean h(t)<=H. Let G_m be a positive-length consecutive gap: low at0 and m, with no low time strictly between. For0<=k<m translate G_m to start at-k. These gap tiles are pairwise disjoint: two consecutive-low intervals containing time0 in their half-open interiors must have identical starts and ends.

Stationarity gives each length-m tile mass r_m=Prob(G_m), and there are m such tiles. Countable additivity gives

    sum_m m*r_m <= 1.

`GapPacking` proves real summability as well as this bound, not merely a totalized infinite sum. Recurrence, ergodicity and finite mean are not premises.

Let E_n be `longExcursion H L n`: low at0 and n, with no low time in[L,n), where L>0. For n>=L choose the last low time k<L. The configuration lies in the translate starting at k of G_(n-k). The finite union over k<L and stationarity bound its probability by a finite sum of r_(n-k). Since n=(n-k)+k, weighted and unweighted gap summability imply

    sum_n n*Prob(E_n) < infinity.

The n<L terms are finite in number. `ExcursionFirstMoment` proves this exact statement.

If c>0 instead gave Prob(E_n)>=c*n^(-12/7) for every n>=L+2, then n*Prob(E_n)>=c*n^(-5/7) on that tail, whose sum diverges. `PolynomialExcursionContradiction` proves the weighted identity and p-series comparison. It does not prove the lower bound for any actual critical Gibbs law.

## Assurance and remaining obligations

All required local mathematical files are included, with public Git-pinned Mathlib and Lean dependencies. Ordinary verification must reproduce all12 exact target bodies, all32 model-origin rows (24 available bodies and eight opaque proof-origin null values) and every owned declaration's transitive axiom closure. Full assurance additionally requires source-bound export/replay, trusted statement comparison, all six checker modes in both stages, a positive full rerun and actual semantic hostile controls. Ordinary compilation is lower assurance and remains labeled that way.

The broader argument still needs actual critical-parameter matching, the null-cylinder hypotheses for its selected limit, positive finite-component conditioning and phase normalization, finite-endpoint Gibbs identities, quantitative local probability estimates and localized coupling. Pressure/entropy laws, numerical enclosures and R9 are separate. These twelve supporting statements discharge none of those full headline obligations by themselves.
