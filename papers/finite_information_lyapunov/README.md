# Finite-information Syracuse potentials: density, rate and depth-one infimum

[Read the TeX/PDF manuscript](paper.pdf) · [TeX source](paper.tex). Rebuild both papers with `python3 papers/build.py` from the repository root; `--check` compares deterministic clean rebuilds on the recorded TeX toolchain.
Jake S. Brusca, 27 November 2026. ChatGPT assisted with the ideas, proof, writing and review. **Status: written draft. The public `lean/external_analysis/` package proves all14 frozen depth-one targets using pinned mathlib; at source commit `8524770`, its clean build, exhaustive axiom audit, sandbox replay, frozen comparison, all six bundled checker modes and nine hostile fixtures passed ([receipts](../../verification/external_analysis/README.md)). Later manuscript changes require final-tree regression CI. No human expert refereeing is claimed.** Separate AI contexts reconstructed the argument and checked the source model; this is not external acceptance.

The manuscript develops literal arbitrary finite-depth densities, explicit inverse-depth bounds, and the exact depth-one infimum/nonattainment theorem for the run-length-only O3′ information class. See the [source and status register](../external_problems/README.md). Finite arithmetic for the series is reproduced by `python3 certificates/external_problems/verify.py` from the repository root. No ordinary Collatz convergence follows.


The [finite-depth density library](../../lean/external_population/README.md) passed full independent gates at8746e08. The [rate library](../../lean/external_rate/README.md) implements all eleven required frozen source proofs, with fresh type/axiom checks of765 theorem/helper closures. Its full replay/comparator/six-checker and hostile-control gates remain pending. The expanded [rate reconstruction](../../lean/external_rate/RATE_PROOF.md) provides the full arithmetic population, marker and Cantelli arguments. Exact higher-depth optimization, the optional stronger liminf and sharp constants remain open.

The depth-one derivation below retains its own exact scope.

## Related work and attribution

Finite parity coding and residue-class counts are classical: [Terras1976, §1](https://doi.org/10.4064/aa-30-3-241-252), and [Bernstein–Lagarias1996](https://doi.org/10.4153/CJM-1996-060-x) on the2-adic conjugacy. Our odd accelerated grouping, joint exit/block cylinders and relative odd-seed normalization are checked explicitly; they do not assert independence along one fixed integer trajectory.

The cycle obstruction is related to [Karp's finite minimum-cycle-mean theory](https://doi.org/10.1016/0012-365X(78)90011-0). Our countably infinite weighted failure objective and arbitrary corrections require their own proof. The nonattainment argument uses [Dirichlet's approximation method](https://doi.org/10.1017/CBO9781139237338.037) with an explicit conversion to positive near-integer returns. The public formalization credits [mathlib](https://arxiv.org/abs/1910.09336); its actual version is pinned in the lockfile. These references identify prior methods without establishing novelty or human acceptance.

## Candidate mathematical statement

For positive odd x, put S(x)=(3x+1)/2^v₂(3x+1), r(x)=v₂(x+1), and V_f(x)=log x+f(r(x)), where f is any real-valued function on positive integers. Failure means V_f(S(x))≥V_f(x). Relative density is normalized by the number of positive odd integers ≤X.

For every such f the failure density d(f) exists. Its infimum p₁ is

p₁=Σ_(r≥1)2^(−r)[1/2−2^(−K_r)],  K_r=floor(1+r log₂(3/2)).

No f attains this infimum. The partial sum through M has remainder between zero and 2^(−M−1).

## 1. Exact population partition

Set a=log(3/2)>0 and b=log 2>0. If r(x)=r≥2, write x=2^r u−1, u odd. Then 3x+1=2(3·2^(r−1)u−1), so K(x)=1 and S(x)+1=3·2^(r−1)u. Thus r(S(x))=r−1. The set r(x)=r is one odd residue class modulo 2^(r+1), hence has relative odd density 2^(−r).

If r(x)=1, then K(x)≥2. Fix k≥2 and next length r≥1. The exact valuation K(x)=k is one odd class modulo 2^(k+1). On it, x=x₀+2^(k+1)t gives S(x)=S(x₀)+6t. Since 3 is invertible modulo every power of two, imposing v₂(S(x)+1)=r selects one further class modulo 2^r in t. This exit edge therefore has relative odd density 2^(−k−r).

All positive odd inputs fall into these ascending edges r→r−1, r≥2, or exits 1→r with k≥2. Their weights sum to

Σ_(r≥2)2^(−r)+Σ_(r≥1,k≥2)2^(−r−k)=1/2+1/2=1.

This partition concerns initial seed populations and uses no convergence assumption. In particular x=1 is the exit k=2,r=1; it is always a failure, but a single integer has zero density.

## 2. Symbolic failure and density existence

For every edge the actual logarithmic increment is

log(S(x)/x)=log 3−K(x)log 2+log(1+1/(3x)).

The final term is strictly positive and tends to zero as x→∞. Define the symbolic edge gains

A_r=a+f(r−1)−f(r),
E_(r,k)=a−(k−1)b+f(r)−f(1).

On each fixed edge cylinder, the asymptotic failure indicator is exactly 1_(A_r≥0) or 1_(E_(r,k)≥0). A zero symbolic gain is a failure for every actual seed in that cylinder.

For any ε>0 retain finitely many ascending and exit edge cylinders with total density >1−ε, which is possible because the positive weights sum to one. On each retained cylinder the indicator eventually stabilizes; their finite union therefore has its predicted failure density. The complement is the complement of a finite dyadic cylinder union and has density <ε. Upper and lower densities of the full failure set differ by at most ε. Sending ε→0 proves density existence and the weighted formula

d(f)=Σ_(r≥2)2^(−r)1_(A_r≥0)+Σ_(r≥1,k≥2)2^(−r−k)1_(E_(r,k)≥0).

This proof permits arbitrary unbounded f because it truncates cylinders, not function values.

## 3. Mandatory positive cycles

Follow the exit 1→r with k≥2, then the ascending edges r→r−1→…→1. The sum of symbolic gains is

E_(r,k)+Σ_(j=2)^r A_j=ra−(k−1)b.

The correction values telescope. This sum is never zero: equality would imply 3^r=2^(r+k−1), impossible for positive integers r. It is positive exactly for 2≤k≤K_r, where K_r=floor(1+ra/b). If all ascending edges through r are strictly good, every such exit must fail.

Put T_r=Σ_(k=2)^K_r 2^(−r−k)=2^(−r)(1/2−2^(−K_r)). The formula also holds when K_r=1, giving the empty sum zero.

If some ascending edge fails, let L≥2 be its least source. Every positive cycle of height r<L then forces its own exit to fail, and the ascending edge L itself fails. Their disjoint weights give

d(f)≥q(L):=2^(−L)+Σ_(r<L)T_r.

If none fails, every positive-cycle exit fails, giving d(f)≥q∞:=Σ_(r≥1)T_r.

A direct subtraction gives

q(L)−q(L+1)=2^(−L−K_L)>0.

Since q(L)→q∞, every finite L satisfies q(L)>q∞. Thus d(f)≥q∞ for every correction f.

## 4. Approaching the bound

For c>a let f_c(r)=c(r−1). All ascending gains equal a−c<0. Each exit gain is

ra−(k−1)b+(r−1)(c−a).

As c↓a this converges to the nonzero cycle gain, so every exit indicator eventually equals the mandatory positive-cycle indicator. Summability of the exit weights (total 1/2) gives dominated convergence d(f_c)→q∞. Hence p₁=q∞.

Because T_r≤2^(−r−1), the series remainder after M is at most Σ_(r>M)2^(−r−1)=2^(−M−1). Floor thresholds can be computed without transcendental approximations: ra>(k−1)b iff 3^r>2^(r+k−1).

## 5. Nonattainment

If an ascending edge fails, Section 3 already gives d(f)>p₁. Otherwise all ascending gains are negative. Set δ=f(2)−f(1)−a>0. For every r≥2, summing strictly positive increment surpluses gives

f(r)−f(1)−(r−1)a≥δ.

The number α=a/b is irrational: if α=m/n were rational, then 3^n=2^(m+n), impossible. There are positive integers r, arbitrarily large, with fractional part {rα} arbitrarily close to one. An elementary proof uses pigeonhole approximation to obtain q>0 with distance of qα to an integer <ε. If its fractional part is already near one, use r=q. Otherwise its positive fractional part γ is small and taking m=floor(1/γ) makes {mqα}=mγ lie within γ of one; irrationality excludes equality. Repeating at smaller ε gives arbitrarily large such r.

Choose r≥2 with b(1−{rα})<δ, and k=K_r+1. Then k−1=ceil(rα), so this exit has negative cycle gain

ra−(k−1)b=−b(1−{rα})>−δ.

Its actual symbolic gain is that cycle gain plus f(r)−f(1)−(r−1)a, which is strictly positive. It therefore fails in addition to every mandatory positive-cycle exit. Its weight 2^(−r−k)>0 gives d(f)>p₁. No correction attains the infimum.

## Exact finite receipt

For M=80, the independently computed enclosure is

24353541309990355464286619961554936997 / 170141183460469231731687303715884105728

≤ p₁ ≤

24353541309990355464286690330299114661 / 170141183460469231731687303715884105728.

Its width is 1/2417851639229258349412352 = 2^(−81). Both endpoints display approximately 0.14313725116205436 at ordinary machine precision. The enclosure depends analytically on the preceding infinite-series theorem; finite arithmetic alone does not certify that theorem or source equivalence.
