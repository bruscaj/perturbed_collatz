# A near-extremal entropy argument for admissible Collatz words

[Read the TeX/PDF manuscript](paper.pdf) · [TeX source](paper.tex). Rebuild both papers with `python3 papers/build.py` from the repository root; `--check` compares deterministic clean rebuilds on the recorded TeX toolchain.
Jake S. Brusca, with ChatGPT assistance in derivation, writing, code and review.
Draft research contribution, 2026-11-27. This is a personal work in progress;
corrections and counterexamples are welcome.

**Evidence status.** The argument below is a written proof candidate, reviewed
in a separate AI context. It has not been refereed by a human expert, formalized
end to end, or independently kernel checked. The repository's abstract integer
Lean lemmas support only the finite prefix/depth and endpoint transformations.
They do not prove the pressure, entropy, asymptotic or source-equivalence claims
below. Finite exact tests check model translations; they do not establish limits.
No claim of priority or external acceptance is made.

The intended contribution is a rung entropy limit near maximal reward and its
near-extremal expansion. It addresses the rung interpretation of M4 near one,
the large-tilt convergence part of R8, and the proposed asymptotic in R9 of
Polson and Sokolov. It does not prove the complete R8 question, compute the
requested M4 entropy table, establish an unrestricted M4 limit, or imply
anything about integer Collatz cycles or convergence.

Primary source: Nicholas G. Polson and Vadim Sokolov, *On the Collatz
Conjecture: Martingales, Momentum and Continued Fractions*, edition 1 (2026),
[v1.4.0 ratchets chapter](https://github.com/VadimSokolov/collatz/blob/v1.4.0/book/chapters/ch10h_ratchets.tex),
labels `rrt:sec:m4`, `rrt:prob:r8`, `rrt:prob:r9`; the tag resolves to commit
`5840497a23fc0d64127b850aea68862d7c93f2b7`.
The [missed-problems chapter](https://github.com/VadimSokolov/collatz/blob/v1.4.0/book/chapters/ch10f_missed.tex)
uses unrestricted-limit wording for M4; the detailed ratchets discussion fixes
the rung subsequence. These formulations must be distinguished. The
[status register](../external_problems/README.md) records the source mismatch
and outstanding acceptance gates. The authors' [results index](https://vsokolov.org/books/collatz/results.html)
was checked on 2026-11-27; an open listing alone is not a novelty search.

## 1. Definitions and the proposed statement

All logarithms below are natural unless a base is displayed. Set

$$
\theta=\log_2 3,\qquad \beta=\theta-1,\qquad
\delta(r)=\lceil r\theta\rceil-r\theta.
$$

A **rung** is a positive integer r such that
$\delta(r)<\delta(t)$ for every positive integer t<r. At length r, a source
word is a tuple of positive integers k_0,...,k_{r-1} with prefix sums
$K_t=\sum_{i<t}k_i$, endpoint $K_r=\lceil r\theta\rceil$, and caps

$$
K_t\le \lfloor t\theta+\delta(r)\rfloor\quad(0\le t<r).
$$

Its reward and the phase-zero reference are

$$
\Phi(k)=\sum_{t=0}^{r-1}2^{K_t-t\theta},\qquad
B_r=\sum_{t=0}^{r-1}2^{-\{t\theta\}}.
$$

Let N(c,r) count these words with $\Phi(k)\ge cB_r$. The candidate result is:
for $0<\epsilon<2(\log 2)10^{-4}$, the limit

$$
\rho(1-\epsilon)=\lim_{\substack{r\to\infty\\r\text{ a rung}}}
 \frac{\log_{10}N(1-\epsilon,r)}r
$$

exists, and, as $\epsilon\downarrow0$ **after this length limit**,

$$
\rho(1-\epsilon)=\frac{3\epsilon}{2\log 2\log 10}
 \left[\log(1/\epsilon)-\log\log(1/\epsilon)
       +1+\log(2/3)+o(1)\right].
$$

At c=1 the rung population has exactly one word, so $\rho(1)=0$.
The displayed leading coefficient is approximately 0.93983174299; this decimal
is illustrative, not an independently certified numerical enclosure.

We use the following classical facts, with the stated hypotheses: an irrational
rotation has uniformly convergent averages, in its initial phase, for bounded
Riemann-integrable functions; finite independent bounded random variables obey
Chebyshev's inequality; a finite concave function is continuous on the interior
of its interval; and elementary calculus and the geometric series. There is no
assumption of independent symbols along an integer Collatz orbit.

## 2. Exact rung and depth transformations

The number theta is irrational: a rational identity theta=a/b would give
$2^a=3^b$, contrary to prime factorization. Irrational-rotation density gives
positive values delta(r) arbitrarily near zero; hence there are infinitely many
strict-record rungs. If r is a rung and 0<t<r, then delta(r)<delta(t), so

$$
\lfloor t\theta+\delta(r)\rfloor=\lfloor t\theta\rfloor.
$$

For x in [0,1), write

$$
L_t(x)=\lfloor x+t\theta\rfloor,\quad
x_t=\{x+t\theta\},\quad g_t=L_{t+1}-L_t\in\{1,2\}.
$$

The floor-endpoint model has K_0=0, K_n=L_n, positive integer increments and
K_t<=L_t. It is in bijection with integer profiles (j_0,...,j_n) satisfying

$$
j_0=j_n=0,\quad j_t\ge0,\quad
j_{t+1}\le j_t+g_t-1,
$$

by $j_t=L_t-K_t$; the inverse increments are
$k_t=j_t+g_t-j_{t+1}\ge1$. This is an equality of finite sets, not an
asymptotic approximation.

At a rung, take x=0. Passing from the source endpoint ceil(n theta) to
floor(n theta) decreases only the last increment by one. The source cap at
n-1 implies that this last increment was at least
$\lceil n\theta\rceil-\lfloor(n-1)\theta\rfloor\ge2$, so positivity is
preserved. Conversely raise the final increment by one. The reward does not
use K_n, so the transformation preserves it exactly.

For general phase define

$$
w_t=2^{-x_t},\quad B_n(x)=\sum_{t<n}w_t,\quad
E(j)=\sum_{t<n}w_t(1-2^{-j_t}),\quad
Z_n(x,\lambda)=\sum_j e^{-\lambda E(j)}.
$$

Thus the reward is B_n-E. Each profile has cost in [0,n], the zero profile is
legal, and the profile set is finite. Indeed its inverse positive increments
sum to L_n<=2n, so it is a subset of finitely many positive compositions.
Uniform equidistribution gives

$$
B_n(x)/n\longrightarrow b=\int_0^1 2^{-u}\,du=1/(2\log2)
$$

uniformly in x.

## 3. Positive runs and a bounded cutting cost

A positive run is a maximal consecutive interval [a,a+ell-1] on which j>0.
At its first site j_a=1 and g_{a-1}=2, so x_a is in [0,beta). Its first cost
is at least $2^{-\beta}/2=1/3$. Every subsequent positive site costs at least
1/4. Consequently a run of length ell has cost at least

$$
1/3+(\ell-1)/4\ge\ell/4.
$$

There are at most $4^{\ell+1}$ shapes for a run of length ell at a prescribed
start. To see this, include its two zero endpoints. Each of the ell+1 depth
increments d is at most one and their sum is zero. The numbers 1-d are
nonnegative integers summing to ell+1. Their number is
$\binom{2\ell+1}{\ell}\le4^{\ell+1}$; phase and positivity conditions can
only remove shapes.

Setting a cut depth j_l to zero factors the partition exactly. If j_l>0,
erase the unique positive run containing l. Erasure is legal, and the erased
profile, interval and shape determine the original profile. There are at most
ell intervals of length ell containing l. Hence, for lambda>=6,

$$
1\le\frac{Z_{l+m}(x,\lambda)}
 {Z_l(x,\lambda)Z_m(x_l,\lambda)}
\le e^{C_\lambda},\qquad
C_\lambda=\log\!\left(1+\frac{4q}{(1-q)^2}\right),\quad
q=4e^{-\lambda/4}<1.
$$

The cutoff is valid because $4e^{-3/2}<1$. In particular C_lambda<=C_6.

## 4. Pressure existence, including phase zero

For a fixed positive block length L put

$$
p_L(\lambda)=L^{-1}\int_0^1\log Z_L(x,\lambda)\,dx.
$$

The integrand is bounded and piecewise continuous: only finitely many floor
breakpoints affect the finite profile set, and within each cell its weights
are continuous. Divide n into L-blocks and a remainder. Iterating the cut
inequalities and using uniform equidistribution for rotation by L theta gives

$$
p_L\le\liminf_n\inf_x n^{-1}\log Z_n(x,\lambda)
\le\limsup_n\sup_x n^{-1}\log Z_n(x,\lambda)
\le p_L+C_6/L.
$$

The remainder has a bounded contribution at fixed L: Z>=1 and the number of
profiles is bounded in terms of L. Since L is arbitrary, the common limit
p(lambda) exists uniformly in x, with

$$
0\le p(\lambda)-p_L(\lambda)\le C_6/L\qquad(\lambda\ge6).
$$

The constant does not depend on lambda. Finite log partition functions are
convex, decreasing and 1-Lipschitz after division by length; these properties
pass to p. The corresponding **reward** pressure is

$$
P(\lambda)=\lambda b+p(\lambda)\qquad(\lambda\ge6).
$$

This proves the candidate large-tilt convergence assertion only. It does not
by itself prove differentiability or convergence for 0<=lambda<6.

## 5. Matching microcanonical growth by independent finite blocks

Define $f(\eta)=\inf_{\lambda\ge6}[p(\lambda)+\lambda\eta]$.
We claim that, for 0<eta<10^-4 and eta_n->eta, at any sequence of initial
phases,

$$
\lim_{n\to\infty}\frac1n\log\#\{j:E(j)\le n\eta_n\}=f(\eta).
$$

The upper bound follows from
$\#\{E\le n\eta_n\}\le e^{\lambda n\eta_n}Z_n(x,\lambda)$
for every fixed lambda>=6 and uniform pressure convergence.

For the lower bound, first ensure an interior finite-block minimizing tilt.
Allow singleton runs only at even eligible sites. They are nonadjacent, their
density is beta/2, and each costs at most 1/2. Thus

$$
p(6)\ge(\beta/2)\log(1+e^{-3})>1/100.
$$

For example beta>1/2, e^3<21 and log(1+u)>=u/(1+u) make the lower bound
larger than 1/88. Ignoring compatibility of all runs gives

$$
p(40)\le\frac{16e^{-10}}{1-4e^{-10}}<1/1000.
$$

The latter elementary comparison follows from e^10>20000. These exponential
inequalities can also be obtained directly from their Taylor series and tails.
Consequently p(40)+40eta<p(6)+6eta throughout 0<eta<=10^-4.

Fix 0<eta'<eta. For all sufficiently large L the same strict comparison holds
for p_L by the pressure bracket. Since p_L>=0, the function
p_L(lambda)+lambda eta' is coercive and has a minimizer lambda_L>6. Differentiating
the finite integral is justified by bounded block cost, and gives

$$
-p_L'(\lambda_L)=\eta'.
$$

On successive length-L blocks, independently sample profiles with probability
proportional to $e^{-\lambda_L E}$ at each block's actual starting phase.
Concatenate at depth zero and use the zero profile on the remainder. For fixed
L, equidistribution applied to the bounded piecewise-continuous block mean
shows that mean total cost/n tends uniformly to eta'. Independence and the
bound E_block<=L give total variance O(nL). Chebyshev therefore puts cost/n
in [eta'-d,eta'+d] with probability tending to one, for any
0<d<min(eta',eta-eta'). This event lies below n eta_n for all large n.

Undoing the Gibbs weights bounds its number of profiles below by

$$
\Pr(\text{event})\,
 \prod_{\text{blocks}}Z_L(x_{\text{block}},\lambda_L)
 \exp[\lambda_L n(\eta'-d)].
$$

Its logarithm/n has lower limit at least
p_L(lambda_L)+lambda_L(eta'-d). First let d decrease to zero. Then let L grow:
the uniform bracket |p-p_L|<=C_6/L implies convergence of the minimizing
values to f(eta'). Finally let eta' increase to eta. The function f is finite,
nonnegative and concave, so it is continuous at every eta>0. This proves the
claimed lower bound. No derivative of the infinite pressure was assumed.

At source rungs, E<=epsilon B_r corresponds to
eta_r=epsilon B_r/r->epsilon b. Therefore

$$
\rho(1-\epsilon)=f(\epsilon b)/\log10
$$

in the indicated near-one interval. At epsilon=0 every positive depth has
strictly positive cost, so the zero profile is the unique qualifying word.

## 6. An explicit large-tilt sandwich

At an interior site a (1<=a<n), a singleton is legal precisely when x_a is
in [0,beta); its activity
is $v_a=e^{-\lambda 2^{-x_a}/2}$, and is zero otherwise. Its mean activity is

$$
I(\lambda)=\int_0^\beta e^{-\lambda 2^{-u}/2}\,du
 =\frac1{\log2}\int_{1/3}^{1/2}\frac{e^{-\lambda y}}y\,dy.
$$

For an upper bound, ignore all incompatibility between positive runs and use
log(1+v)<=v. Singleton contributions have mean I; runs of length at least two
have total activity per possible start bounded by

$$
\sum_{\ell\ge2}4^{\ell+1}
 e^{-\lambda(1/3+(\ell-1)/4)}
 =\frac{64e^{-7\lambda/12}}{1-4e^{-\lambda/4}}.
$$

For a lower bound keep only nonadjacent singleton runs. Their finite partition
recurrence is H_m=H_{m-1}+v_m H_{m-2}, with empty-boundary values equal to one.
The ratio R_m=H_m/H_{m-1} lies between 1+v_m/(1+v_{m-1}) and 1+v_m. Since
log(1+u)>=u-u^2/2 for u>=0,

$$
\log R_m\ge v_m-v_mv_{m-1}-v_m^2/2.
$$

Every nonzero v_m is at most e^{-lambda/3}. Summing and phase averaging yields

$$
I(\lambda)-\tfrac32e^{-2\lambda/3}
\le p(\lambda)
\le I(\lambda)+\frac{64e^{-7\lambda/12}}{1-4e^{-\lambda/4}}.
$$

Substitute y=1/3+z in I. The factor 1/(1/3+z)=3+O(z) on [0,1/6], and its
bounded derivative controls the error after integration against e^{-lambda z}.
The missing tail beyond 1/6 is exponentially small. Thus

$$
I(\lambda)=\frac{3e^{-\lambda/3}}{\lambda\log2}
 (1+O(1/\lambda)),\qquad
p(\lambda)\sim\frac{3e^{-\lambda/3}}{\lambda\log2}.
$$

These are estimates in the untruncated profile model, not a finite-matrix
extrapolation. Also p(lambda)>0 at every finite lambda by the even-singleton
construction, and p(lambda)->0 by the upper bound.

## 7. The asymptotic Legendre minimum

The minimizing tilts for f(eta) escape to infinity as eta decreases to zero.
Indeed f(eta)->0 by first choosing a large fixed tilt and then decreasing eta;
whereas a bounded tilt interval has a positive lower bound for p. For every
fixed 0<d<1, the preceding asymptotic sandwiches p, for sufficiently large
tilt, between

$$
(1\pm d)\frac{3e^{-\lambda/3}}{\lambda\log2}.
$$

The minimizers of these two comparison objectives also escape to infinity,
so the sandwich applies to their infima for small eta. Put t=lambda/3 and
C=(1±d)/log2. The comparison objective is C e^{-t}/t+3eta t. Its unique
positive minimizer satisfies

$$
3\eta=C e^{-t}(1+1/t)/t.
$$

Writing A=log(1/eta) and taking logarithms gives

$$
t+\log t=A+\log(C/3)+\log(1+1/t),\qquad
 t=A-\log A+\log(C/3)+o(1).
$$

At the minimizer the first term is 3eta/(1+1/t). Therefore the comparison
minimum equals

$$
3\eta[A-\log A+1+\log(C/3)+o(1)].
$$

Taking eta to zero first and then d to zero squeezes the actual minimum to

$$
f(\eta)=3\eta\left[\log(1/\eta)-\log\log(1/\eta)
 +1-\log(3\log2)+o(1)\right].
$$

Substitute eta=epsilon/(2 log2) and divide by log10. The constants combine as
log(2 log2)-log(3 log2)=log(2/3), giving the expansion in Section 1.

## 8. Computation, formal coverage and remaining work

The [exact finite bridge oracle](../../certificates/external_problems/bridge.py)
and its recorded data check literal finite words against depth profiles, with
rational caps and rewards. They include nonrungs; a finite normalization witness
at n=2 has words (1,3),(2,2), rewards 5/3,7/3, and phase-zero B_2=5/3. Both
meet that fixed threshold, while only the latter meets the actual maximum.
This witnesses the difference of definitions; it does not by itself refute an
asymptotic limit. The scope of each executed check is recorded separately.

| Target | This draft supplies | Still required for the release goal |
| --- | --- | --- |
| Near-one rung M4 | Written entropy-existence and variational argument | Frozen full formal statement, end-to-end proof, certified entropy table, complete assurance |
| R9 | Written leading and second-order expansion | Full formal analytic bounds and limits, statement matching, fresh and independent checker replay |
| R8 | Written convergence for lambda>=6 | All-tilt convergence and differentiability, including critical tilt, independently scrutinized and fully formalized |
| Literal unrestricted M4 | Explicit source distinction and finite normalization witness | A proved all-length normalization theorem or a fully proved refutation under the literal convention |

Broader all-phase, all-tilt and critical Gibbs-law arguments are research
candidates. They are not premises of the near-extremal derivation above and
are not accepted theorems in this release. A separate critical argument would
need a rigorous stationary finite-depth law, preservation of its conditional
Gibbs identities, same-law excursion bounds and return-gap contradiction;
none is supplied by the finite oracle or supporting Lean library.

The outstanding trust gates include independent review of the full formal
statements against the pinned source, full analytic formalization and transitive
axiom audit, fresh proof replay and independently implemented checker coverage
of these actual headline claims. Supporting-theorem checks must remain labeled
as such. Closed review gates for supporting arithmetic do not close these gaps.
