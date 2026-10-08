# Independent blocks for the bounded-counting weight oracle

The bounded-counting oracle can amortize its bin-chain burn-in across many
observations. Independent blocks, a spectral variance bound, and exact median
amplification give a conditional accuracy proof with explicit work allowances.
This is a change to the estimator in the bounded-table manuscript; it is not
an implemented physical oracle or a new compiled Lean theorem.

The implementation is [`block_budgets.py`](../src/contingency115/block_budgets.py),
with [finite-law tests](../tests/test_block_budgets.py) and a
[deterministic report](../reports/block-budget-comparison.json). The previous
independent-walk policy remains in [`budgets.py`](../src/contingency115/budgets.py).
All schedule decisions, binomial tails, and median comparisons are exact.

```sh
PYTHONPATH=src python3 -m unittest discover -s tests -p test_block_budgets.py -v
PYTHONPATH=src python3 experiments/block_budget_report.py --output reports/block-budget-comparison.json
```

The starting point is OpenAI `math` commit
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, specifically the
[bounded weight-evaluation section][evaluation]: `oracle-telescope`, the
lazy bin kernel, `bin-conductance`, `bin-mixing`, `inner-parameters`, and the
correction-arithmetic argument. [Error budgets](error-budgets.md) derives the
stronger mass, support, product, and rounding bounds reused here.

## Required chain and arithmetic hypotheses

For each annealing level, the actual finite bin kernel must be fixed, lazy,
reversible, and have a certified inverse spectral gap at most $K\ge1$.
The common bound must hold for all levels used by this oracle call. The code
accepts a bound; it does not certify an input matrix or a physical instance.
Every transition within a block must sample this kernel exactly. A fresh
randomized estimate substituted into a Metropolis ratio would generally define
a different kernel and is not covered by this argument.

The source implements its fixed kernel with dyadic proposal and acceptance
probabilities. Any generic kernel also needs an exact bounded-work transition
implementation and a certified per-step cost before these transition counts
can support a complete bit-cost bound.

Each block uses fresh independent randomness. At correction observations, each
conditional offset is fresh given the current bin; its random bits must also
be independent of future transition randomness. Reusing an offset through a
block, sharing block randomness, or feeding an offset bit into a subsequent
transition can invalidate the variance or median bound.

The ideal ratio observable lies in $[1/2,1]$. The correction can use the
published $[1/8,4]$ range or the source-specific $[9/20,10/9]$ range.
The latter requires the source's bin populations, $N\ge100dB$, at most $d$
free coordinates, and scaled penalty Lipschitz constant at most $1/8$.
A custom rational interval is a caller assertion of support, not a proof of
those geometric conditions. The source correction exponent must remain in
$[-2,2]$ for its numerical implementation. Every interval supplied to this
utility has strictly positive width and lower endpoint.

Write $j\in\{0,\ldots,H\}$ for the actual target index. The schedule uses

$$
 s=j+d\lceil\log_2 B\rceil,
 \qquad \pi_{a,\min}^{-1}\le2^s\quad(0\le a\le j),
 \qquad \sigma=\frac{\xi}{(j+2)(1+\xi)}<\frac1{10}.
$$

The published smaller tolerance remains selectable with
`sigma_policy="source"`. With positive source dimension, the default common
gap allowance is $K=2(1024d^2B)^2$, extracted from the source's conductance
proof before its displayed weakening. Known zero-dimensional and $j=0$
cases admit the source's special treatment; in particular $h_0=M_f$ is known.
The budget utility retains a conservative positive schedule rather than
dispatching those cases. At $H=0$, only $j=0$ is permitted, so a physical
implementation must take the exact branch instead of forming $j/H$.

## Stationary block variance, including conditional offset noise

Let $P$ be one such kernel. Observe a stationary chain every

$$
 S=\lceil qKr\rceil\quad\text{transitions},\qquad
 q=7/10>\ln2,\qquad r\ge1.
$$

On centered functions, the $L^2(\pi)$ norm of $P^S$ is at most
$\rho=2^{-r}$: laziness gives nonnegative eigenvalues and the gap gives
$(1-1/K)^S\le e^{-S/K}\le2^{-r}$. For the ratio, let $Y_t=R(V_t)$.
For the correction, let $Y_t=T(V_t,Z_t)$, using the independent conditional
offset rule above. Define $g(v)=\mathbb E[Y_t\mid V_t=v]$. At distinct
observation times, conditional independence gives

$$
 \operatorname{Cov}(Y_0,Y_k)
 =\operatorname{Cov}(g(V_0),g(V_k))
 =\langle g-\mu,(P^S)^k(g-\mu)\rangle_\pi.
$$

Thus its absolute value is at most
$\rho^k\operatorname{Var}(g(V_0))\le\rho^k\operatorname{Var}(Y_0)$.
For $N\ge1$ observations, expanding the variance of the sum yields

$$
 \operatorname{Var}(\overline Y)
 \le\frac{\operatorname{Var}(Y)}{N}
 \left(1+2\sum_{k\ge1}\rho^k\right)
 =\frac{F_r\operatorname{Var}(Y)}N,
 \qquad F_r=\frac{2^r+1}{2^r-1}.
 \tag{1}
$$

For $Y\in[a,b]$ with $0<a<b$, the inequality
$\operatorname{Var}(Y)\le(b-\mu)(\mu-a)$ implies

$$
 \frac{\operatorname{Var}(Y)}{\mu^2}
 \le v(a,b)=\frac{(b-a)^2}{4ab}.
$$

This follows by maximizing the left bound over $\mu\in[a,b]$; its
maximum occurs at $2ab/(a+b)$. In particular,

$$
 v_R=\frac18,\qquad
 v_T=\frac{14161}{64800}
 \quad\text{for the sharper source correction interval}.
$$

Choose an exact rational target $p\in(0,1/4]$ and

$$
 N_R=\left\lceil\frac{F_rv_R}{p\sigma^2}\right\rceil,
 \qquad
 N_T=\left\lceil\frac{F_rv_T}{p\sigma^2}\right\rceil.
 \tag{2}
$$

Chebyshev and (1) make the relative-error probability of each ideal stationary
block mean at most $p$. Both counts are at least one, including for very narrow
custom correction support. The default is $p=1/8$; $p=1/4$ remains selectable.
No claim is made that one fixed $p$ optimizes every parameter tuple or cost model.

## Exact amplification with a bounded integer search

Take the median of an odd number $M$ of independent block means for each
factor. If the median lies outside the desired interval, a strict majority
of blocks fail. Even if their failure probabilities differ, independent
indicators with probabilities at most $p$ are stochastically dominated by
$\operatorname{Binomial}(M,p)$. For $p=x/y$ in lowest terms, its exact tail is

$$
 T_M(p)=\frac1{y^M}
 \sum_{t=(M+1)/2}^{M}\binom Mt x^t(y-x)^{M-t}.
 \tag{3}
$$

Set $L=\lceil\log_2[4(j+1)/\theta]\rceil$ and select the smallest odd
$M$ for which $T_M(p)\le2^{-L}$. All $j+1$ median factors are accurate
except on an event of probability at most $(j+1)2^{-L}\le\theta/4$.
Different factors need no independence for this union bound.

This exact search has a proved finite cap. For $M=2m+1$ and
$X\sim\operatorname{Binomial}(M,1/4)$, Markov applied to $3^X$ gives

$$
 T_{2m+1}(1/4)\le\frac12\left(\frac34\right)^m.
$$

Taking $m=3(L-1)$ suffices since $(3/4)^3<1/2$, so $M\le6L-5$ for
all allowed $p$. For $p\le1/8$, use $7^X$ instead to obtain

$$
 T_{2m+1}(p)\le\frac14\left(\frac7{16}\right)^m.
$$

For $L\ge2$, $m=L-2$ suffices; for $L=1$, one block suffices. Thus the
implementation uses the smaller cap $\max\{1,2L-3\}$ for $p\le1/8$.
The search and its integer operands have polynomial bit complexity in $L$
and the encoding length of $p$. The observation counts themselves grow as
$1/p$; an arbitrarily tiny user-supplied $p$ is not a polynomial-time choice
in its encoding length alone. Likewise, transition counts grow with the
integer spacing parameter $r$, rather than its binary encoding length.
Polynomial-work claims use fixed $p,r$, as in the defaults, or separately
justified polynomial bounds on $1/p$ and $r$.

For comparison, `median_policy="hoeffding"` chooses the least odd integer
at least $qL/[2(1/2-p)^2]$. Hoeffding then gives a tail at most $2^{-L}$.
The exact policy finds the least count for the worst-case binomial bound;
it need not be the least count for a particular chain or observable.

## Burn-in, offsets, and the full error allowance

There are $C=(j+1)M$ independent block starts and at most
$dMN_T$ scalar offset draws. Put

$$
 Q=C+dMN_T,\qquad
 \ell=\left\lceil\log_2\frac{8Q}{\theta}\right\rceil,
 \qquad
 t_0=\left\lceil qK(s/2+\ell-1)\right\rceil.
 \tag{4}
$$

The stronger source mixing inequality
$\|P^{t_0}(x,\cdot)-\pi\|_{\rm TV}
\le\tfrac12\sqrt{\pi(x)^{-1}-1}\,e^{-t_0/K}$
makes every block start accurate to $2^{-\ell}$. Couple each start to an
independent stationary start and use the same exact transition randomness
thereafter. Once two starts match, the complete bin trajectories match; there
is no additional per-transition coupling charge. Approximate scalar offsets
can be coupled conditionally on matching bins to exact uniform draws, each
with error at most $2^{-\ell}$. The probability of any discrepancy is at most
$Q2^{-\ell}\le\theta/8$. The statistical and coupling failure probabilities
therefore sum to at most $3\theta/8<\theta$.

The source's fixed-depth root computation gives each correction evaluation
a deterministic pointwise relative error at most $\sigma$ throughout the
larger tolerance range. Since values are positive, the same bound holds for
each block mean. Order statistics are coordinatewise monotone, so it also
holds for their medians even if numerical approximation changes the ordering:
if $(1-\sigma)x_i\le\widetilde x_i\le(1+\sigma)x_i$ for all $i$, then

$$
 (1-\sigma)\operatorname{med}(x)
 \le\operatorname{med}(\widetilde x)
 \le(1+\sigma)\operatorname{med}(x).
$$

Thus the source telescope has exactly $j+1$ empirical multiplicative errors
and one correction-rounding error. With $n=j+2$ and the chosen $\sigma$,

$$
 (1-\sigma)^n\ge1-n\sigma\ge1-\xi,
 \qquad
 (1+\sigma)^n\le\frac1{1-n\sigma}\le1+\xi.
$$

The last inequality is equality for the product tolerance and also holds for
the smaller source tolerance. The preceding inequality follows by bounding
each binomial coefficient by $n^k$ and extending to the geometric series.
A median generally is biased; this
proof needs its high-probability interval, not unbiasedness.

Medians preserve support. Every ratio median stays in $[1/2,1]$, and the
rounded correction median stays in $[1/16,8]$ under the source ranges and
rounding hypotheses. Consequently the unconditional bound
$M_f2^{-j}/16\le\widehat h\le8M_f$ remains valid, even on failure events.
All loops, powers, sums, and median comparisons have predetermined bounds.
Exact rational insertion computes a median in at most $M(M-1)/2$ comparisons
and as many element moves. A mean only adds the bounded source outputs and
divides by its deterministic observation count. Even without cancellation,
its numerator and denominator lengths are bounded by the sum of its input
lengths plus the encoding length of that count. A median selects one such
mean; each comparison cross-multiplies two polynomial-length operands.
The final product adds the bit lengths of its factors. Thus polynomially many
observations of the source's polynomial-length outputs suffice for the
representation bound. A complete revised machine-cost proof still needs the
actual oracle program and its parameter-length conversion.

## What the work comparison does and does not show

Using (2)--(4), the exact operation allowances are

$$
\begin{aligned}
 \text{bin transitions}
   &=Ct_0+M\{j(N_R-1)+(N_T-1)\}S,\\
 \text{ratio evaluations}&=jMN_R,\\
 \text{correction evaluations}&=MN_T,\\
 \text{scalar offset draws}&\le dMN_T.
\end{aligned}
$$

The report also counts accumulation, division, and median-comparison
allowances. These are separate categories, with different operand sizes and
costs. More spacing between observations decreases covariance and evaluations
but usually increases transitions. Fewer transitions alone cannot establish
a wall-clock speedup, especially when correction arithmetic is expensive.

For the abstract tuple $d=19,B=1000,H=j=100,\xi=10^{-3},\theta=10^{-6}$,
using the same source-derived gap bound and sharper correction support:

| Block policy | Blocks per factor | Independent/block transitions | Block/independent correction evaluations |
|---|---:|---:|---:|
| $p=1/4$, exact tail, $r=1$ | 121 | 6.075 | 34.571 |
| $p=1/8$, exact tail, $r=1$ | 43 | 8.547 | 24.571 |
| $p=1/8$, exact tail, $r=2$ | 43 | 7.692 | 13.650 |
| $p=1/8$, exact tail, $r=4$ | 43 | 5.656 | 9.282 |
| $p=1/8$, Hoeffding, $r=1$ | 73 | 5.034 | 41.713 |

Here the independent comparator is the improved Bernstein policy, using the
same $\sigma$, support, actual index, and gap bound. The default block policy
reduces both transition and evaluation allowances by about 29% against the
quarter-failure block policy on this tuple. At $H=j=10000$, the default has
210.95 times fewer transition allowances than the independent comparator but
24.56 times more correction evaluations.

These tuples are schedule calculations, not constructed physical table
instances. The report includes a low-mixing-cost tuple with $K=2$ where the
default block policy uses about 1.30 times **more** transitions and 14.90 times
more correction evaluations. It also reports an actual-index-$1$ comparison.
No timings were collected and no universal best policy is claimed.

The tests enumerate finite two-state block laws, including fresh conditional
noise, and compare exact moments and median-tail probabilities. Negative
controls show how shared offsets, shared block failures, and reuse of future
transition bits defeat the corresponding proof steps. Tests also cover exact
tail minimality, boundary inputs, very narrow custom support, and numerical
median ordering changes. Finite checks support the argument but do not replace
the general proof or certification of a real bin chain.

## Integration boundary

The change is at the manuscript oracle interface: positive rational output,
the stated unconditional range, accuracy with failure probability at most
$\theta$, and bounded polynomial work under the supplied hypotheses. Existing
Lean `CompanionOracleEstimator.innerTolerance` uses
$\epsilon/[200(j+1)]$ and its `GoodEstimate` interface already contains rounded
factors. Neither the larger tolerance nor medians have been substituted into
that compiled interface here. They need an explicit new estimator-interface
bridge before any claim about the compiled theorem.

This is also a changed random program. If its law is later used in an exact
correction or transition tabulation, that work must propagate the actual
block/median law, deterministic loop bounds, and reserved random bits. Reusing
an independent-sample law or denominator from the previous program is invalid.

[evaluation]: https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/build/sections/evaluation.tex
