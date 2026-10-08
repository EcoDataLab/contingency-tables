# An exact ordinary conditional-worker baseline

`contingency115.workers.OrdinaryWorkerSampler` samples an established fixed-margin distribution without enumerating aggregate tables. It assigns column labels to individual worker slots uniformly without replacement and returns only the aggregate table. This makes a useful baseline for conditional commuting ensembles when the intended law is independent worker allocation subject to fixed controls.

This is **not uniform sampling of aggregate tables**, a new mathematical result, or an implementation of the polynomial-time uniform sampler in OpenAI #115. The distinction already appears in the [CBEI methodology note](cbei-use-cases.md). Mature classical alternatives exist: [SciPy `random_table`](https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.random_table.html) implements Boyett and Patefield algorithms, and [R `r2dtable`](https://stat.ethz.ch/R-manual/R-devel/library/stats/html/r2dtable.html) uses Patefield's algorithm. SciPy documents an `O(K log N)` Patefield method, where `K` is the number of cells and `N` the total. The present implementation prioritizes a short integer-arithmetic correctness argument and exact small-case verification; it makes no claim to be the fastest implementation of this classical law.

## Distribution and scope

Let nonnegative integer row margins `r` and column margins `c` have common total `N`. Every cell is permitted, with no input cell bounds. For a feasible aggregate table `X`,

\[
\Pr(X)=\frac{\prod_i r_i!\prod_j c_j!}{N!\prod_{i,j}X_{ij}!}.
\]

This is the central conditional-worker, or conditional-independence, law. It is also the conditional-Poisson law with all activities equal to one. Strictly positive factorizable activities `a[i,j] = u[i] v[j]` give the same law because the row and column factors cancel under fixed margins. Arbitrary interactions do not cancel.

For margins `(2,2)` by `(2,2)`, the three possible top-left counts `0,1,2` have probabilities `1/6, 2/3, 1/6`. Uniform aggregate tables instead give each probability `1/3`.

The API deliberately accepts only two plain margin vectors. It has no `TableProblem`, bounds, structural-zero, or activity parameter. Do not strip bounds from an existing problem and present the result as a sample of that bounded problem. Rejection conditioning could in principle target a restricted version of this same law, but its acceptance probability and cost are outside this implementation.

## Why the draw is exact

Imagine `N` individual positions split into rows of sizes `r[i]`. An urn contains `c[j]` labels of column category `j`. At each position, draw a uniform integer from `0` through the remaining population minus one; use cumulative category counts to select and remove its label.

Any complete category sequence with these column totals has probability `prod(c[j]!)/N!`. A table `X` corresponds to `prod(r[i]!)/prod(X[i,j]!)` such sequences, giving the displayed table probability.

A Fenwick tree stores remaining category counts and selects an urn rank using logarithmic integer work. The implementation reserves the largest row for deterministic completion, sampling the other rows in their original order. Permuting the order of individual positions leaves the distribution unchanged. Once only one category remains, all further counts are deterministic. Both shortcuts marginalize choices that cannot affect the returned table; they do not condition on favorable outcomes.

Exactness assumes fresh uniform randomness: conditional on all past calls, each `randrange(stop)` call is uniform on the specified integer range. Marginal uniformity without this conditional property would not suffice. The default uses `random.SystemRandom`; reproducible experiments use `random.Random` seeds. There are no floating-point transition probabilities or floating-point acceptance tests.

## Budgets and cost

Construction validates and copies the margins, then determines a conservative bound `Dmax` on integer RNG calls:

* `Dmax = 0` if at most one row or one column has positive count.
* Otherwise `Dmax = N - max(r)`.

The constructor rejects a plan exceeding `max_draws` or dense output size `max_cells` before accepting an RNG or allocating the output matrix. The default limit is one million for each. It does not start drawing and later abandon unfavorable paths. That distinction prevents budget-dependent selection of successful samples. A plan may be rejected even though some realized paths would need fewer draws.

With `D <= Dmax` actual random calls, `m` rows, and `n` columns, the implementation uses

\[
O(mn+m+n+D\log(n+1))
\]

integer operations and `O(mn+m+n)` stored integers, including the dense output. The Fenwick structure itself occupies `O(n)` integers. Integers can contain `O(log(N+1))` bits, so these are operation and storage counts, not unit-cost bit-complexity claims. Uniform integer generation also has its own bit cost. Standard rejection-based integer RNGs have an unbounded worst-case number of internal random-bit attempts even though the number of requested integer draws is bounded.

In particular, balanced `2 × 2` margins `(2^b,2^b)` require a preflight bound of `2^b` draws. This algorithm is **not polynomial in binary margin length**. Conversely, one enormous row and a few small rows may be inexpensive because the enormous row is completed deterministically. The work report records actual draws, deterministically assigned workers, and Fenwick loop iterations rather than using the number of feasible aggregate tables as a runtime proxy.

```python
import random
from contingency115.workers import OrdinaryWorkerSampler, worker_linear_moments

sampler = OrdinaryWorkerSampler([4, 3, 3], [4, 2, 2, 2], max_draws=6)
draw = sampler.sample_with_stats(random.Random(115))
print(draw.table)
print(draw.random_draws, sampler.plan.maximum_random_draws)

# Rational/integer coefficients can describe a linear commute-VMT quantity.
coefficients = [[880, 440, 0, 0], [3520, 1760, 0, 0], [6600, 3300, 0, 0]]
moments = worker_linear_moments([4, 3, 3], [4, 2, 2, 2], coefficients)
print(moments.mean, moments.variance)
```

The example has ordinary support. It does not reuse the structural-zero restrictions in `synthetic_commute.json`.

## Exact linear moments without sampling

Under this same ordinary law, `E[X[i,j]] = r[i] c[j] / N`. The joint covariance is

\[
\operatorname{Cov}(X_{ij},X_{kl})=
\frac{(N r_i\mathbf1_{i=k}-r_ir_k)
      (N c_j\mathbf1_{j=l}-c_jc_l)}{N^2(N-1)}
\quad (N>1).
\]

For `G = sum(q[i,j] X[i,j])`, write

\[
S=\sum_{i,j}r_i c_j q_{ij},\quad
T=\sum_{i,j}r_i c_j q_{ij}^2,\quad
R_i=\sum_jc_jq_{ij},\quad C_j=\sum_ir_iq_{ij}.
\]

Then

\[
E[G]=S/N,\qquad
\operatorname{Var}(G)=
\frac{N^2T-N\sum_i r_iR_i^2-N\sum_jc_jC_j^2+S^2}{N^2(N-1)}.
\]

`worker_linear_moments` computes these expressions with exact rational arithmetic in `O(mn)` rational operations. It handles `N=0` and `N=1` separately as deterministic cases, accepts signed integer/Fraction coefficients, and rejects floating-point inputs. There is no numeric-worker-count loop or factorial computation. Large binary margins can therefore be inexpensive for these moments even when sampling is rejected.

This calculation includes all cell covariances. Treating cell counts as independent generally gives the wrong metric variance; for example, any additive row-plus-column coefficient matrix has zero variance under fixed margins. Exact linear moments do not provide quantiles, nonlinear model outputs, or uncertainty beyond the chosen law and fixed controls.

## Verification and synthetic benchmark

Run:

```sh
PYTHONPATH=src python3 -m unittest discover -s tests -p 'test_workers.py' -v
PYTHONPATH=src python3 experiments/worker_baseline.py
```

The tests expand the sampler's entire uniform-integer RNG decision tree and compare exact rational probabilities with a separate cell-box enumeration weighted by reciprocal factorials. Coverage includes every `2 × 3` and `3 × 2` margin pair with total at most four, further multistage `3 × 3` cases, zero margins, deterministic huge margins, and early deterministic completion. Other tests verify budgets before RNG, excluded API arguments, malformed values, a 100,000-worker sample, signed rational moments, the zero-variance control identity, and analytic moments at `2^200` scale.

[`reports/worker-baseline.json`](../reports/worker-baseline.json) records reproducible seeds, source hashes, exact synthetic metric moments, output hashes, validated margins, actual draw counts, and measured local timings. It includes ordinary tables up to one million workers, a many-category case, a huge-total case with only ten required random draws, a guarded completion-DP comparison targeting the same law, and a rejected `2^80` draw budget. These establish implementation behavior on synthetic inputs, not predictive accuracy or a production performance guarantee.

For CBEI use, the baseline is most useful as a controlled independence model and as a check on more expressive methods. It does not resolve population reconciliation, identify unavailable correlations, preserve staged WFH/other-mode behavior automatically, or replace total household VMT with commute VMT. Route-dependent interactions, genuine structural zeros, and cell caps require the other samplers or a separately justified method.
