# Exact sampling on cactus variable support

Some constrained tables can be sampled exactly without dynamic programming or a Markov chain. If the graph of **variable cells** is a cactus, the feasible tables are a Cartesian product of integer intervals. Counting, ranking, unranking, and uniform sampling then use arithmetic on the interval widths, without enumerating their values.

This is a structural special case of bounded contingency tables. We do not claim novelty for the underlying cycle-space factorization, a general bounded-table algorithm, or a replacement for the main #115 proof.

## Which graph matters

Create one vertex for each row and column. Include edge $(i,j)$ exactly when the effective upper bound exceeds the lower bound:

$$
U_{ij}>L_{ij}.
$$

Remove fixed cells, including fixed **positive** counts. Their contributions must still be included in the margins; equivalently, subtract them before working with the remaining flow. The implementation obtains its feasible base table from `TableProblem.feasibility()`, whose max-flow reduction subtracts all lower bounds, including fixed positive cells.

A cactus graph allows every edge to belong to at most one simple cycle. Distinct cycles may share a vertex. Forest edges, isolated vertices, disconnected components, and cycles with only one feasible parameter value are allowed.

The detector builds a spanning forest and each non-tree edge's fundamental cycle. It rejects if two fundamental cycles share any edge. This criterion is equivalent to the cactus property: fundamental cycles are simple, so a cactus cannot produce an overlap. Conversely, if this basis has disjoint edge supports, every simple cycle must be one basis cycle. A union of multiple basis cycles is disconnected or has a vertex of degree at least four and cannot itself be a simple cycle.

This graph test is sufficient, not necessary, for an easy table fiber. Margins may force additional cells even when their supplied bounds differ. The detector can therefore reject a noncactus graph whose feasible fiber happens to be small or a singleton. It raises `NotCactusError`, not an infeasibility error. An already-proved empty fiber returns count zero without testing the graph; its `support_checked` statistic is false.

## Why the parameters are independent

Let $X^0$ be a feasible integer table. For every fundamental cycle $C_k$, let $s^k$ have alternating $+1,-1$ entries around the cycle and zero elsewhere. Every such vector has zero row and column sums.

For any other feasible table $X$, its difference $X-X^0$ is an integer circulation. Subtract its coefficient on each non-tree edge times the corresponding fundamental cycle. The remainder is a circulation supported on a forest, and removing leaves proves it is zero. The coefficient is an integer because that cycle has entry $+1$ or $-1$ on its unique non-tree edge. Thus every feasible table has a unique representation

$$
X=X^0+\sum_k t_ks^k,\qquad t_k\in\mathbb Z.
$$

In a cactus, each cell belongs to at most one cycle. Its bounds consequently constrain only one parameter. For a cell with sign $+1$, the allowed interval is

$$
L_{ij}-X^0_{ij}\le t_k\le U_{ij}-X^0_{ij};
$$

for sign $-1$, it is

$$
X^0_{ij}-U_{ij}\le t_k\le X^0_{ij}-L_{ij}.
$$

Intersect these intervals around each cycle to obtain $[a_k,b_k]$. Each contains zero because the base table is feasible. All cells outside cycles remain fixed. Each cycle perturbation separately preserves the margins, even when cycles meet at an articulation vertex. Therefore

$$
\Omega\cong\prod_k\{a_k,a_k+1,\ldots,b_k\},\qquad
|\Omega|=\prod_k(b_k-a_k+1).
$$

`CactusTableSampler` uses a stable cycle order and mixed-radix ranks for this product. Its ordering is by cycle coordinates, not the existing DP sampler's lexicographic table order. A uniform integer rank in $[0,|\Omega|)$ gives a uniform table. A feasible forest has a singleton fiber; an empty product contributes one.

The max-flow algorithm does not augment one worker at a time: it augments by path bottlenecks. The graph decomposition and uniform rank operations also do not walk numeric interval widths. With ordinary binary integer arithmetic, the deterministic work in this structural algorithm is polynomial in the encoded input and output sizes. This statement concerns this cactus class and the deterministic operations. Sampling relies on the same uniform-integer RNG contract as the reference sampler; it does not promise a bounded number of random bits on every execution.

## Product-weight laws

For either supported law,

$$
w(X)=\prod_{ij}g_{ij}(X_{ij}),\qquad
g_{ij}(x)=a_{ij}^{x}\quad\text{or}\quad a_{ij}^{x}/x!,
$$

the disjoint cycle cells give the factorization

$$
w(X(t))=w_{\rm fixed}\prod_kw_k(t_k),\qquad
Z=w_{\rm fixed}\prod_k\sum_{t=a_k}^{b_k}w_k(t).
$$

The normalized parameters are independent. Factorials use the **full cell counts**, including lower bounds and fixed counts, not the shifted residual counts. Zero activities impose $X_{ij}=0$ on positive target support: on a cycle this fixes its parameter to a particular value; incompatible requirements or a positive fixed cell at zero activity produce total mass zero.

`CactusWeightedSampler` enumerates and normalizes each positive cycle interval separately. Work scales with the **sum** of these interval widths rather than their product, but this can still be exponential in binary margin size. It prepares every line, exact common denominator, and cumulative integer weight before any RNG call. Each draw then uses independent exact integer choices and a binary search in the cached cumulative weights.

The upfront planner has four limits: total line states, cell-weight evaluations, largest evaluated cell count, and an upper bound on stored coefficient bits. It evaluates these without powers or factorials. For example, $p^x\le2^{x\lceil\log_2p\rceil}$ and $x!\le x^x$ give conservative bounds on the raw numerator and denominator. A common denominator divides the product of line denominators, giving a bound on each integer cumulative weight. The planner includes all cached rational masses, line normalizers, cumulative integer weights, and the final normalizer.

`stored_coefficient_bits_bound` refers to those numerical coefficients. It does not bound Python object overhead, transient arithmetic operands, the input/base tables, elapsed time, or total memory. The largest-cell guard can reject cheap special cases; it deliberately does not attempt symbolic cancellation. Exceeding any limit raises before normalization and before RNG access. Empty and zero-mass targets report a zero normalizer, and sampling raises the corresponding error.

## Example and verification

```python
from contingency115.cactus import CactusTableSampler
from contingency115.tables import TableProblem

width = 2**200 + 17
problem = TableProblem(
    [2 * width, width, width], [width] * 4,
    [[width] * 4, [width, width, 0, 0], [0, 0, width, width]],
)
sampler = CactusTableSampler(problem)
assert sampler.count() == (width + 1)**2
assert sampler.rank(sampler.unrank(sampler.count() - 1)) == sampler.count() - 1
```

The two four-cycles share the first row. This example counts a fiber whose size needs **401 bits**, with no interval enumeration.

The wholly synthetic commuting example adds a fixed positive cell that creates overlapping cycles in the full positive support. Removing that fixed cell leaves the two cactus cycles. For width 2 there are nine tables; both count and all weighted probabilities agree with the independent DP implementation. Under its fictional distances, mode assignments, and activities, uniform mean VMT is **7260** and the bounded activity-weighted conditional-Poisson mean VMT is **404360/61** (about **6629**); that law's normalizer is **3721**. Its activities are nonseparable, so this is distinct from an ordinary worker-assignment urn law. These are model calculations, not evidence about travel accuracy.

```sh
PYTHONPATH=src python3 -S examples/cactus_commute.py
PYTHONPATH=src python3 -m unittest discover -s tests -p test_cactus.py -v
```

[`cactus-commute.json`](../reports/cactus-commute.json) records the full synthetic controls, cycle coordinates, all nine probabilities, exact metric moments, source hashes, large-rank checks, and the intentional weighted-budget rejection on the huge-width example.

Tests compare the detector against explicit simple-cycle enumeration on all **512** bipartite $3\times3$ support graphs and compare counts/ranks with DP for every binary $2\times3$ support and attainable margins. They also cover disconnected cycles, bridges, cycles sharing a vertex, fixed positive chords, nonzero lower bounds, empty and zero fibers, large binary margins, and malformed parameters. Eighty seeded small bounded cases compare both product laws with exact DP. A complete 36-branch random-choice tree verifies the two-cycle factorial sampler, and instrumented weights verify that budget failures happen before cell-weight evaluation.

## Application boundary

This is useful when a legitimate support structure decomposes into sparse independent cycles, and as another exact oracle for checking approximate samplers. Many destination-by-mode tables have a dense variable graph and will fail the test. Do not introduce structural zeros or fix uncertain counts to obtain a cactus. A commuting application using LEHD data still needs coherent populations, margins, routing assumptions, and a justified target law. The graph shortcut changes computation; it does not establish empirical validity.

This implementation and derivation were produced with AI assistance. They have executable finite checks and remain open to independent review; there is no Lean certification of this sampler.
