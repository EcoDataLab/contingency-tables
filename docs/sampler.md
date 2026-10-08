# Exact small-table reference sampler

The implementation in `src/contingency115/tables.py` counts bounded integer tables exactly and samples from explicitly stated laws. Its role is an oracle for small instances, a baseline for methods with few commute modes, and a way to expose modeling differences. It is **not** an implementation of the polynomial-time sampler or FPRAS in OpenAI result #115, and it makes no new worst-case counting-complexity claim.

## Constraints and feasibility

`TableProblem` accepts nonnegative integer row and column margins, inclusive lower and upper bounds, and optional `(row, column)` structural-zero coordinates. Upper bounds are tightened by `min(row_margin, column_margin)`. A zero upper bound is a declared structural restriction; an absent or failed route lookup should not be turned into one without a modeling decision.

Malformed types, shapes, or supplied lower bounds exceeding supplied upper bounds raise. Legitimate but inconsistent constraints define an empty fiber: `count()` returns zero, `feasibility()` explains the failure, and `sample()` raises `InfeasibleTableError`. Contradictions implied by margins or structural zeros also give an empty fiber. The all-zero table is a singleton fiber. At least one row and one column are required.

`feasibility()` subtracts lower bounds and runs an integer Edmonds–Karp maximum flow on the remaining bipartite capacities. It returns a table witness when feasible. This catches collective sparse-support obstructions that checking each row or column alone misses. Feasibility does not imply that the subsequent exact counting calculation will fit its budget.

## Completion counts and exact uniform draws

For row index `i` and remaining column totals `s`, define `C(i,s)` to be the number of completions from row `i` onward. The recurrence is

$$
C(i,s)=\sum_{a\in A(i,s)} C(i+1,s-a),\qquad C(m,0)=1,
$$

where `A(i,s)` consists of bounded row vectors with the required row sum. Suffix lower and upper capacities prune infeasible residual columns. States `(i,s)` are memoized, along with their positive-completion transitions. The row generator uses iterative backtracking; the DP recurses over rows.

Tables have a lexicographic rank from `0` through `C(0,c)-1`. A row branch occupies a consecutive block with size equal to its completion count. Recursively locating a rank in these blocks gives `unrank`; adding the preceding block sizes gives `rank`. These are inverse bijections. A uniform integer rank therefore yields a uniform table, with no floating-point probabilities or MCMC burn-in choice.

```python
from fractions import Fraction
import random
from contingency115.tables import (
    TableProblem, ExactTableSampler, ProductWeights, ExactWeightedTableSampler,
)

problem = TableProblem([2, 2], [2, 2])
uniform = ExactTableSampler(problem)
assert uniform.count() == 3
table = uniform.sample(random.Random(115))
assert uniform.unrank(uniform.rank(table)) == table
```

`sample` needs a source whose `randrange(N)` returns a uniform integer in `[0,N)`. The default is `random.SystemRandom`; a seeded `random.Random` is useful for reproducible experiments. The probability statement is conditional on the uniform-integer RNG model. Rejection inside an RNG can have unbounded realized length, so this interface does not promise the paper's all-execution bounded approximate runtime.

## Two different weighted models

`ExactWeightedTableSampler` is a separate API so its output is not confused with a uniform table draw. `ProductWeights` accepts nonnegative integers or exact `Fraction` activities and an explicit `factorial_weight` flag:

$$
w_{\mathrm{table}}(X)=\prod_{ij}a_{ij}^{X_{ij}},\qquad
w_{\mathrm{worker}}(X)=\prod_{ij}\frac{a_{ij}^{X_{ij}}}{X_{ij}!}.
$$

The second is the conditional independent-Poisson law and, with fixed row totals, the corresponding labeled-worker assignment law after constants cancel. The first is a law on aggregate tables. Activities equal to one give table-uniform only for the first law. Activities encode a model; this package does not estimate them or establish that either model matches travel behavior.

The weighted recurrence multiplies each continuation mass by the product of its row's cell weights. At sampling time, rational branch masses are converted to proportional integers using a common denominator. All normalizers and returned probabilities are exact. Zero activities give zero mass to positive counts in their cells. A geometrically feasible fiber with zero total target mass raises `ZeroMassError` when a probability or sample is requested.

```python
worker = ExactWeightedTableSampler(
    problem, ProductWeights([[1, 1], [1, 1]], factorial_weight=True)
)
tables = list(uniform.tables())
assert [worker.probability(x) for x in tables] == [
    Fraction(1, 6), Fraction(2, 3), Fraction(1, 6)
]
```

The same three tables have probability `1/3` each under the uniform law. Multiplying activities by `alpha[i] * beta[j]`, with positive row and column factors, changes all table weights by the same margin-dependent constant and leaves either conditional law unchanged. This invariance is tested with exact rational factors.

## Resource limits and complexity

The numeric residual-state count can be as large as

$$
(m+1)\prod_j(c_j+1),
$$

before pruning, and each state can have many bounded row allocations. This is pseudopolynomial in numeric margins for a fixed number of columns and exponential when dimension varies; it is not polynomial in binary-encoded margins. Transposition can substantially change the number of residual states, but the best orientation depends on both dimensions and margin sizes. The caller can transpose both the problem and the activity matrix and measure it.

`max_states` and `max_transitions` cap distinct DP states and candidate row allocations. Exceeding either raises `ComputationBudgetExceeded`; the engine then remains failed, and no partial count or draw is returned. `tables(max_tables=...)` checks the complete count before starting enumeration. Its separate output cap does not invalidate an already complete DP. Python row-recursion exhaustion is also reported as `ComputationBudgetExceeded`.

These caps are not limits on wall-clock time, integer bit length, matrix input size, or the preliminary feasibility computation. Counts can be enormous; rational powers, factorials, and common denominators can be expensive even for a modest number of states. The engine caches transitions as well as states, so memory includes stored row vectors. The code uses arbitrary-precision exact arithmetic, not a bounded-bit machine implementation.

## Exact cycle heat-bath experiments

`src/contingency115/kernels.py` builds full rational transition matrices on a verified complete, enumerated fiber. It refuses missing or duplicate tables. The matrix size has its own cap; this is a small-instance diagnostic, not a production MCMC engine.

A simple even cycle in the allowed row/column bipartite graph gives an alternating signed direction `v`. Bounds specify an integer interval of shifts `t` with `X+t*v` feasible. For a fixed cycle, every table on the line has exactly the same line. A uniform draw over that **entire** line is reversible for the uniform table law. For a product-weight target, the code draws proportionally to the exact target weights along the line instead. Applying a uniform line draw to the factorial law would generally be wrong.

The cycle catalog and its exact selection probabilities are fixed by the input. A mixture of its conditional kernels preserves the law. Choosing only currently movable cycles with state-dependent renormalization is not implemented: the fixed-mixture proof would no longer apply. An empty catalog is a hold; singleton feasible lines are holds. An optional fixed holding probability is allowed. Zero-mass weighted lines are defined as holds, which does not affect target stationarity.

`four_cycles` supplies all allowed rectangles. `simple_cycles` supplies all simple cycles, or all up to an explicitly chosen even length. Full enumeration may be exponential and has both cycle-count and search-node budgets; a partial catalog is never silently returned after exhausting those budgets.

There is a useful connectivity fact when all simple cycles are included. For feasible `X != Y`, the signed difference `Y-X` has zero margins. Its positive/negative cells contain an alternating cycle. Moving one unit toward `Y` on that cycle stays within the interval between `X` and `Y`, so it respects every cell bound and reduces their entrywise distance. Repetition connects them. With strictly positive activities, each such move has positive heat-bath probability. Thus the full catalog connects every nonempty bounded fiber. This is a standard cycle-decomposition argument, **not a new mixing-rate bound**. Restricted catalogs must be checked separately.

A six-cell support makes the distinction concrete:

```text
allowed cells    feasible table A    feasible table B
1 1 0            1 0 0               0 1 0
0 1 1            0 1 0               0 0 1
1 0 1            0 0 1               1 0 0
```

All row and column sums are one. There is no allowed rectangle, so a rectangle-only kernel has two isolated states. The six-cycle heat bath chooses either table with probability `1/2` and connects the fiber in one draw. This verifies the sparse-support obstruction; it is not evidence that longer-cycle catalogs always improve computational efficiency. The optional NumPy gap calculation reports float64 diagnostics on the particular enumerated kernel and omits the cost of finding or executing a cycle.

## Synthetic commuting example and verification

Run the wholly synthetic fixture with no third-party dependencies:

```sh
PYTHONPATH=src python3 examples/sparse_commute.py --output reports/sparse-commute.json
PYTHONPATH=src python3 -m unittest discover -s tests -v
```

The three destination rows, five mode columns, and ten fictional workers have exactly **42** feasible tables. The conditional-Poisson normalizer is **582288**. Under the stipulated mileage assumptions, annual attributed commute VMT has mean **18700** under table-uniform and **196016150/12131** (about **16158**) under the activity-weighted worker law. The feasible range is **9460–25080**. These results agree with independent cell-by-cell enumeration. Exact model quantiles and cell expectations are included in the JSON; their spread is model uncertainty under stated synthetic controls, not a validated error bar for CBEI.

The optional `--spectral` run provides a negative control for claims about adding moves. The 12-rectangle catalog is already connected on this fixture. Replacing it with uniform selection from all 24 simple cycles changes the uniform-law spectral gap from about **0.10387** to **0.09783**, and the worker-law gap from about **0.11152** to **0.10421**. The gaps decrease because the mixture weights changed along with the catalog; all detailed-balance identities still hold exactly. Longer cycles fix the separate six-cycle support obstruction, but a larger catalog does not itself imply faster mixing. These are float64 diagnostics, before any transition-cost comparison.

Tests enumerate every binary `2 x 3` structural-zero pattern and every attainable margin combination, compare random small lower/upper bounded cases with independent cell enumeration, check the rank bijection, and exhaust the discrete random-choice tree for small weighted samplers. They also check Hall-type infeasibility, zero margins, budget failures before RNG calls, exact weighted detailed balance and stationarity, and the disconnected rectangle/six-cycle example. These are executable finite checks and ordinary mathematical arguments; this module has no Lean certification.
