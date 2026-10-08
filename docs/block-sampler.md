# Exact factorization over graph blocks

Bounded table fibers factor across the biconnected edge blocks of their variable-cell support graph. This extends the cactus sampler: cycles may overlap inside a block, while different blocks remain independent after their incident margins are fixed. The implementation uses cycle coordinates for simple-cycle blocks and the existing exact DP for complex blocks.

This is an application of classical circulation and graph-block structure, not a new priority claim or a general polynomial-time counting algorithm.

## Factorization theorem

Start with a nonempty bounded integer-table fiber and a feasible table $X^0$. Remove all fixed cells, including positive cells with $L_{ij}=U_{ij}$, from the bipartite support graph. The remaining edges have $U_{ij}>L_{ij}$. Split this graph into biconnected edge blocks; a bridge is a one-edge block.

For a non-bridge block $B$, define its local margins from the base table:

$$
r_i^B=\sum_{j:(i,j)\in B}X^0_{ij},\qquad
c_j^B=\sum_{i:(i,j)\in B}X^0_{ij}.
$$

These margins are the same for **every** feasible table, even when the row or column vertex is shared by multiple blocks.

To prove this, take the integer difference $\Delta=X-X^0$. Orient positive entries from row to column and negative entries in the opposite direction. Zero row and column sums make this an integer circulation. Decompose it into signed simple cycles. Every simple cycle lies inside one biconnected edge block, so the restriction of $\Delta$ to each block has zero incident row and column sums. A bridge belongs to no cycle and therefore has difference zero.

Conversely, choose any feasible local table on each block with margins $(r^B,c^B)$ and the original cell bounds. Insert these disjoint edge sets into $X^0$, leaving fixed cells and bridges unchanged. Each local replacement preserves its incident totals, so all global margins and bounds are preserved. Restriction and insertion are inverse maps. Thus

$$
\Omega\cong\prod_B\Omega_B,\qquad
|\Omega|=\prod_B|\Omega_B|.
$$

The local margins do not depend on which feasible witness was chosen. Shared articulation vertices cause no extra summation or coupling: their contribution from each block is invariant.

For any nonnegative product-cell law,

$$
w(X)=\prod_{ij}g_{ij}(X_{ij}),
$$

disjoint block edge sets also give

$$
Z=w_{\rm fixed}\prod_B Z_B.
$$

When this product is positive, the block tables are independent under the normalized law. A zero fixed-cell factor or zero block normalizer proves the whole target has zero mass. Both aggregate activity weights and factorial conditional-Poisson weights satisfy this factorization. Full cell counts enter the factorials; lower bounds are not subtracted from factorial arguments.

## Implementation

[`block_sampler.py`](../src/contingency115/block_sampler.py) finds edge blocks with iterative depth-first search and a low-link edge stack. Tarjan's original paper presents the classical biconnected-component algorithm: [R. Tarjan, *Depth-First Search and Linear Graph Algorithms*, SIAM Journal on Computing 1(2), 146–160 (1972)](https://epubs.siam.org/doi/10.1137/0201010). The DFS traversal itself is linear in vertices and edges after the dense input scan. Canonical sorting, local-table construction, and the existing integer max-flow feasibility routine add separate preparation costs.

Each local problem includes its incident rows and columns. Positions between those vertices that are **not** edges of that block receive local bounds zero, even if the corresponding global cell has a fixed positive count or belongs elsewhere. Such cells contribute through their own block or the fixed factor, exactly once. Local zero-padding has weight one.

Bridges and original fixed cells are constants. A non-bridge block with as many edges as vertices is a simple cycle and uses the frozen cactus implementation. Other blocks use `ExactTableSampler` or `ExactWeightedTableSampler`. Complex blocks can still have expensive DP state spaces, and bounds may imply simplifications that this first implementation does not discover.

Uniform ranks are mixed-radix products of each factor's own exact rank. They are not the whole-table DP's lexicographic ranks. Sampling a uniform global rank avoids walking the product fiber. The weighted sampler instead draws independently from the fully normalized local target laws and inserts the resulting local tables into the feasible base.

The RNG premise is explicit: each `randrange(stop)` must be uniform on its requested range **conditional on all preceding calls**. Uniform marginal distributions alone are insufficient. Reusing one uniform rank across two nontrivial factors can restrict the output to a diagonal of their Cartesian product. The test suite includes that deliberately correlated source as a negative control. `SystemRandom` is the default; seeded `random.Random` is used only for reproducible examples under the stated idealized RNG contract.

```python
from contingency115.block_sampler import BlockSamplerBudget, BlockTableSampler
from contingency115.tables import TableProblem

problem = TableProblem(
    [6, 3, 3], [2] * 6,
    [[2] * 6, [2, 2, 2, 0, 0, 0], [0, 0, 0, 2, 2, 2]],
)
sampler = BlockTableSampler(
    problem,
    budget=BlockSamplerBudget(
        max_dp_states_total=18,
        max_dp_transitions_total=28,
    ),
)
assert sampler.count() == 49
assert sampler.rank(sampler.unrank(48)) == 48
```

Here two $K_{2,3}$ blocks share the first row. Each local fiber has seven tables, giving $7^2=49$ globally. The cactus-only detector correctly rejects their overlapping cycles; the block sampler delegates them to two small DPs.

## Budgets and preparation

`BlockSamplerBudget` distinguishes limits shared across the whole computation from ceilings on an individual DP block:

| Fields | What is limited |
|---|---|
| `max_dp_states_total`, `max_dp_transitions_total` | Sum of DP states and candidate row transitions across all processed complex blocks, including work in a failed DP block |
| `max_dp_states_per_block`, `max_dp_transitions_per_block` | Independent ceiling for each complex block; the tighter of this ceiling and the remaining shared allowance is passed to the existing DP |
| `max_cycle_line_states_total`, `max_cycle_weight_evaluations_total` | Shared preparation allowances for weighted cycle factors |
| `max_cycle_stored_weight_bits_total` | Sum of the cactus planner's conservative bounds on retained cycle-weight coefficients |
| `max_weight_cell_value`, `max_raw_cell_weight_bits` | Conservative preflight on each potentially evaluated weighted cell, before powers or factorials |
| `max_cells` | Original matrix size before feasibility/decomposition |

The raw-cell bit preflight bounds numerator/denominator sizes with integer exponents and a conservative factorial bound. It does **not** bound DP completion-mass bits, the product normalizer, or total memory. The cycle coefficient allowance excludes DP caches and transient operands. State/transition counters also exclude graph decomposition, max-flow work, cycle-coordinate arithmetic, and RNG internals. These are scoped algorithmic limits, not a total runtime or memory budget.

The engine prepares every required factor before returning a positive count/normalizer or using an RNG. A fully normalized zero factor can end preparation early because the total product is then exactly zero. Budget exhaustion leaves the engine failed: later calls raise the same resource failure, with no partial product or draw. For DP-based weighted sampling, rational branch choices are converted to integers while walking the already-complete DP; their arithmetic and RNG limitations remain those of the original sampler. All budget-limited normalizations have already finished by that point.

## Synthetic benchmark

In a star of $k$ complex $K_{2,3}$ blocks sharing one row, each local first row is $(1,1,1)$ or one of six permutations of $(0,1,2)$. Hence there are exactly $7^k$ tables. With unit activities and factorial weights on this **structurally constrained** fiber, each local normalizer is $1+6/4=5/2$, so $Z=(5/2)^k$.

| Complex blocks | Exact table count | Factor DP states | Factor DP transitions | Whole-table DP with the same allowances |
|---:|---:|---:|---:|---|
| 1 | 7 | 9 | 14 | Completes |
| 2 | 49 | 18 | 28 | Budget reached |
| 10 | 282,475,249 | 90 | 140 | Budget reached |
| 50 | $7^{50}$, about $1.80\times10^{42}$ | 450 | 700 | Budget reached |

This demonstrates reduced DP work on this decomposable graph family. It is not a measured wall-clock speedup or a statement that the whole-table DP cannot finish with a larger allowance. Input scan and feasibility work are additional costs.

A hybrid example combines a single cycle of width parameter $2^{200}+17$ with one complex block. It counts $7(2^{200}+18)$ tables using **9 DP states and 14 DP transitions**, plus width-independent cycle arithmetic. The weighted factorial version is intentionally rejected by its cell-magnitude preflight.

```sh
PYTHONPATH=src python3 -S examples/block_factorization.py
PYTHONPATH=src python3 -m unittest discover -s tests -p test_block_sampler.py -v
```

[`block-factorization.json`](../reports/block-factorization.json) contains exact counts, normalizers, work counters, explicit whole-table DP failures, rank/table hashes, and source hashes. The small cases independently compare every table and every weighted probability with whole-table DP. All controls and graph patterns are synthetic; the benchmark is not a calibrated commuting model. Its constrained conditional-Poisson law is distinct from an ordinary unconstrained worker-assignment urn.

Tests compare all **512** $3\times3$ support partitions with an independent oracle that joins edges lying on simple cycles. They exhaust all binary $2\times3$ supports and attainable margins, exercise articulation rows and columns, bridges, fixed positive chords, disconnected/empty fibers, nonzero lower bounds, and both product laws. A complete random-choice tree reproduces all 49 probabilities for two complex factors. Separate tests exhaust shared versus per-block budgets and verify that failure occurs before any RNG access.

## Application scope

The method can exploit actual fixed cells and sparse separation in a specified destination-by-mode or other contingency table. Dense support may form one large block, giving little improvement. Do not invent zeros, treat missing routes as prohibited, or fix uncertain counts to force a decomposition. The method preserves the chosen target exactly; it supplies no evidence that the target describes real travel behavior.

This implementation and proof note were produced with AI assistance and executable exact checks. No Lean certification or new mathematical priority is claimed.
