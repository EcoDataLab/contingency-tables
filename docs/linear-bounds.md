# Exact, certified bounds for linear table observables

`contingency115.optimize` computes the smallest and largest value of

$$
F(X)=\sum_{ij}c_{ij}X_{ij}
$$

over the **entire specified bounded integer-table fiber**, without enumerating
that fiber or choosing a probability law. Each endpoint comes with an attaining
integer table and exact rational dual potentials. A separate verifier checks
the certificate without running any optimization or sampling algorithm.

This is an applied addition to the #115 research tooling. Capacitated
min-cost flow is an established optimization problem; see the primary
[OR-Tools documentation](https://developers.google.com/optimization/flow/mincostflow)
for its standard formulation. This module uses its own small standard-library
implementation and does not depend on OR-Tools. It is not a new optimization
theorem, a sampler, or an implementation of #115's polynomial-time algorithms.

## Usage

```python
from fractions import Fraction
from contingency115.tables import TableProblem
from contingency115.optimize import linear_bounds, verify_optimality

problem = TableProblem(
    row_sums=[3, 2],
    column_sums=[2, 3],
    lower_bounds=[[1, 0], [0, 0]],
)
costs = [[1, Fraction(1, 2)], [4, 0]]
bounds = linear_bounds(problem, costs, max_work=100_000)
assert bounds.minimum.value == Fraction(5, 2)
assert bounds.maximum.value == Fraction(6)
assert verify_optimality(problem, costs, bounds.minimum.table,
                         bounds.minimum.certificate)
```

For only one endpoint, use `optimize_linear(problem, costs, maximize=False)`;
set `maximize=True` for a maximum. Costs accept integers and `Fraction`,
including negative values. Floats, strings, and booleans are rejected rather
than silently treated as exact scientific inputs. Parse a deliberate rational
input such as `"1/2"` with `Fraction` before calling the optimizer.

`linear_bounds` returns `minimum` and `maximum`, each with `value`, `table`,
`certificate`, `augmentations`, and `work_used`. The two endpoints share one
`max_work` budget; if either solve fails, no partial bounds object is returned.

Generate the reproducible commuting report from the repository root:

```sh
PYTHONPATH=src python3 examples/linear_metric_bounds.py
```

This writes [reports/linear-bounds.json](../reports/linear-bounds.json), including
the input SHA256, effective constraints, exact metric coefficients, both integer
witnesses, potentials, reduced coefficients, signed primal and dual values,
and verification outcomes. Rational quantities use strings. JSON integer
quantities should be parsed with arbitrary precision if adapting the example
to very large counts. `--input`, `--output`, and `--max-work` override defaults.
An incompatible input produces a report containing its cut or elementary
contradictions. A budget failure produces no endpoints and exits with status 2.

## Why the certificate proves optimality

The verifier first checks the witness is an integer table with exactly the
requested margins and inclusive cell bounds. Let `s=1` for minimization and
`s=-1` for maximization. The certificate supplies row potentials `p_i`, column
potentials `q_j`, and the claimed endpoint. Define reduced coefficients

$$
a_{ij}=s c_{ij}+p_i-q_j.
$$

For **any** feasible table `Y` with row sums `r` and column sums `b`,

$$
sF(Y)=\sum_jq_jb_j-\sum_ip_ir_i+\sum_{ij}a_{ij}Y_{ij}
\ge
\underbrace{\sum_jq_jb_j-\sum_ip_ir_i+
\sum_{ij}\min(a_{ij}\ell_{ij},a_{ij}u_{ij})}_{D}.
$$

Every term uses only supplied constraints, costs, and certificate values. For
the witness `X`, the verifier checks the complementary conditions

$$
X_{ij}<u_{ij}\implies a_{ij}\ge0,
\qquad
X_{ij}>\ell_{ij}\implies a_{ij}\le0,
$$

then checks **exactly** that `F(X)` is the claimed endpoint and `s F(X)=D`.
Thus the witness attains a bound applying to every feasible table. Fixed cells
with `lower=upper` require no reduced-coefficient sign condition. All arithmetic
uses integers or fractions; there is no numerical tolerance.

The same bound also holds over real-valued feasible tables. Finding an integer
witness that attains it establishes the integer endpoint directly; the checker
does not need to trust a separate integrality theorem or the solver's history.
Verification takes `O(m n)` arithmetic operations. Operand bit lengths still
affect the cost of those operations.

## Solver and computational limits

Subtract each lower bound from its cell and from the corresponding margins.
Build a flow network with source-to-row residual supplies, bounded row-to-column
cell arcs, and column-to-sink residual demands. For a maximum, negate the costs.
Multiply rational costs by their positive common denominator, so path arithmetic
uses exact Python integers. Starting with zero residual flow, repeatedly find
a shortest augmenting path with exact Bellman–Ford relaxation and send the
path's whole bottleneck amount. Divide final potentials by that denominator
before certification. Scaling preserves all path comparisons and ties; it
changes neither feasible tables nor the optimum of the original objective.
The initial residual graph has no directed cycles. Shortest-path augmentation
preserves the absence of negative residual cycles. At full flow, a final
Bellman–Ford pass from an implicit zero-cost supersource produces potentials
for all components. The independent certificate check must pass before any
endpoint is returned.

The implementation stores capacities as Python integers and does not expand
them into workers or unit arcs. The regression test with margins `2**200` uses
two augmentations per endpoint, just like the same example with margins one.
**This example is not a polynomial-in-bit-length guarantee.** The implementation
uses a basic successive-shortest-path method; its simple general augmentation
bound is the total lower-shifted flow `R`. That can be exponential in the number
of bits used to write `R`. With `V` vertices and `E` directed residual arcs, a
conservative arithmetic-operation bound is `O((R+1) V E + m n)`, while integer
and rational bit complexity adds further cost. No strong-polynomial or
large-scale-performance claim is made.

`max_work` counts every residual arc examination in shortest-path relaxation,
tight-path recovery, and final potential construction. Reaching it raises
`ComputationBudgetExceeded`, including when it prevents final certification.
It does **not** limit input size, setup or verification work, memory, operand
bit lengths, or wall-clock time. Do not use it as a service-level deadline or
as a security boundary for untrusted large inputs.

## Diagnosing an empty fiber

`InfeasibleTableError` reports elementary contradictions: unequal total margins,
a lower bound exceeding its effective cap, or lower bounds exceeding a margin.
When support or caps obstruct otherwise valid lower-shifted controls, its
`InfeasibleFlowError` subclass carries a `FlowCutCertificate`. The certificate
names source-side row indices `A` and column indices `B`; its capacity is

$$
\operatorname{cap}(A,B)
=\sum_{i\notin A}r'_i
+\sum_{i\in A,\,j\notin B}(u_{ij}-\ell_{ij})
+\sum_{j\in B}b'_j,
$$

where primes denote lower-shifted margins. If this is strictly less than total
required residual flow, no feasible table exists. `verify_infeasibility` checks
the inequality and the claimed capacity directly from the problem, without a
flow solver. Index sets describe the obstruction; they do not prescribe which
observations or modeling restrictions should be changed.

## What the commuting example establishes

The fully synthetic [commuting fixture](../examples/synthetic_commute.json)
has 42 feasible tables. Applying its stated linear VMT formula gives exact
endpoints of **9,460 and 25,080 vehicle-miles per year**, with certified
attaining tables. Independent Cartesian enumeration agrees. Neither a uniform
table law nor a conditional-Poisson law is required for these bounds.

These are sharp possibilities under the specified cohort, distances, annual
attendance, vehicle-attribution factors, margins, and cell restrictions. They
are not a confidence interval, an uncertainty distribution, or a claim that
every value between the endpoints is attainable. Any probability law supported
on the full fiber has outcomes and a mean within these bounds; a law assigning
zero probability to some tables can have a narrower supported range.

This gives commuting research a useful first diagnostic: determine how much an
unknown destination–mode association can change a **linear** metric before
choosing behavioral weights or paying for samples. Independent origins with
fixed additive coefficients can be solved separately and their endpoints
summed; that statement requires the absence of cross-origin constraints.

The optimizer cannot reconcile workers with jobs, repair incompatible source
universes, infer actual commuting behavior, or justify treating commute VMT as
all household VMT. Costs depending on allocation, overlapping tensor margins,
congestion, and nonlinear metrics require additional modeling. The synthetic
result is a synthetic commuting benchmark, without production data or empirical calibration.

## Validation

`tests/test_optimize.py` compares against Cartesian cell enumeration for all
81 two-by-two cap patterns with caps in `{0,1,2}` and 180 seeded rectangular
cases with lower bounds and signed rational costs. It also checks both
commuting endpoints, fixed and zero-total fibers, transposition and row/column
cost shifts, a 201-bit margin, budget exhaustion, malformed inputs,
infeasibility cuts, and rejected certificate tampering. Certificate tests
disable the optimizer and flow helpers while verifying valid certificates.
Report tests reconstruct the full problem, costs, witnesses, and certificates
from a JSON round trip before independent verification.

```sh
PYTHONPATH=src python3 -m unittest discover -s tests -p test_optimize.py -v
```
