# Exact experiments with the ideal #115 physical chain

**Status, 8 October 2026:** the bounded exact backend is implemented in [`ideal_chain.py`](../src/contingency115/ideal_chain.py), with thirteen passing tests in [`test_ideal_chain.py`](../tests/test_ideal_chain.py). The literal all-small fixtures, a literal mixed fixture with unique completions, and a separately labelled rescaled acceptance fixture pass exact state, graph, translation, stationary-law, output-bijection, and budget checks. The existing cycle heat baths remain distinct kernels. This backend is an exponential tiny-instance oracle, not the full finite-bit sampler or a practical general sampler.

The source is OpenAI's unchanged revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The aim is to reproduce its finite ideal transition law on instances small enough to inspect exhaustively. An exact completion-counting oracle would replace the source's dense completion implementation. This would not implement its finite-bit programs, prescribed mixing schedule, correction machinery, or general polynomial-time algorithm.

## Supported target and parameters

The first backend should accept an ordinary `TableProblem` with nonnegative integer margins, no effective cell caps, no nonzero lower bounds, and no external product weights. Its final successful output law is uniform over integer tables with those margins. Structural zeros, nontrivial caps, and the conditional-Poisson worker law must stay in separate benchmark panels.

For an `m × n` input, retain the literal source parameters:

\[
d=10+(m+1)(n+1),\qquad U=d^{20},\qquad L=d^{12},\qquad
\beta=2^{-\lceil\log_2(32d^2)\rceil}.
\]

A cell is small when `r[i] < U` or `c[j] < U`. The large cells form the complete rectangle of rows with margin at least `U` and columns with margin at least `U`. Small-coordinate capacity is `U`; large-coordinate capacity is `N+dL+U+2`, where `N=sum(r)`. That large capacity dominates every supported residual total and does not impose an additional effective cell cap.

These formulas are in [`CompletionCounts.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Transport/CompletionCounts.lean) (`paperCapacity`, `firstPaperSmall`, `dimensionAllowance`) and [`FirstPaperSmallKernel.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/FirstPaperSmallKernel.lean) (`smallProposalRat`).

For the first fixture, `r=c=(2,2)`, every cell is small under the actual parameters. Here `d=19` and `beta=1/16384`. Large powers do not require enumerating `0..U`: margin and defect constraints bound the feasible retained entries. No rescaling is needed for this fixture. If a later experiment substitutes smaller `U,L`, its metadata and label must explicitly say that it is a rescaled model, with none of the source's quantitative guarantees carried over.

## Physical state, feasibility, and weight

Represent a state by two tuples `X,Q`, in a fixed row-major ordering of the small cells. They are the actual row and column views. The source's doubled bounded profile is exactly `(X, U-Q)`, so this representation is bijective and preserves the complement coordinate used in its graph.

Permitted patterns are:

- Balanced: `Q=X`.
- A single defect with distinct small cells `s,t`: `Q=X-e_t+e_s`. The source calls `s` negative and `t` positive; `X[t]` must be positive.

Set the views to zero outside the small cells. Let `a[i]` be the sum of `X` over small cells in row `i`, and `b[j]` the sum of `Q` over small cells in column `j`. Require `a[i] <= r[i]`, `b[j] <= c[j]`, and coordinates in `0..U`. The padded residual margins are

\[
R_i=r_i-a_i+\#\{\text{large cells in row }i\}L,\qquad
C_j=c_j-b_j+\#\{\text{large cells in column }j\}L.
\]

Require zero residual outside the large rows/columns and equal residual totals. These are exactly the arithmetic `ProfileFeasible` tests. The completion fibre consists of ordinary nonnegative integer tables with margins `R,C` on the large rectangle. The state weight is the **number of completions**, including multiplicity. If one side of that rectangle is empty, feasibility forces all residuals to zero and the unique empty completion has weight one.

See [`FirstPaperFeasibility.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/FirstPaperFeasibility.lean), [`SmallGraphProfiles.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/SmallGraphProfiles.lean), and [`PhysicalResidualMargins.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/PhysicalResidualMargins.lean).

An exhaustive but finite state enumerator can range each `X[i,j]` only up to `min(U,r[i],c[j]+1)`, enumerate the balanced `Q` and each ordered single-defect modification, then apply all feasibility tests. This bound is complete: column feasibility gives `Q[i,j] <= c[j]`, and a permitted defect changes a cell by at most one. Count every candidate against a work budget; do not expose a partial state list after exhaustion. A row-composition enumerator can prune further without changing this argument.

## Adjacency and literal proposal law

The graph is the union of:

1. Unit exchanges in the doubled coordinates `(X,U-Q)`: add one at a coordinate, remove one at a different positive coordinate, and retain the candidate only if it is a feasible physical state.
2. The designated repair of each feasible defective state, and its reverse edge. For defect labels `s,t`, form `repairMatrix(X,s,t)=X-e_t+e_(t.row,s.column)` on the full matrix. Restrict that matrix to the small cells and set **both** new views equal to it. A crossing cell can be large; then its added unit is represented through the changed residual completion, not a retained small coordinate.

Edges are deduplicated. They are not sampled uniformly among the current state's neighbors. Every feasible neighbor receives the same input-dependent probability `beta`; all unused proposal mass holds. This distinction matters because the number of neighbors varies by state. Assert the source degree allowance and that total proposal mass is at most one half.

The exact arithmetic identification is in [`FirstPaperLocalNeighbors.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/FirstPaperLocalNeighbors.lean) (`ArithmeticEdge`, `arithmeticEdge_iff`). The repair sign and crossing cell are fixed by [`Repair.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/Repair.lean). The graph and the proposal are connected in [`FirstPaperProposal.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/FirstPaperProposal.lean).

## Uniform completion and acceptance

When the large rectangle is nonempty, choose one reference large row `i0` and column `j0`, fixed for the input. For a proposed move `x -> y`, let `DeltaR=R(y)-R(x)` and `DeltaC=C(y)-C(x)`. The integer translation is

- `D[i,j]=0` away from the reference row and column;
- `D[i,j0]=DeltaR[i]` for `i != i0`;
- `D[i0,j]=DeltaC[j]` for `j != j0`;
- `D[i0,j0]=DeltaR[i0]-sum(DeltaC[j] for j != j0)`.

Draw a completion uniformly from the current fibre and accept precisely when every entry of `A+D` is nonnegative. Discard that completion after the test. With `W(x)` completions and `A(x,y)` passing this test, the off-diagonal transition probability is `beta*A(x,y)/W(x)`. The diagonal receives all holds and rejected proposals. Translation gives an exact bijection between accepted forward and backward completions, so `A(x,y)=A(y,x)` and stationary state mass is proportional to `W(x)`.

This is the source's [`SignedMarginTranslation.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Transport/SignedMarginTranslation.lean), [`CompletionProposalLaw.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Transport/CompletionProposalLaw.lean), and [`FirstPaperIdealKernel.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/FirstPaperIdealKernel.lean).

When every cell is small, do not invent a reference row. Use the source's [`AllSmallChain.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/AllSmallChain.lean): every valid neighbor proposal is accepted, and every physical state has weight one.

## Successful output and a fair comparison

A final output uses a **fresh** uniform completion conditional on the current state. It succeeds only if `X=Q` and every large completion entry is at least `L`. Join the small view and the completion, then subtract `L` from every large cell. Successful state/completion pairs are in bijection with original tables. At the exact stationary joint law, conditioning on success therefore gives the uniform table law. A short trajectory from a fixed starting state does not acquire this guarantee merely by using an exact transition kernel.

These statements are separated in [`FirstPaperJointLaw.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/FirstPaperJointLaw.lean) and [`FirstPaperSuccessEvent.lean`](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/OAI/Combinatorics/ContingencyTables/Sampling/FirstPaperSuccessEvent.lean).

For tiny all-small instances only, a second diagnostic can compute the exact chain observed on successive visits to balanced states. Write `A` for balanced states and `B` for defects. Its transition matrix is

\[
P_{AA}+P_{AB}(I-P_{BB})^{-1}P_{BA}.
\]

Each balanced state maps to one original table, so the result can use the existing `ExactKernel` table interface and has a uniform target. Solve the displayed system using rational elimination with a separate matrix-size/work budget; reject a singular or disconnected case rather than assuming return is certain. At stationarity, expected physical steps per return is `1/pi(A)`. The benchmark should also retain per-start return times if computed.

This censored kernel is an algebraic diagnostic. Drawing directly from it bypasses physical excursions, so its draw time must **not** be advertised as the runtime of the literal #115 chain. The benchmark can compare exact laws and asymptotic variance, separately report `pi(A)` and expected physical steps, and later measure actual excursions under a hard physical-step budget. This interface was agreed with the cycle-mixture benchmark agent before the pause.

## Implemented API

Keep the experimental implementation in `src/contingency115/ideal_chain.py`, without changing existing sampler laws.

```text
IdealChainBudget:
  cell count, input bit length, profile candidates, physical states,
  total enumerated completions, aggregate DP work, transition work,
  rational elimination size/work

PhysicalState:
  row_view: tuple[int, ...]
  column_view: tuple[int, ...]

build_ideal_chain(problem, *, budget=...) -> IdealPhysicalChain
  d / U / L / beta / upstream_revision / parameter_regime
  small_cells / large_rows / large_columns / fixed reference indices
  states / completions / completion_counts / neighbors / acceptance_counts
  exact Fraction transition matrix / stationary probabilities
  step(state_index, rng) -> state_index
  output(state_index, rng) -> Table | None
  stationary_output_law() -> exact table masses and failure mass
  all_small_return_kernel(...) -> CensoredTableKernel
  physical_return(state_index, *, max_steps, rng) -> PhysicalReturn

CensoredTableKernel:
  kernel: ExactKernel on original tables
  stationary_success_probability: Fraction
  expected_physical_steps_per_return: Fraction
  per_start_expected_physical_steps: tuple[Fraction, ...]
  construction/provenance explicitly identifying algebraic censoring
```

`build_ideal_chain(problem, budget=...)` always uses the literal `U=d^20,L=d^12`. `build_rescaled_ideal_chain(problem, U=..., L=..., budget=...)` has an explicit `parameter_regime` declaring its departure and absence of source quantitative guarantees. Both reject effective cell caps and nonzero lower bounds; neither accepts product weights. Ordinary zero margins remain supported. Identical residual fibres are cached. One-row/one-column completions are constructed directly without iterating up to a huge margin; other completions use the existing bounded `ExactTableSampler`.

`IdealChainBudget` limits cells, margin and parameter input bits, enumerator visits/profile candidates, physical states, uniquely cached completion tables, aggregate completion DP states and transitions, dense-matrix/neighbor/acceptance work, first-hit solve size/work, and stored rational bit lengths. The solver checks that every state can reach the balanced set, then solves the exact rational system, failing explicitly if singular. These are structural work caps, not wall-clock deadlines. `step` and `output` assume the supplied `randrange(stop)` is uniform; they do not implement or bound a finite-bit RNG. `physical_return` adds a hard number-of-physical-steps cap and counts holding transitions. Exhaustion raises before returning a partial law, fibre, or return.

## Exact fixture results

The table below records exact construction results, not mixing-time or runtime measurements. Every reported physical kernel is connected, stochastic, and satisfies detailed balance exactly. `W` is the number of completions of a physical state. Successful pairs have one preimage per original table; their conditional stationary law is uniform.

| Fixture | Regime | Physical states | Undirected edges | Original tables | State weights W | Stationary output success |
| --- | --- | ---: | ---: | ---: | --- | --- |
| 2×2, r=c=(1,1) | Literal, d=19 | 14 | 28 | 2 | 1 | 1/7 |
| 2×2, r=c=(2,2) | Literal, d=19 | 27 | 56 | 3 | 1 | 1/9 |
| 2×2, r=c=(19²⁰,1) | Literal, unique 1×1 large completions | 9 | 14 | 2 | 1 | 2/9 |
| 3×3, r=c=(4,4,1) | **Rescaled**, U=4,L=1; no paper quantitative guarantees | 49 | 150 | 21 | 5,6,7 | 7/97 |

The two literal all-small return matrices, in lexicographic table order, are

\[
P_{(1,1)}=\begin{pmatrix}7679/7680&1/7680\\1/7680&7679/7680\end{pmatrix},
\qquad
P_{(2,2)}=\begin{pmatrix}
7679/7680&1/7680&0\\
1/7680&3839/3840&1/7680\\
0&1/7680&7679/7680
\end{pmatrix}.
\]

Their proposal probability is still `beta=1/16384`. Expected physical steps to the next balanced visit are `(7,7)` and `(7,13,7)` respectively. The stationary averages are `7` and `9`, agreeing with `1/pi(A)`. Most returns are single holding steps; rare excursions account for the larger expectation. These exact first-return calculations do not claim that a short physical trajectory has reached stationarity. Direct draws from these matrices are algebraic diagnostics and bypass the physical excursions.

The literal mixed fixture has small cells `(0,1),(1,0),(1,1)` and reference large cell `(0,0)`. Its original tables are `((U−1,1),(1,0))` and `((U,0),(0,1))`. The designated repair can add at the large crossing cell, represented through its residual completion. Only 52 enumerator/profile visits and three distinct residual completions are needed; huge margins are represented as integers, not expanded ranges.

The rescaled fixture is used only to exercise genuine completion multiplicities and reference-translation rejection. Among its 300 directed edges, 82 have acceptance below one. Each accepted forward completion translates bijectively to an accepted backward completion. This law differs from simply using the Metropolis ratio of completion counts; the test checks that distinction. Its successful pair count is 21 out of stationary total completion multiplicity 291, giving success `21/291=7/97` and unconditional table mass `1/291`.

Critical definitions were cross-checked directly against the pinned source: `CompletionCounts.lean` for `firstPaperSmall`, `paperCapacity`, and `dimensionAllowance`; `FirstPaperFeasibility.lean` for arithmetic feasibility; `Repair.lean` for the signed defect and crossing repair; `FirstPaperLocalNeighbors.lean` for exchanges and both repair orientations; `PhysicalSmallGraph.lean` and `SmallProposal.lean` for degree `5d²+1` and the half-hold allowance; `FirstPaperSmallKernel.lean` for dyadic beta; `SignedMarginTranslation.lean` for target-minus-source star translation; and `AllSmallChain.lean` for the unit-weight branch. The empty completion convention is the unique zero matrix on an empty large rectangle.

Validation command: `PYTHONPATH=src python -m unittest discover -s tests -p test_ideal_chain.py -v`. Thirteen tests pass. They independently enumerate both physical views for the all-small fibres, compare every pair against doubled exchanges or repair edges, verify mixed residual margins, enumerate accepted translations and their inverse, expand the finite proposal/completion RNG decision tree with identical unused hold slots grouped, and compare the return matrix with an independently solved embedded-jump first-hit equation. Each named budget is exercised. No theorem-length trajectory or Lean process is launched by this module or these tests.

The design uses the standard-library exact reference tools already in this repository. Every exhausted budget must fail explicitly before returning an incomplete kernel or catalogue. The algorithms are exponential finite oracles, not production-scale alternatives for LEHD.

## Validation scope and next experiments

The implementation and tests are in the assigned source and test paths. The following checks define the audit scope and are covered by the thirteen tests above. Independent source review and benchmark integration remain separate steps.

- Independently enumerate small row/column views and compare the complete state set, including complementary-coordinate encoding and the unique empty completion.
- Check every state against the source feasibility equations and distinguish balanced from single-defect patterns.
- Check graph symmetry, no duplicate edges, the unit-exchange criterion, and repairs whose crossing cell is small or large.
- Exhaustively count accepted translations in both directions, verify row/column changes, and check the reverse bijection.
- Verify exact row sums, nonnegative probabilities, detailed balance with completion multiplicities, and connectivity for each reported instance.
- Expand the finite RNG decision tree on tiny examples to compare `step` with the exact matrix, including hold and rejected proposals.
- Compare successful output pairs with an independent enumeration of original tables: exactly one preimage per table, no missing or extra table, exact conditional uniformity.
- Verify the censored kernel independently by solving first-hit equations; verify uniformity, row sums, and the stationary return-time identity. Keep algebraic sampling timings distinct from actual excursion timings.
- Exercise each budget before any partial result escapes, and reject sparse/capped/product-law inputs rather than silently altering the target.

Physical trajectories and comparative benchmark timing should record construction/solve cost, physical steps including holds, balanced returns, and direct algebraic draws separately. No generic practical-speed claim follows from these exact finite fixtures.
