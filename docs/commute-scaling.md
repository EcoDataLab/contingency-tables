# Certified commute bounds beyond the reference counting budget

The synthetic benchmark certifies both linear VMT endpoints for a
**300-destination, five-mode table with 41,328 workers**. Its constraints admit
at least **3.468 × 10^236** distinct tables by an independently checked
construction. Both attaining witnesses and their dual certificates are saved
in [the complete report](../reports/commute-scaling.json).

The sharp endpoints for that case are **232,823,135.6 and 398,881,403.8 annual
household-attributed commute vehicle-miles**. These are conditional possibilities
under synthetic controls, not empirical estimates or a confidence interval.

The 750-destination case reaches the optimizer's explicit 25-million-arc work
budget and returns **no bounds**. Every tested reference counting DP also
reaches an explicit state or transition limit. The benchmark records those
limits as unsuccessful computations, without substituting a partial answer.

## Reproduce the benchmark

```sh
PYTHONPATH=src python3 experiments/commute_scaling.py
```

Default destination counts are `4, 12, 30, 75, 150, 300, 750`. Each case runs in
a separate worker with a 30-second wall-time watchdog. The optimizer has a
shared 25,000,000-residual-arc budget for the two endpoints. The reference DP
has at most 2,000 states and 10,000 row transitions. All limits can be changed
explicitly with `--destinations`, `--max-work`, `--max-states`,
`--max-transitions`, and `--case-timeout`; `--output` chooses the report path.

The JSON includes complete problem constraints, rational coefficient strings,
a feasible anchor, a constructive lower bound on fiber size, attaining endpoint
tables, dual potentials, independent verification results, deterministic work
counts, machine metadata, and local wall times. Source hashes identify the
generator, optimizer, and reference sampler. Each instance also has an input
hash. No private data or CBEI production files are used.

## Synthetic controls and scope

Destination prefixes are generated deterministically with seed `1152026`.
Each destination has 25–250 synthetic workers. Stipulated mode weights are
converted into a feasible integer anchor by largest-remainder allocation; its
column sums become the exact mode controls. These weights create the test
instance and are not a fitted probability law used by the optimizer.

One-way distances range from 0.50 to 50.00 miles in exact hundredths; the first
destination is one mile away. Walking is forbidden beyond three miles.
Transit is forbidden beyond 35 miles and for every fifth destination. These
are deliberately synthetic support restrictions, not recommendations for a
real commuting model. Every seventh destination receives positive cell lower
bounds where its anchor permits them; every third destination receives tighter
upper caps. All restrictions are built around the anchor, so feasibility is
known before optimization and then checked independently.

The modes are drive alone, two-person carpool, transit, walk, and work from
home. The objective uses two commute legs per workday, 220 workdays, and
vehicle-attribution factors `(1, 1/2, 0, 0, 0)`. Work-from-home entries retain a
workplace association. Zero household-auto VMT for transit does not mean zero
transit emissions. All quantities and restrictions are uncalibrated.

The linear coefficients use exact fractions. The feasible set contains integer
counts; there is no rounding of optimization results. No sampling law is needed
to certify its smallest and largest possible objective.

## Recorded results

The following times are from one local run of CPython 3.14.3 on Darwin 24.6.0,
arm64, with 10 logical CPUs reported by the operating system. The solver is
serial. Timings include its independent certificate checks and exclude process
startup and subsequent JSON report serialization. They are measurements on
this machine, not machine-independent speed estimates.

| Destinations | Workers | Explicit fiber-size lower bound, approximately | Residual arc examinations | Optimizer wall seconds | Result |
| ---: | ---: | ---: | ---: | ---: | --- |
| 4 | 495 | 729 | 5,885 | 0.00143 | Both endpoints certified |
| 12 | 1,677 | 7.881 × 10^8 | 42,578 | 0.00674 | Both endpoints certified |
| 30 | 4,357 | 5.846 × 10^22 | 231,668 | 0.03111 | Both endpoints certified |
| 75 | 9,903 | 1.021 × 10^56 | 1,231,105 | 0.15142 | Both endpoints certified |
| 150 | 20,403 | 4.366 × 10^115 | 5,242,458 | 0.62575 | Both endpoints certified |
| 300 | 41,328 | 3.468 × 10^236 | 19,360,240 | 2.36961 | Both endpoints certified |
| 750 | 103,063 | 3.174 × 10^593 | 25,000,000 | 2.92015 | Work budget exhausted; no endpoints returned |

The exact integer lower bounds, rather than their rounded displays above,
appear in the JSON. All six completed optimizer cases pass independent
verification after their witnesses and certificates are serialized and read
back.

The reference DP uses destination rows and five mode columns. For 300
destinations it stops after 2,000 states and 9,554 transitions. Every other
listed case stops at 10,000 transitions. Each run reports `complete: false` and
provides no count or sample. These are outcomes under the **chosen reference
implementation and limits**. They do not prove that a different DP, a larger
budget, an approximate counter, or a theorem-backed sampler would fail. Flow
optimization and counting answer different questions; their runtimes should
not be presented as interchangeable-method speed comparisons.

## Checking that the fiber really is large

Take two consecutive rows `i,k` and the drive and work-from-home columns `a,b`.
Starting from the feasible anchor, apply the cycle

\[
(X_{ia},X_{ib},X_{ka},X_{kb})
\longmapsto
(X_{ia}+t,X_{ib}-t,X_{ka}-t,X_{kb}+t).
\]

This preserves every row and column sum. Intersect the four cell-bound
intervals to obtain a nonempty integer interval `[L,U]` for `t`. It contains
zero because the anchor is feasible. Now choose **disjoint row pairs**. Their
cycles affect disjoint cells, and each cycle preserves the column totals by
itself. All choices of their parameters are therefore feasible simultaneously.
Different parameter vectors give different full tables, so

\[
|\Omega|\ge\prod_{\text{row pairs}}(U-L+1).
\]

`verify_switch_family` checks the anchor, disjointness, parameter intervals,
cell bounds at both endpoints, and the exact product, without counting the
full fiber. Every integer between each interval's endpoints also satisfies the
linear cell bounds. Tests independently construct this family in a tiny
example: its nine distinct feasible tables form a proper subset of the full
19-table fiber. The reported construction is explicitly a **lower bound**, not
an exact count or a statement about probability mass.

## Profile-guided exact arithmetic change

The original optimizer repeatedly performed `Fraction` arithmetic during
shortest-path search. Profiling the 30-destination case before editing it
showed 1,471,424 function calls, with fraction addition and comparison among
the main costs. The original source matches commit `25b857b` and SHA256
`4ee72acb00cb83d0b45867cfd13130121dea3fb56099d4c13903bf5c4d31f9c9`.

The solver now clears the rational costs' common denominator once per solve,
uses Python integer costs and distances internally, then divides its final
potentials back exactly. Multiplication by one positive constant preserves all
path comparisons and ties. The public API, objective, work accounting,
certificate conditions, and flow algorithm are unchanged. This is an exact
arithmetic implementation improvement; it introduces no approximation and no
new asymptotic guarantee.

For the same profiled instance, the updated solver made 290,359 function calls
and examined the same 231,668 residual arcs. The captured profiled times were
0.357 seconds before and 0.070 seconds after; profiling itself adds overhead.
The five uninstrumented baseline cases, through 150 destinations, have
**identical witnesses, rational potentials, objective values, augmentation
counts, and arc counts** after the change. The report retains both profiles
and those exact comparisons. Their wall times came from single runs at
different instants; the deterministic equality checks carry more weight than
an asserted stable speed ratio.

To profile the current implementation separately:

```sh
PYTHONPATH=src python3 experiments/commute_scaling.py --profile-only 30 --output /tmp/commute-profile.json
```

The stored before-change snapshots can optionally be supplied through
`--baseline-profile` and `--baseline-report` when reproducing the comparison;
they are historical measurements, not recomputed by a normal benchmark run.
Current-only reproduction still regenerates the instances, verifies results,
and records current timings and source hashes.

## What this contributes

For a chosen linear commuting metric, sharp possible endpoints can be useful
well before an allocation distribution can be counted or sampled by the small
reference DP. They expose the consequences of incomplete association data
under explicit controls and give independently checkable extrema for testing
future samplers or weighted models.

These synthetic results establish computational behavior for the recorded
instances. They do not establish accurate source reconciliation, travel
behavior, inference, or uncertainty coverage. They do not change the
distinction between jobs and workers or between commute VMT and total
household VMT. The solver still uses a basic successive-shortest-path method
with a total-flow-dependent general augmentation bound; large binary inputs
can exceed its budget. See [the certificate and complexity note](linear-bounds.md).
