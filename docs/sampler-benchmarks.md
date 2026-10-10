# Bounded same-law sampling comparison

This reproducible synthetic panel compares reference methods **under the same
margins, bounds, activities, and target law within each case**. It measures
local preparation and finite trajectories and supplies exact stationary
observable diagnostics when the fiber is small enough. It does not implement
the full finite-bit #115 sampler or its theorem-length schedule. The literal
ideal physical chain is included only on two tiny ordinary-table instances.
Independent source review, targeted checks, and the integrated Python suite cover the implementation; the [checkpoint receipt](../reports/checkpoint-verification.json) records their scope.

## Panels and competitors

- Ordinary uniform tables: few-mode, dense, zero/small-margin, unequal-margin,
  and increasing-square-dimension fixtures, with exact independent DP draws and
  equal-selection rectangle full-line heat baths.
- Bounded/structural-zero uniform tables: a six-cycle negative control and the
  synthetic commute fixture, with rectangle and all-simple-cycle heat baths.
  Rectangles deliberately hold forever on the six-cycle fixture.
- Bounded activity-weighted conditional-Poisson tables: the same commute input
  with its nonseparable activity and inverse-factorial weights. Exact weighted
  DP and weighted heat baths share this law.
- Ordinary inverse-factorial tables: three small cases compare exact weighted
  DP, the existing independent worker-urn sampler, and rectangle heat baths.
  This is the classical individual-assignment conditional independence law.
  The urn method is not a uniform-table competitor, and the benchmark does not
  execute Patefield's algorithm or SciPy/R implementations.
- Literal ideal chain: ordinary uniform 2x2 margins `(1,1)` and `(2,2)` compare
  DP, rectangle heat baths, algebraic censored-return draws, and physical
  balanced-state return excursions. The backend is described in
  [the ideal-chain note](ideal-chain-experiment.md).

For the two commute laws, supplied pre-tuned rectangle and all-simple-cycle
mixtures also run. Their probabilities come from the saved
[finite gap-certificate report](../reports/cycle-mixtures.json). Preparation
loads the report, checks the fixture and sampler-source hashes, verifies the
complete input/law, matches cycle signs, and checks rational probabilities.
It does not replay the spectral certificates or rerun the original full-fiber
numerical optimization. That original tuning cost is **unmeasured and excluded**;
these methods compare the cost of executing a supplied mixture, not its full
end-to-end discovery cost. A better certified gap is not a measured speedup.

Every cycle catalog and its selection probabilities are input-fixed. A
transition draws exactly from the complete feasible integer line. Uniform
lines use an integer rank without enumerating their width; weighted lines
normalize rational masses. The reference implementation validates tables and
cycles on each transition. Self-transitions and degenerate lines are counted;
cycle heat baths have no Metropolis rejection stage.

## Starts, timing, and RNG

Each MCMC method uses up to three distinct oracle-selected tables at low,
intermediate, and high values of the reported linear observable. Each start
runs with warmup zero and warmup 200, under two fixed seeds in the saved panel.
These are diagnostic cold starts, not a practical initialization algorithm.
Seed repetitions are separate from the number of available starts; singleton
fibers still repeat every seed. DP and worker urn need neither a table start
nor warmup and repeat the same seed set once each. Run counts therefore differ;
comparisons concern per-run draw counts and costs, not pooled runtime totals.

Fresh preparation, RNG/state initialization, warmup, and retained-output draw
time are recorded separately for each run. The full-fiber oracle, start
selection, exact stationary diagnostics, metrics, histograms, and heuristic ESS
are outside the operational sampling clocks. Total operational time includes
preparation, initialization, warmup, and draws. Output-table allocation and
retention are timed. No thinning is used. A finite warmup does not certify
convergence. Reused numerical seeds do not imply matched random choices across
methods, whose call sequences differ.

The RNG contract requires every `randrange(stop)` to be uniform conditional on
all previous calls. `random.Random` supplies reproducible pseudorandom paths;
these seeds are not a proof of physical randomness. Exact-law statements are
conditional on the ideal integer-RNG contract.

Python memory is measured in a separate `tracemalloc` pass with fresh
preparation, at most 100 retained outputs, and no warmup. It excludes prior
input, oracle, and initial-table allocations and is not process RSS. Its
instrumented wall time is not used for throughput. Timing runs share a local
development machine with uncontrolled background work. They support neither
cross-machine claims nor practical-scale extrapolation.

## Exact stationary diagnostic

The observable is
`sum((row_index-column_index)^2 * cell_count)` with zero-based indices. It is a
generic nonseparable statistic, not physical commute VMT. Enumeration supplies
its exact target mean and variance. For a bounded exact reversible kernel,
[`chain_diagnostics.py`](../src/contingency115/chain_diagnostics.py) solves the
rational Poisson equation in each positive-mass communicating class:

$$
(I-P+\mathbf 1\pi^{\mathsf T})h=f-\mathbb E_\pi f,
\qquad
\sigma^2=2\langle f-\mathbb E_\pi f,h\rangle_\pi
-\operatorname{Var}_\pi(f).
$$

The reported asymptotic variance is the stationary-start limit
`lim(n * Var(sample mean of n outputs))`. This definition handles a periodic
negative-one eigenvalue even when its ordinary covariance series does not
converge. Exact means, variances, component means, between-class mean variance,
and the variance-inflation ratio `sigma^2 / Var_pi(f)` are recorded as rational
strings; the ratio also has a display float.

If component means differ, sample-mean variance has a positive limit and the
asymptotic variance diverges. Its value is null with status
`infinite_between_classes`. If component means agree, the stationary ensemble
can have finite asymptotic variance even though a fixed start cannot explore
the whole target. Reducibility is reported in either case. Zero observable
variance and zero asymptotic variance are distinct statuses; neither produces
a speedup/ESS inference. A small exact variance ratio applies to this
observable at stationarity and is not a general mixing certificate.

Empirical total variation compares the observed table frequencies with the
entire exact target, including unseen tables. It has ordinary finite-sample
noise even for iid methods. Independent methods report their draw count as ESS
only when the target observable has nonzero variance. MCMC ESS is a trajectory
heuristic: biased autocovariances, positive pairs at lags `(1,2)`, `(3,4)`, etc.,
stopping at a nonpositive pair or lag 200, with an upper cap at trajectory
length. Constant trajectories return null. This explicitly defined pairing is
not a convergence certificate, a guarantee of standard initial-sequence
properties, or a justified accuracy target. Reducible support is flagged on
every run. Sample-mean error, coverage, TV, starts, and warmup remain visible
alongside any ESS estimate.

## Literal physical and censored accounting

The direct return-kernel method draws from the exact algebraic balanced-state
censoring matrix. Its timed preparation includes physical-chain construction
and the rational first-return solve separately. Its timed draws **bypass the
physical excursion** and are labeled diagnostic only.

The physical method constructs the chain, then counts every literal step,
including holds, until the next balanced state. It does not perform the
censoring solve in its operational path. Its exact diagnostic is separate.
Physical steps, returned ordinary tables, incomplete-excursion steps, balanced
stationary probability, and per-start expected steps are separate fields.
At stationarity the expected steps per returned table are exactly
`1 / pi(balance)`; this expectation includes rare long excursions and is not
an observed short-run average. This relation does not assert independence of
returned tables or justify a cold-start schedule.

An excursion exceeding its cap terminates that run. It does not discard the
excursion and continue, emit a replacement, or count an unfinished table.
Partial trajectories and elapsed costs remain available, explicitly labeled
failed; ESS/throughput is unavailable for a failed run. A method with any failed
run receives no aggregate median sampling time, avoiding a survivor-only speed
comparison. The successful paths are still individually inspectable.

## Work limits and reproduction

The panel uses DP caps of 20,000 states/200,000 transitions and a full-fiber
oracle cap of 2,000 tables. Exact cycle-kernel/Poisson diagnostics cap dimension
at 48, so larger enumerated cases still get trajectories and exact target
moments but explicitly omit the dense diagnostic. Cycle enumeration caps at
1,000 cycles/100,000 search nodes, and weighted lines cap at 2,000 tables.
Literal oracle construction uses the reported `IdealChainBudget`; physical
runs cap at 10,000 steps per excursion and 100,000 steps across warmup and draws.
These limits bound counted work, not elapsed time. Diagnostic rational caps
are post-operation checks on retained rational results; temporary products
and sums before reduction are not preflight bounded. The stipulated small
fixtures are not a guarded general service for arbitrary inputs.

The CLI caps outputs at 10,000, warmup at 2,000, and seed repetitions at five.
Resource exhaustion is explicit per case/method/run; a partial cycle catalog
is never silently used. Invalid inputs or programming errors raise rather
than being presented as valid benchmark measurements.

```sh
PYTHONPATH=src python3 -S experiments/sampler_benchmarks.py \
  --draws 500 --warmup 200 --repetitions 2
PYTHONPATH=src python3 -S -m unittest discover -s tests -p 'test_chain_diagnostics.py'
PYTHONPATH=src python3 -S -m unittest discover -s tests -p 'test_sampler_benchmarks.py'
```

`--smoke --draws 40 --warmup 10 --repetitions 2` runs a smaller control panel.
The JSON records complete synthetic inputs, budgets, seeds, environment, work,
costs, failures, and source hashes. No general rapid-mixing, practical-scale,
real commuting accuracy, or complete finite-bit #115 superiority claim follows from it.

## Observations in the saved bounded panel

The saved panel has 18 cases, 500 retained outputs per requested run, warmup
zero/200, and two seeds per start. The dense diagnostic state cap explicitly
omits four larger fibers (90, 120, 282, and 720 tables); target enumeration and
DP draws still complete. All DP, worker-urn, and heat-bath requests complete.
Five literal physical runs exhaust an excursion budget and retain 78–409
outputs; their incomplete excursions are counted and their method medians are
unavailable.

On the tiny ideal panels, the exact stationary variance-inflation factors for
the reported observable are **7,679** and **15,359** per returned table, versus
one for the iid DP and single-rectangle full-line heat bath. Exact mean physical
steps per return are seven and nine. Fast algebraic direct draws do not remove
that correlation or establish fast literal sampling.

For the uniform commute fixture, the observable's exact inflation factors are
approximately 15.63 (equal rectangles), 16.30 (equal all-simple cycles), 10.52
(supplied tuned rectangles), and 10.45 (supplied tuned all-simple cycles). The
weighted fixture gives approximately 14.19, 13.50, 10.05, and 9.70. These show
improvements to this stationary observable under the supplied mixtures. They
do not establish a general speedup, and the original tuning cost remains
unmeasured. Exact iid DP remains a useful small-fiber baseline; its favorable
local measurements do not predict behavior on fibers beyond its budgets.
