# Reference implementation preparation benchmarks

Three bounded Python changes reduce repeated preparation: weighted-DP categorical plans, communicating classes via iterative strongly connected components, and cycle-local heat-bath line reuse. The saved [result](../reports/implementation-benchmarks.json) contains three raw timing repetitions per phase, medians, exact comparisons, source SHA-256 digests, environment and allocation measurements.

Run this opt-in experiment from the repository root:

```sh
PYTHONPATH=src python3 experiments/implementation_benchmarks.py \
  --output .local/reports/implementation-benchmarks.json
```

It requires only Python 3.10+ and Git, including commit `d851f00508840e5182fe5e9328446e65626f6e6b`. Both baseline modules are loaded read-only with `git show` into an isolated in-memory package. No baseline source copy is committed. The default output is also under `.local/reports/`; generating a new published result requires explicitly supplying `--output reports/implementation-benchmarks.json`. Timing is not a CI check.

## Observed medians

These measurements come from the saved run, with uncontrolled machine load. Seconds below exclude input construction; their preparation boundaries differ as explained below.

| Fixture and operation | Baseline seconds | Candidate seconds |
| --- | ---: | ---: |
| Rational/factorial 3×3 margins 6, warmed 2,000 weighted draws | 0.070000 | 0.005260 |
| Directed cycle, 256 states, communicating classes | 1.067499 | 0.004381 |
| Uniform 2×2 margins 120, 121-state heat-bath construction | 0.100976 | 0.042202 |
| Factorial-weighted 2×2 margins 30, heat-bath construction | 0.010179 | 0.004608 |
| Weighted/capped overlapping cycles, 14-state heat bath | 0.002055 | 0.001359 |

Including dense matrix/state construction, the 256-state SCC comparison is **1.081796 → 0.029257 s**. Including problem, weights, input-fiber and catalog construction, the 121-state heat-bath comparison is **0.102430 → 0.043193 s**. This demonstrates why input preparation belongs in a separate phase.

There are also small regressions. On the weighted 3×3 fixture, the first draw after completed DP takes **45.37 → 48.25 μs**; a cold first draw takes **4.7927 → 4.8331 ms**. A forced singleton heat-bath line has no reusable work: construction excluding input setup takes **78.83 → 79.58 μs**, and including it takes **141.08 → 142.17 μs**. Empty-catalog construction including setup takes **2.8055 → 2.8746 ms**. These small differences are noise-scale observations from three repetitions, not stable overhead estimates. The intended weighted benefit requires repeated draws; the heat-bath benefit requires multi-state lines.

## Phase boundaries and exact checks

For weighted draws, the DP phase excludes constructors and feasibility checks. The first draw after DP includes lazy preparation only for visited choices and excludes RNG creation. A cold first draw includes problem/weights/sampler construction, feasibility, DP and the visited plans, while excluding RNG creation. Complete-cache preparation is a separate benchmark-only eager phase after completed DP. Production remains lazy. Warm 2,000-draw batches include seeded RNG creation and exclude DP and complete-cache preparation.

For communicating classes, adjacency construction always occurs inside the timer. Input setup refers to constructing the supplied state tuple and dense rational matrix. There is no persistent SCC cache. The independent Boolean-closure oracle from `tests/test_kernels.py` checks all 512 three-vertex directed graphs; the benchmark does not run the test suite.

Every heat-bath construction includes complete-fiber validation and its DP count, target masses, dense matrix assembly and exact stochasticity/detailed-balance assertions. Cycle-line reuse occurs within one construction and resets for each cycle. Repeated constructions retain no line cache. Complete states, matrices and stationary vectors match the pinned baseline and the independent pairwise-line/rational-weight oracle from `tests/test_kernels.py`, including capped/weighted/structural-zero, overlapping-cycle, empty-catalog and singleton-line fixtures.

Across all four weighted fixtures, 200 seeded sampled tables and every RNG `(stop, value)` pair match exactly, as do normalizers and DP statistics. Compact JSON SHA-256 digests record the sample sequences and traces without publishing duplicate arrays. These replay checks supplement the independent law checks in the ordinary test suites.

## Preparation and memory costs

The weighted 3×3 DP has 58 states and 462 transitions. Preparing all 57 positive nonterminal plans takes a median **0.000402 s** and stores 462 cumulative integers with **6,873 integer bits**. Its dictionary and plan tuples occupy 8,696 shallow bytes; unique cumulative integer objects occupy 12,424 bytes. Those object sizes exclude existing DP state-key objects and can include shared/interned integers. A separate incremental `tracemalloc` run after completed DP records **24,080 retained / 26,312 peak bytes**. Integer-bit payload is not heap usage, and these three measurements are not interchangeable.

With input objects prebuilt, the 256-state sparse-cycle SCC traced peak decreases from **2,167,672 to 67,576 bytes**. Forward and reverse adjacency each store one entry per edge; dense graphs can still require quadratic temporary storage. The 121-state heat-bath traced peak increases from **1,442,656 to 1,461,768 bytes**. Its cycle-local visited indices, target indices and probability vector each contain at most the supplied fiber size, with no persistent cache.

Allocation runs are separate from timing, retain returned outputs, and measure Python allocations rather than process RSS or native allocator usage. Existing state/transition caps do not bound rational bit lengths or heap bytes. Explicit dense kernel output and exact balance validation remain quadratic; fiber and cycle enumeration remain potentially exponential. The results establish finite reference-implementation preparation savings on these fixtures, with no inference about mixing rates or complete-sampler performance.

## Keeping the maintenance cost proportionate

A proposed audit-preparation refactor was deferred: roughly 12 milliseconds saved
on synthetic fixtures did not justify 85 net production lines and 149 net test
lines. A cosmetic Lean deduplication also remains unpromoted; it would add a helper
and require new proof verification without improving the sampler or reducing
total source size. The existing mathematical and failure-mode tests remain.

Historical producer hashes now describe provenance independently of current
mathematical replay. Exact certificate obligations still have to pass. Likewise,
changed orchestration scripts do not retroactively invalidate unchanged theorem
sources, and an old compiler receipt does not verify those changed scripts. This
avoids unnecessary report regeneration or proof rebuilds without weakening the
mathematical checks. Full strict Comparator verification remains a separate task.
