# Classical worker law: mature-library benchmarks

The existing Python `OrdinaryWorkerSampler` is substantially slower than mature library implementations on these measured unrestricted cases. This comparison measures the **same inverse-factorial fixed-margin law** in the local urn sampler, SciPy `stats.random_table`, and R `stats::r2dtable`. It does not execute the uniform-table algorithm in Finding #115, and it supplies no runtime measurement for that theorem.

The reproducible harness is [worker_library_benchmarks.py](../experiments/worker_library_benchmarks.py); all timings, margins, seeds, diagnostics, dependency versions and source hashes are in [worker-library-benchmarks.json](../reports/worker-library-benchmarks.json). The checked-in measurement began at `2026-10-10T05:00:28Z` (October 9 Pacific time).

## Matching the target law

All cells are permitted, both margin vectors are fixed, and there are no bounds, structural zeros or interaction activities. For feasible table `X`, the probability is

\[
P(X) = \frac{\prod_i r_i!\prod_j c_j!}{N!\prod_{i,j}X_{ij}!}.
\]

For `(2,2)` by `(2,2)` margins, the top-left cell has probabilities `1/6, 2/3, 1/6` for counts `0,1,2`. Uniform sampling of the three aggregate tables would have probabilities `1/3,1/3,1/3`; it would be an inappropriate comparator.

[SciPy's documentation](https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.random_table.html) identifies this as the fixed-margin independence distribution and documents `rvs` methods `boyett`, `patefield`, and automatic selection. It gives Boyett `O(N)` time/space and Patefield `O(K log N)` time with small workspace, where `K` is cell count. Those are documented algorithm descriptions, not fitted runtime laws from this experiment. [R's documentation](https://stat.ethz.ch/R-manual/R-devel/library/stats/html/r2dtable.html) specifies Patefield sampling and the public `r2dtable(n,r,c)` API.

The harness independently enumerates the entire small 2×2 and 3×3 fibers (3 and 21 tables), assigns exact rational inverse-factorial masses, and checks their normalization against the factorial formula. Every SciPy `pmf` is compared against those rational probabilities; the maximum absolute discrepancy was `1.11e-16`. R exposes no PMF through this API, so its check uses the documented algorithm, verifies every sampled table's margins, compares small-fiber frequencies to the independent oracle, and compares observable moments. This finite empirical check is not an exact-law proof of R's floating-point implementation.

## Measured scaling

Numbers below are **median measured draw microseconds per table**, across three repetitions after one discarded warmup table per repetition. SciPy and R use one batch API call; the urn implementation loops to return the same number of tables. Batch sizes range from 1024 in each small-law case down to 2 at one million workers. Inspect the JSON for every repetition and for setup-plus-draw totals.

| Case | Python urn | SciPy auto | SciPy Boyett | SciPy Patefield | R Patefield API |
|---|---:|---:|---:|---:|---:|
| 2×2, N=4 | 3.59 | 0.05 | 0.04 | 0.07 | 0.10 |
| 3×3, N=6 | 5.81 | 0.07 | 0.07 | 0.24 | 0.19 |
| 20×5, N=1,000 | 973.12 | 7.48 | 8.76 | 7.22 | 4.87 |
| 20×5, N=10,000 | 9,989.75 | 9.88 | 92.27 | 8.65 | 12.50 |
| 20×5, N=100,000 | 100,836.80 | 15.20 | 919.55 | 12.02 | 290.27 |
| 20×5, N=1,000,000 | 1,003,531.21 | 24.46 | 9,693.71 | 26.40 | 5,836.96 |
| 5×5, N=10,000 | 8,496.05 | 3.68 | 93.32 | 3.03 | 16.63 |
| 100×5, N=10,000 | 11,007.94 | 40.20 | 97.74 | 40.68 | 39.37 |
| 1000×5, N=10,000 | 10,946.22 | 95.08 | 96.65 | 342.49 | 207.01 |
| 100×20, N=10,000 | 14,071.83 | 92.85 | 94.30 | 182.86 | 116.74 |
| 100×100, N=10,000 | 16,956.68 | 98.69 | 90.41 | 769.28 | 418.13 |
| Skewed 3×5, N=1,000,000,000 | 13.87 | 1.13 | skipped | 0.87 | skipped |

At 20×5 and one million workers, the measured Python urn draw took about **1.00 second per table**, compared with **26.4 microseconds** for SciPy Patefield, approximately 38,000 times faster in this run. R's public API took about 5.8 milliseconds per table in a batch of two. These are implementation-specific, batch-specific measurements, not a general algorithm ranking or complexity proof.

The method crossover is also retained: at 100×100 with ten thousand workers, Boyett was about eight and a half times faster than Patefield. At fixed 20×5 dimensions, Boyett and the local urn showed strong numeric-total dependence, while SciPy Patefield changed much less over the measured range. Output dimensions affect the methods differently; the reported row and column scaling panels hold `N=10,000` fixed.

The skewed large-total case has row margins `(999999990,6,4)`. The local sampler reserves the enormous row for deterministic completion and needs just ten random urn draws per table. This is an inexpensive special case; balanced billion-worker margins would exceed its work budget.

## Timing and implementation caveats

Each Python repetition constructs a sampler and RNG, then warms up, then measures a batch. R's external wrapper runs one fresh process per case and performs the same phases internally. The JSON separates `setup_seconds`, `warmup_seconds`, `draw_seconds`, `setup_plus_draw_seconds`, `setup_warmup_draw_seconds`, and observation/validation cost. Python times use `perf_counter`; R uses elapsed `Sys.time`. Batching amortizes timer granularity, but the fastest measurements should be interpreted at their displayed scale rather than as exact constants.

Setup measures preparation exposed through the public APIs: margins/frozen sampler and RNG initialization. Scratch preparation inside the native sampling call remains in the draw phase. In particular, [R's 4.5 source](https://github.com/wch/r-source/blob/R-4-5-branch/src/library/stats/src/random.c) allocates `N+1` doubles and computes their log-factorials inside each `r2dtable` call before generating the requested batch. Thus this API has a numeric-total setup cost, even though its table generator uses Patefield's method. Batch size affects how much of this overhead is charged to each table. The harness deliberately leaves that cost in the public API measurement.

R process wall times are separately recorded (about 0.14–0.22 seconds per case here). They include startup, all repetitions, validation and serialization. They should be used when assessing the overhead of calling R through a fresh subprocess; native draw-phase times should be used when assessing sampling in an existing R process. Python imports and SciPy module initialization are outside the per-case sampling timings.

The billion-worker case skips R before its log-factorial allocation and skips Boyett before its `O(N)` scratch allocation. Each has a configured `N<=1,000,000` cap. These are safety/work-budget decisions, not measured failures or evidence of incorrect distributions. Urn work is capped at one million random draws per table and three million across a repetition, including warmup; output size is bounded separately. No run invokes a literal astronomical theorem schedule.

The local worker baseline uses its instrumented `sample_with_stats` API, including work counters. SciPy/R use their public native samplers and their own output representations; no attempt is made to erase these implementation costs. Seeds match numerically within a case but RNGs differ: Python `random.Random` (MT19937), NumPy `Generator(PCG64)`, and R `Mersenne-Twister/Inversion/Rejection`. Identical seeds across runtimes are not identical streams.

Hardware was an Apple M1 Pro, model identifier `MacBookPro18,3`, 10 logical CPUs and 32 GiB memory, on macOS 15.7.9 arm64. Measurements ran sequentially, with common numerical thread environment variables set to one; actual native thread counts and shared host activity were not instrumented. Runtime versions were Python 3.14.3, NumPy 2.5.3, SciPy 1.18.1, and R/stats 4.5.1.

## Observed statistics and verification

For every case the report computes exact rational expectation and variance of the abstract nonseparable linear statistic `sum((i%7-j%5)^2 * X[i,j])`, using the full covariance formula, and also computes exact moments of the first cell. It records observed means, unbiased sample variances, and mean errors divided by the known iid standard error. Large-case sample counts are deliberately small; observed variances are noisy. The largest metric mean discrepancy was about 3.38 standard errors in this run across the entire panel, which is retained without declaring a sampler failure or certifying agreement from a threshold.

In the two small fibers, 3072 samples per method gave empirical total variation of approximately 0.006–0.013 (2×2) and 0.022–0.033 (3×3). These are distances of finite empirical distributions from the exact law; they are not bias estimates or convergence certificates. All returned tables passed margin checks.

Eleven focused tests passed, including independent full-fiber normalization, nonseparable moments checked by enumerating the fiber, bad-output rejection, optional dependency skips, preflight budget rejection, recorded timing-phase arithmetic, full SciPy PMF comparisons, actual R API/readback, preflight rejection of overflowing case/repetition seeds, and actual R sampling at the largest signed 32-bit seed. Run without SciPy or R and the corresponding optional integration test is skipped with a reason; the rest of the harness remains usable.

## Reproduction

The optional SciPy dependency was installed in a new private virtual environment; the pre-existing project `.venv` was not modified. R was already installed and no R packages were installed. To recreate the Python dependency versions:

```sh
python3 -m venv .local/worker-library-benchmark-venv
.local/worker-library-benchmark-venv/bin/python -m pip install scipy==1.18.1 numpy==2.5.3
PYTHONPATH=src .local/worker-library-benchmark-venv/bin/python -m unittest discover -s tests -p 'test_worker_library_benchmarks.py' -v
OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 VECLIB_MAXIMUM_THREADS=1 NUMEXPR_NUM_THREADS=1 PYTHONPATH=src .local/worker-library-benchmark-venv/bin/python experiments/worker_library_benchmarks.py
```

The checked-in measurement additionally supplied `--hardware-json` containing the public inventory described above because sandboxed `sysctl` reads were unavailable. Without that option the script records accessible hardware metadata and marks unavailable details. `--case NAME`, `--warmup`, `--repetitions`, `--seed`, and `--output` allow bounded partial reruns. Optional dependencies are discovered and explicitly skipped with reasons; this script does not install them or dispatch remote jobs.
