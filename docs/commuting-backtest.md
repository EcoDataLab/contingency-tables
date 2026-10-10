# Public commuting joint-table hold-out backtest

The margin-only conditional-worker law misses the held-out published cell in
all 100 predefined Rhode Island cases. Uniform aggregate tables cover all 100,
with much wider intervals. This is an empirical check of two probability laws
on a fixed public case frame, not a sampler-performance experiment or a
calibration guarantee. The complete observations, margins, intervals, errors,
and numerical checks are retained in the
[machine-readable report](../reports/commuting-backtest.json).

| Primary cell score, central 95% model interval | Uniform aggregate tables | Ordinary conditional-worker law |
| --- | ---: | ---: |
| Published-cell coverage | 100 / 100 | 0 / 100 |
| Mean interval width, jobs | 7,912.36 | 124.64 |
| Mean absolute error of model mean, jobs | 1,802.98 | 2,572.06 |
| Root mean squared error, jobs | 2,762.40 | 4,295.02 |
| Mean signed error, jobs | −744.32 | −1,223.30 |
| Mean absolute error / case total | 4.36% | 5.57% |
| Mean interval width / case total | 17.26% | 0.36% |

Signed error means model mean minus the published count. These are unweighted
case means; large cases are not counted as more replications. The uniform
intervals are about 63 times wider on average. Broad coverage alone does not
show that uniform aggregate tables provide an accurate or scientifically
appropriate commuting model.

## Public observation and provenance

The observation is the Census Bureau's
[2023 Rhode Island LODES OD main JT00 file](https://lehd.ces.census.gov/data/lodes/LODES8/ri/od/ri_od_main_JT00_2023.csv.gz).
The [Census technical document, format 8.4](https://lehd.ces.census.gov/doc/help/onthemap/LODESTechDoc.pdf)
defines `main` as jobs whose workplace and residence are both in the selected
state, `JT00` as all jobs, and `S000` as their total count. Its release note
records Census approval of disclosure-avoidance practices. These released
counts are validation observations after processing and disclosure protection,
not literal ground truth about unique people or their daily journeys.

The source was accessed on **10 October 2026 UTC**. Its exact version text
reports data vintage **20251202_1657**, release format **8.4**. The full selected
file contains **390,223 block OD records** totaling **412,443 published jobs**.
We sum every record into the 25 home-county × workplace-county cells, using the
first five digits of each 2020 Census block identifier. Rows are home counties;
columns are workplaces. No RAC/WAC table, out-of-state auxiliary file, client
data, or production application is used. This is the intrastate job universe,
not all employment of Rhode Island residents or all jobs located in the state.

The retained public artifact is only a
[454-byte county table](../data/public-commuting/ri-2023-county-od.csv),
[source manifest](../data/public-commuting/source-manifest.json),
[version text](../data/public-commuting/version.txt), selected
[Census checksum entry](../data/public-commuting/census-checksum.txt), and
[selection protocol](../data/public-commuting/protocol.json). The block-level
download is not vendored. The Census checksum is for the **decompressed CSV**;
we verify it and separately hash the compressed download.

| Input | SHA256 |
| --- | --- |
| Compressed Census source, 2,181,612 bytes | `ba52ad6518bb9f9fc09675cf93a77ca3a9de2b8f4a91e15a927e66a0e5642e0a` |
| Decompressed CSV, 23,803,747 bytes; matches Census entry | `e6087fec026026ff47dd1f58ebda8ae15f17e9e6acbd16602223faaf93066206` |
| Retained 25-cell county table | `031fb665ef62c649f4a2aca7ffdcdb43a87ed67cb2aa2c104c867e7bdf63f7fb` |
| Protocol written before OD counts were downloaded or scored | `f2dda7a355e51fd6d506c61f6355a5834fca2f790fe778abe6e077f4838a2ee4` |

The manifest also records source URLs, access times, `Last-Modified`, the
documentation hash, source and subset byte counts, processing `createdate`,
the official checksum-file hash, and the aggregation total. A second live
download reproduced the compressed hash, official decompressed checksum,
version text, and every subset byte. A future source revision fails verification
instead of silently replacing this observation.

## Selection and withholding

Rhode Island was chosen for its small file and five counties, allowing an
exhaustive bounded comparison. Source availability and definitions were checked
first. The selection protocol was then written and hashed before the OD counts
were downloaded, aggregated, or scored. There was no search over states,
years, county pairs, or outcomes to improve performance.

The [chronology receipt](../data/public-commuting/protocol-freeze-receipt.json)
preserves the original protocol hash, its filesystem timestamp, the root
agent's receipt of that hash before acquisition, and the first verified source
snapshot time. It was written retrospectively after scoring and is not an
external preregistration. The original protocol bytes are unchanged.

The county universe is fixed to `44001`, `44003`, `44005`, `44007`, `44009`.
Take every unordered pair of distinct home counties and every unordered pair
of distinct work counties. Sort each pair by FIPS to fix orientation. This
gives `choose(5,2) × choose(5,2) = 100` candidate 2×2 tables. Retain all cases
except singleton feasible fibers; **all 100 were non-singleton and none were
excluded**. Invalid records, unexpected county identifiers, or numerical budget
exhaustion fail the experiment rather than shrink the denominator. No source
zeros become structural-zero constraints.

Each case's margins are derived within its two-home/two-work-county universe.
Other counties' jobs are outside that case. The program separates the margins
and held-out joint, constructs **every prediction before any scoring**, and
passes only margins to the prediction API. Public county identifiers define
the secondary metric, without entering either law. There are no fitted
parameters, travel distances, interaction weights, or joint-dependent choices.
The published joint reappears only in scoring and the retained audit report.

The 100 cases overlap a single released 5×5 county table. They are **not 100
independent replications**. Coverage here is the descriptive fraction of the
predefined case frame included by a model interval; we report no calibration
confidence interval or frequentist 95% coverage guarantee.

## Identical feasible tables, different laws

Let the home margins be `(r1,r2)`, work margins `(c1,c2)`, and total `N`. The
free count `x` determines the entire feasible table:

```text
                  work 1           work 2
home 1               x             r1 − x
home 2            c1 − x       r2 − c1 + x

L = max(0, r1 − c2),  U = min(r1, c1),  x ∈ {L,...,U}
```

Both laws assign positive mathematical probability to exactly this same fiber.
Uniform aggregate tables give each of the `U−L+1` integer tables equal weight.
Their free-cell mean is `(L+U)/2` and variance is `((U−L+1)^2−1)/12`.

The ordinary conditional-worker law corresponds to assigning fixed work
categories without replacement to labeled job slots, conditional on the same
margins. Its aggregate probability is proportional to the reciprocal product
of the four cell factorials. Therefore

```text
P(x) = choose(c1,x) choose(N−c1,r1−x) / choose(N,r1)
E[x] = r1 c1 / N
Var[x] = r1 c1 (N−r1)(N−c1) / (N²(N−1))  for N > 1
```

This is a conditional-independence allocation law. The name follows the
repository's worker baseline; the empirical input remains **all-job counts**.
It does not account for spatial association or make jobs into unique workers.
Uniformity on each restricted 2×2 fiber also need not be the marginal of a
uniform law on the full 5×5 fiber. The experiment tests the stated 2×2 laws.

For `x`, take the least integer with CDF at least `1/40` and the least with CDF
at least `39/40`. Keep the closed interval and map it through each cell's affine
formula. Discreteness makes the retained model mass slightly greater than
95%: 95.001%–95.088% under uniformity, and 95.025%–95.714% under the worker law.
This mass describes the assumed law, not an arbitrary fixed released joint.

Each of the four cells is an invertible affine function of `x`, so their
coverage indicators coincide. The report retains 400 cell scores, but its
primary denominator is **100 cases**, not 400 independent observations. The
signed errors across all four cells cancel because both laws preserve the
margins. Primary signed error therefore refers to the FIPS-first cell; the
secondary flow metric has a more interpretable orientation.

## Intercounty flow and a fixed first-case example

The secondary metric counts jobs with different home and work county labels
within a case. When the two home counties and two work counties are disjoint,
all jobs in that case are intercounty jobs, so the metric equals the known
total. This happens in **30 cases**. Both laws cover those cases with zero-width
metric intervals because the margins already identify the metric. The
remaining **70 informative cases** are scored separately.

| Intercounty metric, cases not identified by margins | Uniform aggregate tables | Ordinary conditional-worker law |
| --- | ---: | ---: |
| Coverage | 70 / 70 | 0 / 70 |
| Mean interval width, jobs | 12,498.71 | 162.30 |
| Mean signed error, jobs | +2,259.17 | +4,705.71 |
| Mean absolute error, jobs | 2,884.21 | 4,705.71 |
| Mean signed error / case total | +5.34% | +8.17% |
| Mean absolute error / case total | 5.83% | 8.17% |

The worker-law mean overstates this flow in all 70 informative cases. That is
consistent with a margin-only independence model failing to represent the
published concentration of jobs within the same home/work county. This explanation is an inference
from the released table, not a causal attribution or a claim about individual
travel behavior. Uniformity has smaller mean errors in this panel but also
overstates the metric on average and leaves wide uncertainty.

As a reproducible illustration, use the **first case in FIPS order**, not a
case selected for its performance. Home and work county pairs are both
`(44001,44003)`, and the published table is:

```text
             work 44001   work 44003   home total
home 44001       5575         1562         7137
home 44003        993        29994        30987
work total       6568        31556        38124
```

Only the margins enter prediction. The first published cell is 5,575.
Uniformity gives mean 3,284 and interval `[164,6404]`; the worker law gives mean
1,229.56 and interval `[1173,1286]`. Published intercounty jobs total 2,555;
the corresponding intervals are `[897,13377]` and `[11133,11359]`. The difference
comes from the laws, with the same margins and feasible tables.

## Numerical evidence and reproduction

Uniform quantiles, means, and variances use exact integer/rational arithmetic.
Worker means and variances use the exact formulas above. Worker probabilities
use a mode-centered binary64 hypergeometric recurrence over the full support,
normalized with compensated summation. The run visits **832,887 support
points**, with largest support **60,460**. There is no Monte Carlo error, normal
approximation, or tail cutoff. The job total is not iterated by an individual
urn sampler and the full 5×5 fiber is not enumerated.

Remote relative weights underflow to zero at **584,920 support points**. This is
retained in the report rather than hidden. The largest normalization residual
is `1.11e−16`; the largest numeric mean discrepancy from the exact formula is
`7.28e−12` jobs, and largest relative variance discrepancy is `3.47e−16`.
Those checks do not supply a formal large-case rounding or tail certificate.
The independent checks are stronger evidence for the intervals actually used:

- An exact combinatorial `Fraction` oracle checks all **819 margin pairs with
  total at most 12**. All 1,638 central-interval endpoints agree; maximum
  point-probability discrepancy is `1.11e−16`.
- [SciPy's documented hypergeometric implementation](https://docs.scipy.org/doc/scipy/reference/generated/scipy.stats.hypergeom.html),
  version **1.18.1**, independently checks all **200 endpoints in the 100 public
  cases**, with zero mismatches. Maximum interval-mass discrepancy is
  `1.67e−12`. The retained report includes this optional-library receipt.
- Ten tests check independent small-law combinatorics, uniform integer
  quantiles, a large symmetric worker distribution with recorded underflow,
  held-out-joint separation, invalid/budget rejection, source orientation,
  checksum integrity, exhaustive selection, and the metric denominators.

The retained run constructed all predictions and validated local source hashes
in about **0.84 seconds**. This measured Python computation excludes acquisition,
scoring, exact-oracle and SciPy checks, and writing. It is not an asymptotic
runtime claim or a measurement of the universal #115 sampler.

From the repository root, the default replay uses only the standard library:

```sh
python3 experiments/commuting_backtest.py --output /private/tmp/commuting-backtest-replay.json
python3 -m unittest discover -s tests -p test_commuting_backtest.py -v
```

To repeat the additional receipts, use a Python environment with SciPy 1.18.1
installed and run:

```sh
python3 experiments/commuting_backtest.py --crosscheck-scipy --verify-source --output /private/tmp/commuting-backtest-reverified.json
```

`--verify-source` performs bounded downloads from the fixed public Census URLs,
verifies the official decompressed checksum, and requires byte-for-byte subset
and version agreement. It never refreshes the pinned input. Default execution
is offline. Timestamps, environment details, optional receipts, and elapsed
time can differ on replay; observations, case selection, law predictions, and
scores are deterministic.

This one state/year result establishes a concrete failure of the ordinary
margin-only worker law for this public case frame and shows how much wider the
uniform intervals are. It does not validate either law across commuting
applications, propagate uncertainty in Census disclosure processing, measure
mode choice or commute distance, or produce VMT/emissions estimates.
