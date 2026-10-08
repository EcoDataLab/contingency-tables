# Contingency-table research for commuting and consumption-based emissions

This note specifies public research applications of OpenAI result #115. It uses a completely synthetic example and public methodological references. It does not claim that the prototype is a validated commuting model, that a uniform table is a plausible behavioral forecast, or that a table sampler recovers confidential records.

The practical aim is to replace a single unexplained allocation with a reproducible distribution of allocations, while preserving accounting constraints and the distinction between source observations and modeled quantities. The immediate research products are exact small-instance benchmarks, feasibility diagnostics, and conditional sensitivity analyses. A deployable large-scale estimator needs separate computational and empirical validation.

## 1. Where the two-way problem fits

| Application | Rows and columns | Appropriate use | Main limitation |
| --- | --- | --- | --- |
| Allocate commute modes within one home area | Workplace destinations × modes, including work from home | Preserve a chosen home–work flow for each destination and reconciled home-area mode totals while exploring their unknown association | Source totals come from different statistical universes; route and behavioral information requires a specified weighted law |
| Explore an unavailable workforce joint distribution | Earnings bands × disjoint industry groups, within a workplace area | Quantify sensitivity to a joint distribution that is only partially observed | First check whether the public source already publishes the desired cross-tabulation |
| Complete an aggregate employment table | Disjoint areas × disjoint industry leaves, for one ownership class and period | Bound modeled allocations using published cells and compatible margins | Suppression, rounding, classification changes, and overlapping hierarchies require explicit treatment |
| Construct household-category ensembles | Two compatible household attributes, such as household size × tenure | Examine the effect of joint composition on nonlinear consumption predictions | Margins do not identify correlations; higher-dimensional household constraints are not automatically a two-way table problem |

LODES publishes origin–destination job counts, residence-area characteristics, and workplace-area characteristics. Its WAC filenames can select earnings groups `SE01`–`SE03`, and those files contain industry columns `CNS01`–`CNS20`. A needed earnings-by-industry table may therefore be directly available; verify the same job type, period, geography, release, and totals before constructing it from marginal shares. Direct public aggregate evidence takes precedence over an independence approximation. See the [LODES 8.3 file specification](https://lehd.ces.census.gov/data/lodes/LODES8/LODESTechDoc8.3.pdf), especially the WAC layout. The format version is not the source-data vintage.

The useful mathematical scope is also precise. Result #115's [exact uniform sampler](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Exact-Uniform-Sampling-of-Contingency-Tables-with-Arbitrary-Margins-September-24-2026/main.pdf) concerns ordinary tables with fixed margins. Its [companion](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/An-FPRAS-for-Cell-Bounded-Contingency-Tables-September-24-2026/main.pdf) provides approximate counting for bounded cells, including forbidden cells. Neither statement by itself establishes a practical rapid-mixing weighted sampler for arbitrary sparse transportation models. Keep a new kernel's invariant-law proof, its mixing evidence, and any complexity theorem separate.

## 2. A commute model that really is a two-way table

Fix a home area `o`. Let `N[o,d]` be the chosen integer total assigned to workplace destination `d`, and let `M[o,m]` be the chosen integer home-area total in mode `m`. Define

$$
\Omega_o=\left\{X\in\mathbb Z_{\ge0}^{D\times K}:
\sum_m X_{dm}=N_{od},\quad
\sum_d X_{dm}=M_{om},\quad
\ell_{dm}\le X_{dm}\le b_{dm}\right\}.
$$

Include work from home as a column if the cohort includes those workers. A work-from-home entry retains a workplace association for bookkeeping but contributes no journey to that workplace under this model. Hybrid attendance belongs in a separate attendance model; a usual-mode estimate is not a count of remote days.

With fixed controls and no cross-origin coupling, the feasible space is a product of these home-area tables. The target distribution factorizes too when its weights factorize by home area. This offers a natural way to parallelize exact reference calculations and independent origin-level sampling.

An integration must also preserve the existing model's staging. A workflow that assigns work from home through an origin intercept, then an other/unrouted category, then four routed modes has a different factorization from a joint six-mode table model. Joint sampling is a distinct model variant requiring validation. A staged adapter could instead condition on the earlier assignments and sample a remaining routed-mode subtable, explicitly preserving those stage totals. The five-mode synthetic example below is a research illustration, not a drop-in specification for that staged workflow.

IPF produces fractional fitted expectations; it does not by itself specify a sampling law. Fractional departure-time or block-level subcells can also be numerical quadrature weights rather than integer worker counts. Do not round those weights into fictitious workers simply to invoke an integer-table theorem. Keep the count-allocation layer and the continuous integration layer explicit.

Adding destination-by-mode totals across multiple home areas changes the problem: the cells are `X[o,d,m]` with overlapping two-dimensional margins. Flattening the array does not turn all those constraints into ordinary row and column sums. Such an extension needs a new reduction or proof. The same warning applies to household tensors constrained simultaneously by age, income, tenure, and household size.

## 3. State the target distribution

Different laws answer different questions even when they have identical support.

**Uniform tables:**

$$
\pi_U(X)=|\Omega_o|^{-1}.
$$

This gives each aggregate matrix equal probability. It is a valuable reference law and an exact computational benchmark. Marginal constraints alone do not make it a scientifically preferred uncertainty distribution.

**Conditional independent-worker choices:** Suppose the `N[o,d]` members of each row independently choose modes with positive relative activities `a[d,m]`, then condition on the column totals and cell bounds. The row multinomial coefficients give

$$
\pi_P(X)=Z^{-1}\prod_{d,m}\frac{a_{dm}^{X_{dm}}}{X_{dm}!},\qquad X\in\Omega_o.
$$

The same law follows from independent Poisson cell counts conditioned on the controls. The factorials count the different labeled assignments leading to the same aggregate matrix. Dropping them changes the law. For the uncapped `2 × 2` problem with both margins `(2,2)` and every activity equal to one, the three feasible tables have uniform probabilities `(1/3,1/3,1/3)` but conditional-Poisson probabilities `(1/6,2/3,1/6)` in order of the top-left entry `0,1,2`.

**A rare-category example.** Let both margin vectors be `(a,M)`, with `M≥a≥1`. Every ordinary feasible table has the form

$$
\begin{pmatrix}x&a-x\\a-x&M-a+x\end{pmatrix},\qquad x=0,\ldots,a.
$$

Uniform aggregate tables give `E[x]=a/2`, independently of `M`. This attains the [sharp ordinary-table mean bound](small-entry-formalization.md). Under ordinary independent-worker allocation, `E[x]=a²/(a+M)`, which tends to zero as `M` increases. For the synthetic choice `a=10,M=990`, those means are **5** and **0.1**, despite identical controls and support. This is an exact model comparison, not evidence that either law describes a particular workforce. Better uniform-table sampling cannot decide the appropriate behavioral or uncertainty model by itself.

A gravity-style choice `a[d,m] = exp(-beta[m] * travel_time[d,m])` is one possible model, with behavior and route assumptions requiring empirical support. Work-from-home activity needs its own model. Missing route data is a missing predictor, not a reason to assign zero probability.

**Row and column scaling invariance.** For either the product-activity law or the factorial law, replacing `a[d,m]` by `u[d] * a[d,m] * v[m]` multiplies every feasible table's unnormalized weight by the same number,

$$
\prod_d u_d^{N_{od}}\prod_m v_m^{M_{om}}.
$$

Thus row normalizers and IPF mode multipliers cancel after conditioning on the corresponding exact margins. Association information remains in interaction odds, such as `a[i,j]a[k,l]/(a[i,l]a[k,j])`. This is both a computational simplification and a useful invariance test. Margins already encode the calibrated mode totals; extra multipliers cannot create new conditional information.

Under lower-bound shifting `Y = X - lower`, preserve factorials as `(Y[d,m] + lower[d,m])!`. Replacing them by `Y[d,m]!` would silently change the target. Positive rational activities permit exact arithmetic in small reference instances; floating-point `exp` values require an explicit approximation contract before a sampler is described as exact for those weights.

## 4. Reconcile controls before sampling

ACS commute estimates describe workers and usual travel behavior; LODES describes jobs and their workplace–residence associations. They differ in coverage, reference periods, primary-job definitions, and location concepts. LODES contains no observed commute-mode variable, and a workplace association need not represent a daily journey. These are source-design differences, not numerical errors to fix by blindly forcing totals equal. The Census Bureau's [ACS–LODES design comparison](https://www.census.gov/library/working-papers/2014/adrm/ces-wp-14-38.html) explains the distinctions.

For each run, specify a common analytical cohort, geography vintage, source periods, source release identifiers and hashes, job type, and category mapping. Retain the original source estimates. Store any reconciliation and balanced integerization as separate transformations with before/after values and a rationale. If ACS proportions are applied to a LODES job total, identify that operation as a modeling assumption rather than an observed joint total.

Check cross-boundary coverage before defining the margins. LODES OD files are organized by workplace state: its `main` file has both ends within the state, while `aux` has a workplace in the state and a residence elsewhere. A complete residence-based commute distribution can require files from multiple workplace states; filtering a single workplace-state file to in-state residents is not sufficient. The [LODES file specification](https://lehd.ces.census.gov/data/lodes/LODES8/LODESTechDoc8.3.pdf) defines those parts.

Keep these input states distinct:

| Input state | Treatment |
| --- | --- |
| Published count chosen as an exact conditional control | Preserve the value and its source lineage; conditional exactness does not remove source error |
| Survey estimate with uncertainty | Propagate an explicitly specified joint control model in an outer layer, or analyze several control scenarios |
| Rounded published quantity | Use a documented rounding interval where relevant; do not manufacture exact additive identities |
| Suppressed or unavailable quantity | Keep it unknown and infer only under labeled assumptions or valid bounds |
| Observed public zero | Preserve it as a reported value; it is not automatically an impossible event in a latent model |
| Structural zero | Set the upper bound to zero only with a stated substantive restriction |
| Missing route, stale service feed, or route-engine failure | Record missing coverage; do not turn it into a structural zero |

BLS withholds some QCEW employment and wage data for confidentiality while including them in higher-level totals. Its annual averages also require attention to their units and rounding. A worker-count table should not mix annual-average employment with monthly job counts or wage dollars. Use disjoint leaves for an exact table reduction, and treat wages and derived pay as separate quantities. See the [QCEW overview](https://www.bls.gov/cew/overview.htm).

Published LODES data already undergo disclosure avoidance. Choose and document an uncertainty model appropriate to the actual release; do not assume that every source uses independent noise, the same privacy mechanism, or a known cellwise error distribution. A feasible completion is a modeled aggregate, not recovered confidential truth. The [LODES methodology report](https://www.census.gov/library/working-papers/2025/adrm/CES-WP-25-52.html) is a starting point for the source-processing review; its methodology version and the file-format version are different concepts.

### Feasibility and bounds

Equal grand totals are necessary but insufficient under sparse support. Shift out lower bounds, obtaining residual margins `r'`, `c'` and capacities `b' = upper - lower`. Reject negative residuals. Build a network from source to row nodes with capacities `r'`, row to column nodes with capacities `b'`, and column nodes to sink with capacities `c'`. The integer table is feasible exactly when maximum flow equals the residual grand total. A deficient cut can identify the subset of controls and allowed cells causing failure.

Report infeasibility as a diagnostic; do not silently drop a control, add a forbidden edge, or widen a bound. Individually minimize and maximize each cell over the feasible set when useful. Such tightened ranges are valid simultaneously as bounds, but arbitrary combinations of their endpoints need not be feasible tables. Decomposing disconnected support components also requires compatible totals within every component.

Population reconciliation and travel-time controls can remain incompatible with route assumptions even when a mode-margin table is feasible. Check these at the appropriate model layer: time-bin constraints are additional restrictions, not automatically ordinary row and column sums. A different sampler cannot repair incompatible population definitions or make an unattainable travel-time distribution feasible.

If margins are uncertain, a clear research design is an outer control draw followed by an inner conditional-table draw. Preserve correlations and accounting identities in the outer model. Independent Gaussian perturbations of every ACS category followed by clipping and renormalization are not a justified joint uncertainty model. Rejection of infeasible control draws also changes their distribution and must be accounted for. Report conditional allocation variation separately from survey, source-processing, behavioral, route, attendance, occupancy, and emissions-factor uncertainty.

## 5. Sparse interface and commuting metrics

The proposed adapter contract is an ordered set of row and column identifiers; integer margins; explicit lower/upper bounds; allowed-edge metadata; positive activities; a target-law identifier; and provenance. Real adapters should preserve sparse edge lists and distinguish an absent record from a forbidden edge. The synthetic JSON uses small dense arrays to make every cell inspectable.

An output should identify the control realization, target law, method, random seed, and arithmetic precision. Exact small-instance samplers can report exact normalization and moments. MCMC implementations should report convergence evidence and Monte Carlo error separately from modeled uncertainty. Effective sample size for the output metric matters more than the number of matrix transitions.

For mode-specific one-way route distance `D[o,d,m]` in miles, attendance `A[o,d,m]` in commute workdays per year, legs per day `L[o,d,m]`, and vehicles attributable per worker `v[o,d,m]`, annual household-attributed commute VMT is

$$
V(X)=\sum_{o,d,m}X_{odm}D_{odm}A_{odm}L_{odm}v_{odm}.
$$

For a drive-alone category, `v = 1`; for a two-person carpool, `v = 1/2` under equal allocation of shared mileage. Taking an average occupancy and dividing all person-miles by it generally differs from summing occupancy-category person-miles divided by their own occupancies. Keep the convention explicit. Work-from-home entries have zero workplace-commute mileage in this calculation. A round-trip factor of two and a fixed annual workday count are assumptions, not information contained in LODES.

Transit, walking, and cycling contribute zero to **household automobile VMT**, but transit can contribute to a separate emissions metric with a passenger-mile factor. A generic emissions observable can be supplied as a mode-specific coefficient matrix with its own units, lifecycle boundary, source year, and attribution basis. Multiplying household automobile VMT by an automobile factor does not estimate transit emissions or a complete transport footprint.

**Commute VMT is one component of household travel.** It must not replace total household VMT, which also includes shopping, personal services, leisure, and other travel. Likewise, a change in modeled commute allocation is not automatically a causal effect of a housing or transportation policy. Resident-attributed and workplace-attributed summaries are alternative allocations of the same flows and should not be added together.

For any linear metric `g(X) = sum(q[i,j] * X[i,j])`, exact cell expectations give the mean, but the metric variance requires cell covariances or direct ensemble evaluation. Preserve complete table draws: resampling cells independently destroys their shared constraints and covariance. In general, nonlinear footprint calculations satisfy `E[f(X)] != f(E[X])`. Preserve paired control/factor draws when estimating differences between scenarios.

The reference tools support several distinct questions:

- For the range permitted by reconciled controls and hard bounds, use [certified linear optimization](linear-bounds.md); no allocation law is needed.
- For linear means and variances under ordinary conditional-worker independence, use [exact full-covariance moments](worker-baseline.md); neither sampling nor table enumeration is needed.
- For bounded, structurally constrained or interaction-weighted laws, use the exact small-fiber benchmark and [certified finite cycle comparisons](cycle-mixtures.md) to evaluate the chosen algorithm. The ordinary worker formula does not apply unchanged.
- If the variable-cell graph consists of cycles that share no edges, the [cactus sampler](cactus-sampler.md) counts and draws uniform tables through independent integer coordinates. This can handle enormous fibers without enumeration. Product-weight draws have separate, explicit work limits. Use this shortcut only when the justified support already has that structure; introducing hard zeros to make computation easier changes the model.

## 6. Public synthetic benchmark

[`examples/synthetic_commute.json`](../examples/synthetic_commute.json) describes ten fictional workers associated with one fictional home area and three workplace areas. Columns are drive alone, two-person carpool, transit, walk, and work from home. There are no real geocodes, employer records, client observations, or calibrated emission factors.

The row totals are `(4,3,3)` and mode totals are `(4,1,2,1,2)`. Far-area transit and mid/far walking are prohibited by explicit synthetic design. They are not inferred from missing routing data. Every other cell has a positive integer activity. The supplied feasible table is a witness, not an observed truth or preferred estimate.

Compare at least:

1. The exact uniform law on feasible aggregate tables.
2. The exact conditional-Poisson law using the activities and factorial weights.
3. A deterministic fractional IPF allocation, where defined, as a point-estimate baseline.
4. The minimum and maximum feasible value of the commute metric, which are law-independent sensitivity bounds.

The example fixes two commute legs per attending workday and 220 workdays per year. Those values are deliberately illustrative. Its two-person carpool column allocates half a vehicle's mileage per person; an odd count is allowed because the other rider may lie outside this home-area cohort. No real-world precision should be inferred from exact arithmetic on synthetic assumptions.

Independent exhaustive enumeration gives 42 feasible tables. Exact benchmark values are:

| Quantity | Annual commute vehicle miles |
| --- | ---: |
| Minimum over the feasible set | 9,460 |
| Uniform-table mean | 18,700 |
| Conditional-Poisson mean | `196016150 / 12131` (about 16,158) |
| Maximum over the feasible set | 25,080 |

The conditional-Poisson normalizing constant for the stated integer activities is `582288`. The difference in means comes entirely from the target law: margins, bounds, route distances, attendance, and occupancy conventions are identical. The extrema are sensitivity bounds, not a confidence interval.

## 7. Validation that addresses the intended use

Mathematical verification and model validation answer different questions.

* **Finite reference checks:** enumerate small feasible sets; verify every margin and bound; compare exact law normalization, cell expectations, metric moments, and sampler frequencies. Test zero margins, fixed cells, lower bounds, infeasibility, disconnected support, and supports requiring cycles longer than four.
* **Target-law checks:** exercise row/column scaling invariance and the `2 × 2` factorial contrast. Check detailed balance against the stated law. An invariant distribution does not by itself establish connectivity, convergence time, or practical efficiency.
* **Empirical reconstruction checks:** mask genuinely available public aggregate cells and compare reconstructed distributions with those released values. Hold out complete areas, periods, or characteristic groups to test transportability. Ensure a target is not recoverable from retained controls; otherwise the exercise tests arithmetic rather than prediction. This evaluates prediction of released aggregates, not unknown confidential counts.
* **Travel validation:** reserve independent mode/destination surveys or travel diaries where available. Use travel-time histograms as holdouts only if they were not used to fit the same model. Assess route coverage by the affected worker mass as well as edge counts. Include cross-boundary trips and within-area distances.
* **Decision-relevant metrics:** report bias and absolute error for flows and commute VMT; interval coverage and width where the assumed probability model supports a coverage claim; and calibration by scale, mode, sparsity, and source reliability. Compare with independence, IPF, a public-data prior, and the uniform reference. Matching calibration margins is not independent validation.
* **Computational evaluation:** compare time and memory per effective sample of commute VMT or another stated observable. Record initialization, rejected proposals, component structure, seeds, precision, and failure behavior. A polynomial theorem is not evidence that a practical run has mixed.

The first integration milestone should be an adapter tested entirely on public or synthetic inputs, with source-state labels and reproducible uncertainty outputs. Any production application then needs a reviewed source reconciliation, a chosen and tested target law, and independent checks of the downstream commuting or emissions quantities it is meant to inform.
