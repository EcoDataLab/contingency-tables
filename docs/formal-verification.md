# Formal verification of the #115 refinements

The formal work is additive to OpenAI's pinned #115 source. It now proves
sharper Poincare bounds for the unchanged original ideal chains and actual
parameterized ideal chains at both dense-compatible and smaller ideal-only scales,
with stationary success, uniform-output, finite-walk output-error, and
approximate-completion interface proofs. The dilated completion law now has
full finite-table counting, geometric acceptance, and bounded-retry accuracy
proofs. The new dense specialization supplies the accurate fine law and
all-state physical oracle. The encoded completion routine also has exact
output semantics and polynomial charged cost in supplied input. The both-branch
typed Boolean sampler now has pointwise feasible output and scheduled accuracy,
and its numeric schedule has polynomial charged cost. Concrete encoded outer-program identification,
complete sampler runtime, and secure Comparator verification remain open.

## Completed stage, 10 October 2026 UTC

The [completed stage aggregate](../formal/results/completion-aggregate-1236/verification.json) passed **1,236 focused plus six standalone named declaration audits (1,242 total)**. Its 583-module normal closure contains 582 authenticated reused modules and one fresh aggregate root; four fresh named-audit checks passed. The formerly separate 46 encoded-program, 193 physical-bridge, and 134 Boolean-law/schedule declarations are now integrated into the default focused target. This is ordinary Lean compilation and selected axiom auditing with reused dependency objects, not a fresh rebuild of every dependency or strict kernel replay. All selected axioms remain within `propext`, `Classical.choice`, and `Quot.sound`, or subsets.

The [compiled-environment audit](../formal/results/environment-aggregate-1236/README.md) passed: its explicit namespace/defining-module filters enumerated 22,710 declarations, including 16,549 theorem constants, and checked six complete headline dependency closures. These totals include pinned upstream and generated/private declarations. The full report, exact types, axioms, imported objects, and unchanged before/after input inventories are retained. This is ordinary compiled-environment inspection with trusted compiler/cache inputs, not strict Comparator replay. The [fresh Linux attempt at `cef573d`](../formal/results/linux-focused-cef573d-failure/README.md) compiled the core and passed all 1,236 named audits, then failed before the environment audit because an unused Lake library directory was absent. Its overall outcome remains failure. The reviewed inventory-runner repair is published at `df469a5`; a [fresh rerun](https://github.com/EcoDataLab/contingency-tables/actions/runs/38030825047) is in progress with unchanged proof sources.

The final [outer-sampler attempt](../research/outer-sampler/status.json) failed: 673 modules were reused, three failed, nine were dependency-blocked, and no new source compiled successfully in that attempt. `LatticeProfileStep` had passed the preceding normal attempt and was reused; the current failures are `LatticeProfileWalk`, `LatticeSamplerPreparation`, and `LatticeUnitStep`. All 13 attempted outer-sampler sources and diagnostics are frozen under [research/outer-sampler](../research/outer-sampler/) outside the default formal target. No complete literal outer sampler or full machine runtime is verified.

The [runtime-degree archive](../research/runtime-degree/) retains passed TreeDegree diagnostics, a failed PolynomialCompilerDegree diagnostic, and uncompiled fresh-bit/finite-word proposals. The numerical complete runtime exponent is unknown. The [Comparator serial archive](../research/comparator-serial/) retains 33 offline orchestration tests and 16 planner tests, without a real Linux runtime result for that route. The [strict VM attempt](../formal/results/strict-comparator-vm-895b45c/README.md) passed ABI-11 sandbox preflight but exhausted memory before comparison; it produced no candidate export or kernel result.

Use the [contributor handoff](handoff.md) for reproduction and ordered next-round obligations. Reviewed application evidence includes the [mature worker-library benchmark](worker-library-benchmarks.md), [public commuting backtest](commuting-backtest.md), and [source-level composed complexity review](composed-complexity.md). These measure a classical law, describe a public job-table case frame, and retain a symbolic uncompiled cost proposal, respectively; none verifies a complete universal sampler.

Review provenance: the independent source reviews are separate AI-agent reviews within this project. Human MCMC and Lean review is welcome; ordinary compiler outcomes, mathematical review, and strict kernel replay are distinct evidence.

## Historical component evidence

The [Boolean codec/retry module](completion-boolean-program.md)
passed 25 declaration audits and six native Lean evaluations after checkpoint
8. Its [receipt](../formal/results/completion-boolean-retry/verification.json)
and frozen-source review retain their isolated scope. Its 25 declarations
are now included in the focused aggregate; the historical checkpoint-8 Linux
result still covers 632 declarations at its recorded commit.

The subsequent [binary-list decoder](completion-list-decoder.md) passed
52 declaration audits and nine native boundary checks. It proves exact
agreement with the typed table trial and polynomial TreeTyped work and
output weight in the binary input size. Its [receipt](../formal/results/lattice-decoder/verification.json)
and independent frozen-source review retain their isolated scope. Its 52
declarations are now included in the focused aggregate. No whole-sampler
runtime claim follows.

The [explicit schedule arithmetic](completion-schedules.md) contributes two
modules with 24+32 standard-axiom audits and clean actual-source compilations.
They bound all four scalar errors and the full reserved random-bit bank.
The [receipt](../formal/results/completion-schedules/verification.json)
does not cover the separate physical wrappers or the final outer program.
These 56 declarations are now included in the focused aggregate. Their
original receipt does not certify later wrappers or expand the Linux scope.

The [input-size proofs](completion-input-size.md) contribute two modules
with 25+7 standard-axiom audits and empty successful compile logs. They connect
binary margins and the reserved bank to the original public sampling-size
measure, with numeric precision `h`, and provide generic cost composition for
a supplied deterministic polynomial-time realizer. Equal totals are explicit
in the literal public-input bound. The [receipt](../formal/results/completion-input-size/verification.json)
and independent frozen-source review cover these 32 declarations. The complete
sampler and random-machine cost composition remain separate. These 32
declarations are now included in the focused aggregate; the historical
Linux scope remains unchanged.

The [dense completion family](completion-dense-law.md) contributes three
modules with 25+3+38 standard-axiom audits. Actual native Windows compilations
and independent review cover the canonical Boolean-word law, exact pinned
analytic premise discharge, all-state residual inputs and completion accuracy,
the normalized outer finite-law bound at `K=80000d¹⁷`, and common reserved
word widths. The [receipt](../formal/results/completion-dense-law/verification.json)
retains exact source, object, dependency and audit hashes. Four style/unused
variable warnings remain in the compile logs; all named audit logs contain
only axiom reports. The final encoded walker and public-machine cost are
not yet verified. These 66 declarations are now included in the focused
aggregate; the historical Linux scope remains unchanged.

The [encoded completion program](completion-sampler-program.md) originally added two
isolated modules with 32+14 standard-axiom audits. Their actual compiled
list routine combines computed dense inputs and draws, signed decoding,
bounded retries and a computed greedy fallback. Whole-word and prefix
identities establish the actual output law, including fallback error, under
the proved completion hypotheses. Its polynomial charged-cost proof includes
execution and output weight in the full input with supplied Boolean bits;
it evaluates all reserved trials before selecting the first success.
The [receipt](../formal/results/completion-program/verification.json) preserves
source, object, dependency and audit hashes. The physical list-order bridge
is covered by the subsequent checkpoint below; outer-program and public
random-machine composition remain separate. These
46 declarations are now integrated into the completed stage aggregate. Their original isolated receipt retains its exact scope and does not expand the historical Linux result.

The [computed physical bridges](completion-physical-bridges.md) originally added seven
isolated modules with `24+2+6+69+21+32+39=193` standard-axiom audits.
They verify computed physical proposals, actual large-list ordering and
all-state completion accuracy, reference-walk and explicit finite-law schedule
specializations, and unique empty-block reconstruction. Adaptive dense
parameters remain supplied under explicit conditions. The
[receipt](../formal/results/completion-physical-bridges/verification.json)
binds seven exact sources, seven delivered objects, raw compiler and audit
logs, and the authenticated 564-module dependency closure. Six objects were
reused with verified hashes; `ListedLatticeCompletion` was freshly compiled
with one retained style warning. Earlier fresh predecessor receipts for
`AdaptiveDenseCompletion` and `CompletionRandomBudget` attest log hashes;
those earlier logs were not delivered. At this historical checkpoint, the 193 names were disjoint from the 869 aggregate and isolated 46. All are now integrated into the completed stage aggregate. Neither the complete Boolean walker nor
its public-machine runtime is certified by this scope.

The [both-branch Boolean law and computed schedule](completion-boolean-schedule.md)
originally added three isolated modules with `16+105+13=134` standard-axiom audits.
`PhysicalReferenceBoolean` identifies the typed reference-branch word experiment;
`LatticeScheduleProgram` computes the actual numeric schedule and reservations
with polynomial charged cost; `PhysicalBooleanSampler` supplies automatic
branches, greedy fallback and initialization, pointwise feasible output, and
scheduled `2^-h` accuracy for every equal-total natural margin pair and natural
`h`. Zero margins and empty index types are included. This final typed law is
noncomputable; the literal encoded walker and public machine remain unverified.
The [receipt](../formal/results/completion-boolean-schedule/verification.json)
binds all three fresh native Windows compilations, authenticated reused
imports, exact ordered audits, and complete before/expected/after input maps.
The logs retain nine warnings. The surrounding batches failed, and no failed
or blocked module is included in the claimed result. These 134 names were disjoint from the historical 869 aggregate and separate 46+193 audits and are now integrated into the completed stage aggregate. Their component receipt adds no fresh Linux or strict Comparator result and no complete machine-time degree.

## Reproduction

From the repository root, with Git, curl, Python 3, and a C toolchain installed:

```sh
scripts/bootstrap_lean.sh
scripts/verify_lean.sh focused
```

The bootstrap script installs Elan and Lean under `.tools/`, downloads a sparse
upstream checkout under `.upstream/`, and puts build artifacts under
`formal/.lake/`. It does not change the user's shell profile or default Lean
installation. The original upstream `lakefile.lean`, `lake-manifest.json`,
`lean-toolchain`, and proof files remain unchanged. The first run needs several
GiB of disk space: some unchanged upstream modules import all of Mathlib.

The focused package retains exactly the original Lean version and mathlib
dependency revisions:

| Component | Pin |
|---|---|
| OpenAI source | `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` |
| Lean | `leanprover/lean4:v4.34.1` |
| mathlib | `d13f23b723b8a846827a245b89c10fc7d3f11612` |
| Elan installer | `v4.2.4`, platform archive SHA-256 checked |

[`formal/results/provenance.json`](../formal/results/provenance.json) records
the pinned original source modules, their Git blob IDs and SHA-256 hashes, and
the original build-file hashes. The checkpoint-specific closure counts are
reported below.
[`formal/lake-manifest.json`](../formal/lake-manifest.json) contains the relevant
dependency entries from the original manifest. We do not run `lake update`.
The separate harness avoids the original package configuration's eager cloning
and compatibility patching of unrelated manuscript dependencies.

## New statements

[`QuadraticCoefficient.lean`](../formal/Math115/QuadraticCoefficient.lean)
formalizes the elementary sharp inequality

$$
a(M-a)\le M^2/4,
$$

including equality precisely at `a = M/2` for real `a,M`.

[`TransportRefinement.lean`](../formal/Math115/TransportRefinement.lean) applies
it to the actual upstream `weightedFuture`, `correctionKernel`, and recursive
transport definitions. The original potential coefficient

$$
1/s+1/t+2(W+1)^2c/(st)
$$

becomes

$$
1/s+1/t+(W+1)^2c/(2st).
$$

This divides the auxiliary-defect contribution by four. It does **not** divide
the entire bound by four; the endpoint terms remain. The theorem
`integer_root_leaf_transport_quarter` also retains `leafEnergySum` in place of
the larger `integerGraphEnergy`. Its graph-energy corollary preserves the
original interface with the sharper coefficient.

These statements use the same positivity, signature, width, and root-balance
hypotheses as the original transport theorem. They introduce no new axioms or
admissions. The physical exposure and ideal-chain integrations below now transfer this
refinement through the actual contexts. The complete finite-bit sampler at the
new scales remains separate.

[`WidthWeightedTransport.lean`](../formal/Math115/WidthWeightedTransport.lean)
retains each slot's actual coefficient `(U + 1)^2/4` before summing auxiliary
masses. Its root and leaf-energy statements require no shared upper width `W`;
the original lower-width, positivity, and signature hypotheses remain. This
can be sharper for heterogeneous widths. It does not establish those
hypotheses for arbitrary capped-table or weighted models.

[`RepairCoefficient.lean`](../formal/Math115/RepairCoefficient.lean) checks the
subsequent scalar step independently: if `c ≤ Q max(s,t)` and `s,t > 0`, then

$$
\min(s,t)\bigl(1/s+1/t+2c/(st)\bigr)\le 2+2Q.
$$

The quarter-bound specialization yields `2 + d(U+1)^2/2` under the original
repair-mass premise `c ≤ d max(s,t)`, versus the original
`2 + 2d(U+1)^2`. It does not prove that premise for a new physical model.

[`GlobalDisplayOwnership.lean`](../formal/Math115/GlobalDisplayOwnership.lean)
proves that an unordered exchange edge identifies the full display and then its
unique overfull slot, adjacent level, and fixed-order prefix. Slot widths may
differ and may be zero. Maximum recovery itself is already in the upstream
proof; the new theorem allows the special slot and prefix to vary globally.
The abstraction uses the same pointwise unit-removal operation. The physical
bridge below now supplies the actual context mapping.

[`SmallEntrySwitching.lean`](../formal/Math115/SmallEntrySwitching.lean) counts
actual four-cycle incidences, using a recoverable injection and the original
table margin equations. [`SmallEntryTail.lean`](../formal/Math115/SmallEntryTail.lean)
builds actual shifted-fiber bijections and proves the strong linear tail,
finite-product survival bound, and mean bound. The supporting finite-sum and
survival algebra modules contain the remaining arithmetic steps. See the
[formal statement guide](small-entry-formalization.md) for hypotheses,
zero cases, and exact exports.

[`ScaleCertificate.lean`](../formal/Math115/ScaleCertificate.lean) discharges
the generic scale arithmetic. [`PaddedMarginBridge.lean`](../formal/Math115/PaddedMarginBridge.lean)
connects it to actual enlarged margins, marked-cell counts, a finite union
bound, and the successful-padding bijection. Both `U=64d⁵` and the explicit
shape-aware threshold yield enlarged-table count at most twice the original
count under their stated margin hypotheses. The [scale guide](scale-formalization.md)
separates these actual-table conclusions from generic arithmetic interfaces.

[`PhysicalLeafEnergy.lean`](../formal/Math115/PhysicalLeafEnergy.lean) retains
literal leaf edges through the actual physical embedding and the hard-weight
limit. It uses the boxed auxiliary kernel required by the source repair
injection, handles zero-child contrasts, proves unique ownership across
prefixes, and sums all adjacent contrasts with coefficient
`2+(p−1)(U+1)²/2` against physical energy. This is the continuous quarter
coefficient; it does not claim the additional discrete-floor refinement.
The [physical integration note](physical-transport-integration.md) records the
exact interfaces. Exposure, the original repair extension, and ideal-chain
comparison are now checked in the additional modules below.

[`PaddingGrowth.lean`](../formal/Math115/PaddingGrowth.lean) and
[`PaddingGrowthAlgebra.lean`](../formal/Math115/PaddingGrowthAlgebra.lean)
strengthen the padding result by iterating actual ordinary-fiber count ratios.
They verify `U=47d⁵`, a shape-dependent threshold, and the zero-donor case.
The earlier `U=64d⁵` certificate remains valid. See the
[sequential-padding proof](sequential-padding.md).

[`PathVariance.lean`](../formal/Math115/PathVariance.lean), with
[`PathDistanceSum.lean`](../formal/Math115/PathDistanceSum.lean), proves the
weighted path-variance coefficient `U(U+1)/2` and its sharper mode-dependent
form. The actual child-weight wrappers use the source's global minimum
property, which retains the required interval support and handles zero weights.
[`PhysicalExposureVariance.lean`](../formal/Math115/PhysicalExposureVariance.lean)
combines this with the globally owned physical leaf energies.
[`PhysicalFullVariance.lean`](../formal/Math115/PhysicalFullVariance.lean)
then uses the unchanged source repair extension and positive-support encoding.
For `p` small cells, the resulting actual-state coefficient is

$$
K_{p,U}=(1+2p^2)\frac{U(U+1)}2
\left(2+\frac{(p-1)_+(U+1)^2}{2}\right)+2.
$$

The [path proof](path-variance-formalization.md) and
[physical exposure integration](physical-exposure-integration.md) give the
precise hypotheses and exports.

[`CompletionAdjustment.lean`](../formal/Math115/CompletionAdjustment.lean)
checks the actual source exchange and repair translations: entry magnitude at
most one, support at most three, and negative support at most two, including
reverse repairs and the singleton/empty cases.
[`ReferenceEdgeAcceptance.lean`](../formal/Math115/ReferenceEdgeAcceptance.lean)
uses the ordinary-table small-entry theorem to prove actual half acceptance for
free padding `L ≥ 3e`, where `e` is the product of the numbers of nonreference
large rows and columns. This includes the singleton `L=e=0` case. See the
[adjustment](completion-adjustment-formalization.md) and
[acceptance](reference-edge-acceptance.md) notes.

[`SmallChainGap.lean`](../formal/Math115/SmallChainGap.lean) and
[`AllSmallChainGap.lean`](../formal/Math115/AllSmallChainGap.lean) preserve the
literal source chain definitions at `U=d²⁰`, `L=d¹²`. They prove exact
coefficients `2K/β` and `K/β`, respectively, and the conservative bounds
`1024d⁸⁵` for `paperSmallChain` and `512d⁸⁵` for `unitSmallChain`.
The [original-chain comparison](small-chain-gap.md) distinguishes these bounds
from the source's displayed `d¹⁶⁰` allowance and its unweakened intermediate
calculation.

[`ReducedSmallChain.lean`](../formal/Math115/ReducedSmallChain.lean) constructs
an actual ideal completion chain with free `U,L`, the source physical graph,
its stationary completion weights, and the proved acceptance comparison.
For `U ≥ 2`, `L ≥ 3d`, it proves `1024d⁵U⁴`; at `U=47d⁵`, `L=32d³`, this gives
`1024·47⁴d²⁵`. The theorem explicitly assumes a nonempty positive-weight state
space and a chosen large reference row and column. It does not cover the
missing-reference branch or discharge nonemptiness from equal total margins.
The [reduced-chain guide](reduced-small-chain.md) separates this checked
ideal-chain result from finite-bit oracle implementation and end-to-end sampler
runtime.

[`ReducedAllSmallChain.lean`](../formal/Math115/ReducedAllSmallChain.lean)
constructs the unit branch at free scales and selects between reference and
unit chains automatically. [`PhysicalStateNonempty.lean`](../formal/Math115/PhysicalStateNonempty.lean)
builds a positive physical state from equal ordinary totals at arbitrary
`U,L`, including zero margins and empty index types. Their final wrappers
remove the two external assumptions described in the older module above.

[`RepairVarianceRefinement.lean`](../formal/Math115/RepairVarianceRefinement.lean)
proves the abstract defect-side square-root inequality.
[`PhysicalRepairRefinement.lean`](../formal/Math115/PhysicalRepairRefinement.lean)
applies it to the unchanged actual repair map, label encoding, weight
domination, and graph energy, yielding

$$
K'_{p,U}=C_T+(\sqrt{p^2 C_T}+1)^2
\le d^3U^4,
\qquad C_T=\frac{U(U+1)}2\left(2+\frac{(p-1)_+(U+1)^2}{2}\right).
$$

The polynomial inequality assumes `d≥11`, `U≥2`, and `p≤d`; the source
dimension allowance is always at least 11. Actual chain comparison gives
`128d⁵U⁴` for the reference/selected chain and `64d⁵U⁴` for the unit branch.
The eightfold improvement in these conservative polynomial bounds combines
the exact repair refinement with tighter polynomial estimates.

[`IdealOracleScales.lean`](../formal/Math115/IdealOracleScales.lean) constructs
actual ideal chains at `U=5d³,L=3d`, proves the corresponding ordinary padding
count ratio, and shows the retained dense interface forces `L≥32d³`.
[`IdealRepairRefinement.lean`](../formal/Math115/IdealRepairRefinement.lean)
then specializes the sharper chain bound to `80,000d¹⁷` (unit: `40,000d¹⁷`).
[`ReducedRepairRefinement.lean`](../formal/Math115/ReducedRepairRefinement.lean)
supplies the dense-compatible `128·47⁴d²⁵` bound (unit: `64·47⁴d²⁵`).
Both include final automatic wrappers requiring only equal ordinary totals.
Neither is a finite-bit completion or outer sampler theorem.

[`PhysicalStationaryMass.lean`](../formal/Math115/PhysicalStationaryMass.lean)
keeps the actual completion multiplicities and proves `Z≤(1+p²)P` for the
physical normalizer, arbitrary cutoff and padding, and ordinary padded-table
count `P`. Equal ordinary total margins supply positive normalization for the
probability statements.
[`PhysicalStationarySuccess.lean`](../formal/Math115/PhysicalStationarySuccess.lean)
constructs a bijection between original tables and successful actual
state/completion pairs. Success requires both a balanced state and sufficient
large-cell entries to unpad; all completions remain in the joint space.
[`PhysicalStationaryLaw.lean`](../formal/Math115/PhysicalStationaryLaw.lean)
identifies its rational state law with the selected chain's actual stationary
law, proves the dependent joint law uniform, and gives table mass `1/Z` and
total success `N/Z`. At `U=5d³,L=3d`, success is at least `1/[2(1+p²)]`.
Independent stationary retries have an exact uniform/fallback mixture and
total variation error at most `exp(−n/[2(1+p²)])`. The
[stationary-output guide](physical-stationary-success.md) gives the scope and
named interfaces; none of these statements assumes a finite walk has already
reached stationarity.

[`PhysicalRationalKernel.lean`](../formal/Math115/PhysicalRationalKernel.lean)
defines exact rational reference, unit, and selected transition laws and
identifies their real casts with the actual chain, including diagonal holds.
[`PhysicalFiniteWalk.lean`](../formal/Math115/PhysicalFiniteWalk.lean)
proves a minimum stationary mass using positive integer completion weights
and `B=(M+dL+U+3)^(2d)`, where `M` is the total row margin. It combines the
actual finite-walk mixing bound with a fresh conditional uniform terminal
completion and independent restarted retries. At the ideal scales, the
output TV error is at most `exp(−R/S)+RB exp(−T/K)`, with
`S=2(1+p²)` and `K=80,000d¹⁷`. Explicit real-log sufficient inequalities
give any positive target error. These noncomputable finite laws retain a
supplied feasible fallback and make no operational completion or machine-cost
claim. The [finite-walk guide](physical-finite-walk.md) and
[source review](../formal/results/finite-walk-review.json) record the interfaces.

[`PhysicalCompletionOracle.lean`](../formal/Math115/PhysicalCompletionOracle.lean)
identifies the literal dyadic proposal, ordinary completion draw, and signed
translation test with the exact rational kernel. Holding proposals incur
no completion error, giving a transition TV bound `β deg(x) ζ` and its
uniform allowance `γζ`, with `γ=(5d²+1)β≤1/2`. It also transports terminal
completion laws through the actual reference-fibre equivalence, preserving
TV, and proves the empty branch's fibre has cardinality one.
[`PhysicalApproximateOracle.lean`](../formal/Math115/PhysicalApproximateOracle.lean)
then proves an added output error `R(Tδ+η)` for uniform all-state transition
and conditional-terminal errors. Its actual oracle specialization gives
`R(Tγζstep+ζterminal)`, retaining fresh conditional draws and independent
restarts. The [guide](physical-approximate-oracle.md),
[37-declaration receipt](../formal/results/approximate-oracle/verification.json),
and [source review](../formal/results/approximate-oracle-review.json) specify
the exact accuracy contract; no efficient oracle is assumed constructed.

[`LatticeCompletion.lean`](../formal/Math115/LatticeCompletion.lean)
proves the signed integer prefix/difference inverses, exact encode/decode
identities with Euclidean division, boundary-dependent margin formulas,
entry positivity, and `k^((a−1)(b−1))` cardinality of the constructed finite
digit image. Its [44-declaration receipt](../formal/results/lattice-completion/verification.json)
covers that core. The new
[`LatticeCompletionFinite.lean`](../formal/Math115/LatticeCompletionFinite.lean)
supplies restriction/extension, full accepted-fiber surjectivity, and the
actual finite-table equivalence for all dimensions and positive dilation.
Equivalence with the Python implementation remains separate.

[`DilatedCompletionMargins.lean`](../formal/Math115/DilatedCompletionMargins.lean)
retains the actual block's full padding multiplicities: `R_i≥bL`, `P_j≥aL`,
and `H≤M+abL`. It defines fine margins on the same reference-table index
types and derives equal total `d¹²(H+2ab)`, nonemptiness, and the original
dense sampler's `d¹²` minimum-margin threshold.

Nine new modules in the [completion formalization](completion-oracle-formalization.md)
close the finite-table and geometric obligations. Actual prefix-cell covers,
constructed real margin monotonicity, and scalar volume give the full fine
count bound. An exact analytic constant then proves quarter acceptance.
[`LatticeCompletionAccuracy.lean`](../formal/Math115/LatticeCompletionAccuracy.lean)
combines these results with the actual decoder's independent retry law.
At `k=d¹²`, equal totals, the strong margins, a dimension bound, and a
feasible fallback suffice; its approximation premise concerns the whole
fine-table law. The subsequent [dense specialization](completion-dense-law.md)
discharges that premise and assembles all-state physical laws. Concrete
encoded outer-program realization and complete cost remain open.

## Verification levels

- `standalone` compiles the sharp coefficient, repaired scalar bound, and global ownership abstraction
  without importing the large upstream proof tree, then checks their axioms.
- `focused` compiles the unchanged upstream leaf-energy and root-transport
  modules, then all refinements imported by `Math115`, and checks their printed transitive axiom
  dependencies against `propext`, `Classical.choice`, and `Quot.sound`. It then
  requires the compiled-environment inventory and all six headline dependency
  closures to pass the same axiom policy and frozen-input checks. Named-audit
  success alone does not complete this expanded scope.
- `full` compiles the unchanged `UnconditionalMain` and Comparator challenge
  modules (a much larger dependency closure), then audits the three original
  exported sampling/counting theorems. This is Lean compilation and an axiom
  audit, not a Comparator pass.
- `comparator` uses the original challenge JSON and requires actual Comparator,
  Landrun, and lean4export installations. Use a fresh supported Linux
  environment and the sandbox invocation in the
  [official Comparator instructions](https://github.com/leanprover/comparator).
  The development `fake-landrun` script is not a substitute for that guarantee.

The local development host is macOS arm64. The official Comparator sandbox
depends on Linux Landrun; no secure Comparator success is claimed on this host.
The focused harness trusts the downloaded official Mathlib cache, as allowed by
the upstream Comparator instructions. Independent kernel replay would be an
additional verification level.

## Recorded outcome

The [completed stage aggregate](../formal/results/completion-aggregate-1236/verification.json) passed **1,236 focused plus six standalone named declaration audits (1,242 total)**. Its 583-module normal closure contains 582 authenticated reused modules and one fresh aggregate root; four fresh named-audit checks passed. The formerly separate 46 encoded-program, 193 physical-bridge, and 134 Boolean-law/schedule declarations are now integrated into the default focused target. This is ordinary Lean compilation and selected axiom auditing with reused dependency objects, not a fresh rebuild of every dependency or strict kernel replay. All selected axioms remain within `propext`, `Classical.choice`, and `Quot.sound`, or subsets.

See the current stage summary above for the [compiled-environment evidence](../formal/results/environment-aggregate-1236/README.md) and the fresh Linux run. Historical component receipts below retain their exact earlier scopes.

The [historical completion aggregate receipt](../formal/results/completion-aggregate/verification.json) records its earlier root compilation, exact focused and standalone audit drivers, raw audit logs, source/object hashes, and verification scope. The focused driver selects 863 unique names; the six unchanged standalone names are disjoint. The nine additions contribute `25+52+24+32+25+7+25+3+38=231` declarations. This is a successful scoped aggregate compilation and audit, not a success claim for the surrounding native build: its overall watcher exited with failure because a separate draft failed. Their original isolated receipts remain the evidence for native examples and component-specific checks; those checks were not rerun by the aggregate audit.

The historical eighth local checkpoint passed on 9 October 2026 UTC with Lean 4.34.1.
New modules were compiled serially, followed by a fresh aggregate
`Math115.lean` compilation and fresh focused and standalone axiom audits.
Those integrated checks use existing compiled dependency outputs. This is
**not a fresh build of the complete dependency closure**.

| Check | Outcome | Evidence |
|---|---|---|
| Completed stage aggregate | 1,236 focused plus six standalone named audits passed; 582 authenticated normal object reuses and one fresh root; four fresh named-audit checks | [Stage receipt](../formal/results/completion-aggregate-1236/verification.json) |
| Environment-derived inventory | Passed on the frozen native aggregate; complete selected theorem inventory and six headline closures; trusted compiler/cache boundary | [Complete report and receipt](../formal/results/environment-aggregate-1236/README.md) |
| Fresh Linux stage reproduction | `cef573d` passed the normal build and 1,236 named audits, but failed before the environment audit; reviewed runner fix at `df469a5` is being checked in a fresh run | [Failure receipt](../formal/results/linux-focused-cef573d-failure/README.md), [rerun](https://github.com/EcoDataLab/contingency-tables/actions/runs/38030825047) |
| Historical completion-aggregate Linux build | Fresh focused project build and all 863 focused audits passed at `895b45c`; 111 recorded source hashes match that commit; excludes standalone and isolated audits | [Successful run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37991819113) and [receipt](../formal/results/linux-focused-895b45c/verification.json) |
| Checkpoint 8 aggregate | `Math115.lean` compiled; both axiom audits passed | [Eighth-checkpoint log](../formal/results/eighth-checkpoint.log) |
| Checkpoint 8 dependency inventory | 228 source modules: 178 unchanged upstream and 50 local; 50 trusted external import entries | [Verification scope](../formal/results/verification.json) and [source provenance](../formal/results/provenance.json) |
| Checkpoint 8 focused audit | 632 selected declarations passed | [Eighth-checkpoint log](../formal/results/eighth-checkpoint.log) |
| Checkpoint 8 standalone audit | Six selected declarations passed | [Eighth-checkpoint log](../formal/results/eighth-checkpoint.log) |
| Independent checkpoint 8 Linux build | Fresh focused build and all 632 focused audits passed at `0aa5a61`; 73 recorded source hashes match that commit | [Successful run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37963647335) and [receipt](../formal/results/linux-focused-0aa5a61/verification.json) |
| Independent checkpoint 7 Linux build | Fresh focused build and all 420 focused audits passed at `5b37032`; excludes checkpoint 8 | [Successful run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37932487805) and [receipt](../formal/results/linux-focused-5b37032/verification.json) |
| Checkpoint 7 aggregate | `Math115.lean` compiled; both axiom audits passed | [Seventh-checkpoint log](../formal/results/seventh-checkpoint.log) |
| Checkpoint 7 dependency inventory | 219 source modules: 178 unchanged upstream and 41 local; 47 trusted external import entries | [Historical source provenance](https://github.com/EcoDataLab/contingency-tables/blob/5b3703234e7f6cd88e6b6f6b3dab85510ba4366f/formal/results/provenance.json) |
| Checkpoint 7 focused audit | 420 selected declarations passed | [Seventh-checkpoint log](../formal/results/seventh-checkpoint.log) |
| Checkpoint 7 standalone audit | Six selected declarations passed | [Seventh-checkpoint log](../formal/results/seventh-checkpoint.log) |
| Independent checkpoint 6 Linux build | Fresh focused build and all 318 focused audits passed at `e5d5dd3`; excludes subsequent oracle additions | [Successful run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37927276465) and [receipt](../formal/results/linux-focused-e5d5dd3/verification.json) |
| Checkpoint 6 aggregate | `Math115.lean` compiled; both axiom audits passed | [Sixth-checkpoint log](../formal/results/sixth-checkpoint.log) |
| Checkpoint 6 dependency inventory | 212 source modules: 175 unchanged upstream and 37 local; 45 trusted external import entries | [Historical source provenance](https://github.com/EcoDataLab/contingency-tables/blob/e5d5dd3e81b5eac0e3f42841530286b56bcb96e5/formal/results/provenance.json) |
| Checkpoint 6 focused audit | 318 selected declarations passed | [Sixth-checkpoint log](../formal/results/sixth-checkpoint.log) |
| Checkpoint 6 standalone audit | Six selected declarations passed | [Sixth-checkpoint log](../formal/results/sixth-checkpoint.log) |
| Checkpoint 5 aggregate | `Math115.lean` compiled; both axiom audits passed | [Fifth-checkpoint log](../formal/results/fifth-checkpoint.log) |
| Checkpoint 5 dependency inventory | 207 source modules: 172 unchanged upstream and 35 local; 45 trusted external import entries | [Historical source provenance](https://github.com/EcoDataLab/contingency-tables/blob/7ad5c81117bbaa869da751b1f92a9213ddefdd22/formal/results/provenance.json) |
| Checkpoint 5 focused audit | 279 selected declarations passed | [Fifth-checkpoint log](../formal/results/fifth-checkpoint.log) |
| Checkpoint 5 standalone audit | Six selected declarations passed | [Fifth-checkpoint log](../formal/results/fifth-checkpoint.log) |
| Independent checkpoint 5 Linux build | Fresh focused build and all 279 focused audits passed at `7ad5c81`; excludes the finite-walk additions | [Successful run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37924611391) and [receipt](../formal/results/linux-focused-7ad5c81/verification.json) |
| Checkpoint 4, historical local result | Aggregate and 232 audits passed, using the then-current dependencies | [Fourth-checkpoint log](../formal/results/fourth-checkpoint.log) |
| Independent checkpoint 4 Linux build | Fresh focused build and all 226 focused audits passed at `d2e8b0b`; excludes the stationary-output additions | [Successful run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37890362781) and [receipt](../formal/results/linux-focused-d2e8b0b/verification.json) |
| Checkpoint 3, historical local result | Aggregate and 154 audits passed, using the then-current dependencies | [Historical third-checkpoint log](../formal/results/third-checkpoint.log) |
| Checkpoint 2, historical local result | 86 upstream modules in its import closure; 62 focused and six standalone audited declarations | [Historical focused log](../formal/results/focused.log) and [standalone log](../formal/results/standalone.log) |
| Earlier focused Linux run | Passed at `5e5d6ef`; excludes subsequent local additions | [Run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847572556) |
| Full original Linux build and audit | **Passed** at `5e5d6ef`: unchanged `UnconditionalMain`/challenge closure and all three original exported sampling/counting theorem audits | [Successful run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847944509) and [Linux receipts](../formal/results/linux-runs.json) |
| Earlier native Windows run | At `b14082b`: 128 Python tests, 100 freshly compiled source modules, and 68 audited declarations | [Native Windows verification](windows-verification.md) and [receipt](../formal/results/thor-verification.json) |
| Strict Comparator | Not passed: historical hosted ABI preflight failure; newer VM passed ABI-11 strict preflight but exhausted memory before comparison | [Hosted preflight](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847722684) and [VM failure receipt](../formal/results/strict-comparator-vm-895b45c/README.md) |

The historical checkpoint 8 total is **638 selected declarations: 632 focused plus six
standalone, comprising 636 new declarations and two original baseline
declarations**. All use only the standard allowed axioms `propext`,
`Classical.choice`, and `Quot.sound`, or subsets.

[`verification.json`](../formal/results/verification.json) records the exact
selected declarations, axioms, source hashes, and verification scope.
Historical checkpoint-8 compilation and audits are retained in
`eighth-checkpoint.log`; the earlier expanded aggregate has its historical
[receipt](../formal/results/completion-aggregate/verification.json), and the completed stage has a separate [current receipt](../formal/results/completion-aggregate-1236/verification.json). The source pin and unchanged upstream files
are recorded in provenance, and the focused manifest retains the original
revision entries. The separate successful original-theorem Linux run audits
three original sampling/counting exports at its own recorded commit. It is
neither a Comparator pass nor a Linux verification of later refinements. The
separate checkpoint-8 focused Linux run covers its exact recorded sources;
its 73 environment-recorded source hashes were checked against `0aa5a61`.

This checkpoint verifies ideal-chain variance bounds, ordinary-table padding,
automatic branch selection, physical feasibility, and the actual stationary
physical success/output law, together with a matching finite-walk law and
output-error bound at the new scales. The new modules identify the finite
proposal/draw/test law, propagate approximate-completion errors, and verify
integer codec algebra and actual fine-input margin bounds. The eighth
checkpoint adds the full finite accepted-table equivalence, geometric
count comparison, quarter acceptance, and actual bounded-retry completion
accuracy conditional on fine-law accuracy. The separate 66-declaration dense
completion receipt now instantiates the canonical dense law and every physical
oracle. The subsequent 46-declaration encoded completion receipt identifies
the list program with that completion law and proves its polynomial charged
cost for supplied input. The subsequent 193-declaration physical-bridge receipt
connects actual list ordering and computed proposals to the physical laws.
These receipts do not yet prove the
complete encoded outer program or its machine runtime. Official Mathlib cache
artifacts and Lean bootstrap binaries remain trusted.
