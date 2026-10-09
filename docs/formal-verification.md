# Formal verification of the #115 refinements

The formal work is additive to OpenAI's pinned #115 source. It now proves
sharper Poincare bounds for the unchanged original ideal chains and an actual
parameterized ideal chains at both dense-compatible and smaller ideal-only scales. Finite-bit sampler runtime and secure Comparator
verification remain separate from these results.

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

## Verification levels

- `standalone` compiles the sharp coefficient, repaired scalar bound, and global ownership abstraction
  without importing the large upstream proof tree, then checks their axioms.
- `focused` compiles the unchanged upstream leaf-energy and root-transport
  modules, then all refinements imported by `Math115`, and checks their printed transitive axiom
  dependencies against `propext`, `Classical.choice`, and `Quot.sound`.
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

The fourth local checkpoint passed on 9 October 2026 UTC with Lean 4.34.1.
New modules were compiled serially, followed by a fresh aggregate
`Math115.lean` compilation and fresh focused and standalone axiom audits.
Those integrated checks use existing compiled dependency outputs. This is
**not a fresh build of the complete dependency closure**.

| Check | Outcome | Evidence |
|---|---|---|
| Checkpoint 4 aggregate | `Math115.lean` compiled; both axiom audits passed | [Fourth-checkpoint log](../formal/results/fourth-checkpoint.log) |
| Checkpoint 4 dependency inventory | 200 source modules: 168 unchanged upstream and 32 local; 43 trusted external import entries | [Verification scope](../formal/results/verification.json) and [source provenance](../formal/results/provenance.json) |
| Checkpoint 4 focused audit | 226 selected declarations passed | [Fourth-checkpoint log](../formal/results/fourth-checkpoint.log) |
| Checkpoint 4 standalone audit | Six selected declarations passed | [Fourth-checkpoint log](../formal/results/fourth-checkpoint.log) |
| Checkpoint 3, historical local result | Aggregate and 154 audits passed, using the then-current dependencies | [Historical third-checkpoint log](../formal/results/third-checkpoint.log) |
| Checkpoint 2, historical local result | 86 upstream modules in its import closure; 62 focused and six standalone audited declarations | [Historical focused log](../formal/results/focused.log) and [standalone log](../formal/results/standalone.log) |
| Earlier focused Linux run | Passed at `5e5d6ef`; excludes subsequent local additions | [Run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847572556) |
| Full original Linux build and audit | **Passed** at `5e5d6ef`: unchanged `UnconditionalMain`/challenge closure and all three original exported sampling/counting theorem audits | [Successful run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847944509) and [Linux receipts](../formal/results/linux-runs.json) |
| Earlier independent Thor run | At `b14082b`: 128 Python tests, 100 freshly compiled source modules, and 68 audited declarations | [Thor verification](thor-verification.md) and [receipt](../formal/results/thor-verification.json) |
| Strict Comparator | Not passed: hosted runner reported Landlock ABI 7, while ABI 9 was required | [Preflight run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847722684) |

The checkpoint 4 total is **232 selected declarations: 226 focused plus six
standalone, comprising 230 new declarations and two original baseline
declarations**. All use only the standard allowed axioms `propext`,
`Classical.choice`, and `Quot.sound`, or subsets.

[`verification.json`](../formal/results/verification.json) records the exact
selected declarations, axioms, source hashes, and verification scope.
Historical logs are retained; current aggregate compilation and fresh audits
are in `fourth-checkpoint.log`. The source pin and unchanged upstream files
are recorded in provenance, and the focused manifest retains the original
revision entries. The separate successful original-theorem Linux run audits
three original sampling/counting exports at its own recorded commit. It is
neither a Comparator pass nor a Linux verification of these new refinements.

This checkpoint verifies ideal-chain variance bounds, ordinary-table padding,
automatic branch selection, and physical feasibility. It does not verify a
modified finite-bit sampler, a stationary physical output-success theorem at
the new scales, or a complete machine runtime. Official Mathlib cache artifacts
and Lean bootstrap binaries remain trusted.
