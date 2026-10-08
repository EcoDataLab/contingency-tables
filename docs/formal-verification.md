# Formal verification of the #115 refinements

The formal work is additive to OpenAI's pinned #115 source. It does not replace
the sampler, change its target law, or claim a new machine runtime exponent.

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
the 86 original source modules in the expanded focused dependency closure, their Git
blob IDs and SHA-256 hashes, and the original build-file hashes.
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
admissions. This is a local transport refinement; transferring it through all
contexts, parameter schedules, and the concrete sampler requires further work.

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
exact interfaces and remaining exposure, repair, and chain-comparison steps.

## Verification levels

- `standalone` compiles the sharp coefficient, repaired scalar bound, and global ownership abstraction
  without importing the large upstream proof tree, then checks their axioms.
- `focused` compiles the unchanged upstream leaf-energy and root-transport
  modules, then all refinements imported by `Math115`, and checks their printed transitive axiom
  dependencies against `propext`, `Classical.choice`, and `Quot.sound`.
- `full` attempts the unchanged `UnconditionalMain` and Comparator challenge
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

The second local focused checkpoint passed on 8 October 2026 with Lean 4.34.1:

| Check | Outcome | Evidence |
|---|---|---|
| Unchanged upstream dependency closure | 86 original modules in the expanded import closure; source hashes and Git blobs recorded | [Provenance](../formal/results/provenance.json) and [focused build log](../formal/results/focused.log) |
| Standalone refinements | Six exported declarations compiled and passed the axiom allowlist at 18:56:17 UTC | [Standalone log](../formal/results/standalone.log) |
| Integrated refinements | Transport/ownership, actual switching and tails, scale/padding, and physical hard-limit/global-contrast modules compiled | [Focused log](../formal/results/focused.log) |
| Focused axiom audit | 60 new declarations and two original baseline declarations passed at 21:52:20 UTC | [Focused log](../formal/results/focused.log) |
| Earlier published focused checkpoint on fresh Linux | Passed at commit `5e5d6ef`; excludes the subsequent additions in this local checkpoint | [Run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847572556) |
| Full original `UnconditionalMain` / challenge build | Running on Linux at `5e5d6ef`; no successful full-build claim yet | [Run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847944509) |
| Secure Comparator | Hosted runner preflight failed: Landlock ABI 7, required ABI 9; expensive replay skipped | [Run](https://github.com/EcoDataLab/contingency-tables/actions/runs/37847722684) |

The 68 audited declarations comprise 66 new declarations and two original
baseline declarations. All depend only on the standard allowed axioms
`propext`, `Classical.choice`, and `Quot.sound`; the ownership theorems use only
`propext` and `Quot.sound`. No admissions occur in the new proof files.
[`verification.json`](../formal/results/verification.json) records the exact
declarations, axioms, source-file hashes, and verification scope.

The unchanged source tree was clean before verification, and all nine focused
dependency manifest entries match the original entries exactly. This validates
the local transport improvements, actual table tail and padding results,
physical embeddings, and global adjacent-contrast sum. It does not certify the
proposed global mixing exponents or full sampler. The original three
sampling/counting machine theorems have not been independently reverified by
this focused run. [Linux provenance](../formal/results/linux-runs.json) records
separate workflow outcomes at their own source commit.
