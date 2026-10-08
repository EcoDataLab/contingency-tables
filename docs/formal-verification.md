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
the 25 original source modules in the focused dependency closure, their Git
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
The abstraction uses the same pointwise unit-removal operation. It does not
yet verify each physical context's mapping into that abstraction.

## Verification levels

- `standalone` compiles the sharp coefficient, repaired scalar bound, and global ownership abstraction
  without importing the large upstream proof tree, then checks their axioms.
- `focused` compiles the unchanged upstream leaf-energy and root-transport
  modules, then the new refinement, and checks the printed transitive axiom
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

All focused checks passed on 8 October 2026 with Lean 4.34.1:

| Check | Outcome | Evidence |
|---|---|---|
| Unchanged upstream dependency closure | All 25 original modules compiled, through `IntegerLeafEnergy` and `IntegerRootTransport` | [Original build log](../formal/results/upstream-focused-baseline.log) |
| Standalone refinements | Six exported declarations compiled and passed the axiom allowlist at 18:56:17 UTC | [Standalone log](../formal/results/standalone.log) |
| Integrated refinements | Quarter coefficient, leaf-energy bound, actual-width extension, and upstream ownership bridge compiled | [Focused log](../formal/results/focused.log) |
| Focused axiom audit | Nine new declarations and two original baseline declarations passed at 19:06:26 UTC | [Focused log](../formal/results/focused.log) |
| Full `UnconditionalMain` / challenge build | Not run | Separate `full` mode is provided |
| Secure Comparator | Not run; platform preflight exits 2 on macOS | [Comparator preflight log](../formal/results/comparator.log) |

The 17 audited declarations comprise 15 new declarations and two original
baseline declarations. All depend only on the standard allowed axioms
`propext`, `Classical.choice`, and `Quot.sound`; the ownership theorems use only
`propext` and `Quot.sound`. No admissions occur in the new proof files.
[`verification.json`](../formal/results/verification.json) records the exact
declarations, axioms, source-file hashes, and verification scope.

The unchanged source tree was clean before verification, and all nine focused
dependency manifest entries match the original entries exactly. This validates
the local transport improvements and abstract ownership results; it does not
certify the proposed global mixing exponents, the full sampler, or new physical
context embeddings. The original three sampling/counting machine theorems have
not been independently reverified by this focused run.
