# Affine refinement of the conditional sampler degree

Two exact Lean modules passed ordinary native compilation, with separate named axiom audits of **six declarations** for the finite-word refinement and **four declarations** for its public-sampler specialization. Both saved-log scopes pass exact ordered replay using only subsets of `propext`, `Classical.choice`, and `Quot.sound`. The [independent AI saved-artifact review](review/review.md) passed its scoped checks; it is not human review or a new compiler run.

The conditional public degree improves from

```
340 * max(1,t) * max(e,6)
```

to

```
340 * max(max(e,6),t)
```

The [comparison lemma](ResearchBounds/AffinePublicSamplerDegree.lean) proves that the new expression is no larger for every pair of natural degree parameters. The [original bridge](../public-sampler-degree-v1/README.md) remains available with its unchanged source and evidence. **Numerical `e` and `t` are still unresolved**; neither formula supplies a concrete complete sampler exponent or a measured runtime result.

| Module | Exact source | Native receipt | Named audit |
| --- | --- | --- | --- |
| Affine finite-word degree | [AffineFiniteWordDegreeBounds.lean](ResearchBounds/AffineFiniteWordDegreeBounds.lean) | [Compilation](compilation/AffineFiniteWordDegreeBounds/receipt.json) | [Six names](audit/AffineFiniteWordDegreeBounds/receipt.json) |
| Affine public-sampler degree | [AffinePublicSamplerDegree.lean](ResearchBounds/AffinePublicSamplerDegree.lean) | [Compilation](compilation/AffinePublicSamplerDegree/receipt.json) | [Four names](audit/AffinePublicSamplerDegree/receipt.json) |

The improvement separates charged computation from the size of the data passed to the draw. Generating `n(a)` fresh Boolean cells gives encoded output weight at most `4*n(a)+1`. Keeping the original input alongside that word gives a pair of weight at most `4*w+2`, where **`w = weight(a) + n(a)`** is the finite-word measure and the reserved-bit count `n(a)` is numeric. This affine output bound lets the draw polynomial compose with a degree-one size envelope rather than the count-work polynomial. The same complete online realizer therefore has conditional degree `max(max(e,6),t)`, and the unchanged physical compiler contributes a factor 2.

## Exact public claim

The public theorem assumes

```lean
DegreeBounds.Typed PublicLatticeSampler.wordCountRealizer e
DegreeBounds.Typed PublicLatticeSampler.publicDrawRealizer t
```

These certify the actual complete realizers, including charged work and encoded output weight; they are not supplied here. For fixed certificates, there is **one positive `Ctime`**, chosen before the dimensions, margins and precision, such that for all natural `m,n`, natural row/column margins with equal totals, and **numeric `h >= 1`**,

```
PublicLatticeSampler.machineTime(Algorithms.encodeSamplingInput r c h)
  <= Ctime * (Algorithms.samplingSize n r h) ^ (340 * max(max(e,6),t))
```

At that time, every tape `bits : Fin time → Bool` outputs a feasible original `Table r c` through `Algorithms.OutputsTable`. The induced output law has total variation distance at most `2^-h` from the uniform table law. Empty dimensions and zero margins remain covered when equal totals hold. The authoritative [exact Lean statements](ResearchBounds/AffinePublicSamplerDegree.lean) are `machineTime_public_degree` and `fixedMachineBoundedSampling_with_degree`.

The machine is still **`Math115.PublicLatticeSampler.machine`**, with the same `Algorithms` encoding, output tape, table mass and both sampler branches/fallback. The public size is exactly `Algorithms.samplingSize n r h`; the existing degree-170 word-measure envelope applies under equal totals and `h >= 1`. This refinement changes a conditional bound, not the implementation, codec, precision convention or sampler law. The positive coefficient need not equal the earlier bridge's coefficient. Complete parser/catalogue, count and draw degree certificates remain open. No fresh Linux/default-target verification or strict Comparator acceptance is asserted.

## Evidence and retained failure

[Verification](verification.json) binds the two exact source/object/receipt pairs and two audit scopes. Actual [six-name log](audit/AffineFiniteWordDegreeBounds/stdout.log), [six-name records](audit/AffineFiniteWordDegreeBounds/records.json), [four-name log](audit/AffinePublicSamplerDegree/stdout.log), [four-name records](audit/AffinePublicSamplerDegree/records.json) and [AI artifact/log readback](audit/readback.json) are separate from exhaustive environment enumeration or existing default-target counts. The two **executed per-module audit drivers** are [six-name driver](audit-source/Checkpoint12Audits/ResearchBounds_AffineFiniteWordDegreeBounds.lean) and [four-name driver](audit-source/Checkpoint12Audits/ResearchBounds_AffinePublicSamplerDegree.lean); their bytes are preserved exactly.

[Provenance bindings](provenance-bindings.json) record accepted native R10 sampler objects, the complete shared eight-module namespace comprising the [seven helpers](../generic-helpers-v1/README.md) and [original public bridge](../public-sampler-degree-v1/README.md), and the fresh first affine object used by the second module. Official pinned package/toolchain caches are reused. Full normal/cache snapshots and binary objects are omitted; raw capture/config/runtime/snapshot identities and direct source/object bindings remain explicit. This is ordinary native evidence using authenticated reused prerequisites, not a fresh normal rebuild. The independent review locally rehashes captured bytes; uncaptured transitive cache bytes rely on the preserved runtime authentication and successful before/after checks. Public replay remains unperformed. Source attribution and creation-time draft headers remain unchanged; source-only comments describe the earlier stage, while receipts record the later checked status.

[Selected affine01 authentication failure](history/attempt01/failure.json) was caused by attempting to authenticate a local generated Python-cache file as a prior capture input. The accepted public-degree authority is the **original immutable 116-file remote capture manifest**, not a later local directory inventory containing Python caches or a collector manifest. Affine02 binds that original allowlist explicitly. Affine01 remains a failed prerequisite-authentication attempt, with no affine proof/audit outcome or promoted object inferred from it. This is one selected failure, not complete research history.

[Redaction mappings](redaction-manifest.json) bind original and published hashes separately. Sources/license and actual drivers retain exact bytes. Logs retain full warnings/errors with only owned-workspace prefix substitution. Public receipt projections omit process identities; original stream hashes still refer to original logs, while published hashes are separate. Raw execution context is retained through digests, not account/host identifiers or transcripts.

## Reproduction

Location: `research/runtime-degree/checkpoints/affine-public-sampler-degree-v1/`. The prior packets remain separate and unchanged. Use **one fresh shared ResearchBounds object prefix** for all ten source modules; partial separate trees can shadow one another. These contributor commands are syntax-checked preparation instructions, not a public-platform replay:

```sh
set -euo pipefail
bash scripts/bootstrap_lean.sh
export ELAN_HOME="$PWD/.tools/elan"
export ELAN_TOOLCHAIN="$(cat formal/lean-toolchain)"
export MATHLIB_CACHE_DIR="$PWD/.tools/mathlib-cache"
TASK_REPO="$PWD"
TASK_HELPERS="$TASK_REPO/research/runtime-degree/checkpoints/generic-helpers-v1"
TASK_PUBLIC="$TASK_REPO/research/runtime-degree/checkpoints/public-sampler-degree-v1"
TASK_AFFINE="$TASK_REPO/research/runtime-degree/checkpoints/affine-public-sampler-degree-v1"
TASK_OBJECTS="$TASK_REPO/.local/affine-public-degree-replay-v1"
test ! -e "$TASK_OBJECTS"
mkdir -p "$TASK_OBJECTS/ResearchBounds" "$TASK_OBJECTS/logs"
cd formal
../.tools/elan/bin/lake build \
  OAI.Combinatorics.MatchingCount.Complexity.TreeCostMeasure \
  OAI.Combinatorics.MatchingCount.Complexity.OnlineWordCost \
  OAI.Combinatorics.ContingencyTables.Machines.FiniteWordMachine \
  Math115.LatticeScheduleProgram Math115.PublicLatticeSampler
for TASK_MODULE in TreeDegreeBounds PolynomialCompilerDegree FreshBitDegreeBounds FiniteWordDegreeBounds TreeArithmeticDegree ScalarOutputSizeDegree WordCountSeedDegrees PublicSamplerDegree AffineFiniteWordDegreeBounds AffinePublicSamplerDegree; do
  case "$TASK_MODULE" in
    PublicSamplerDegree) TASK_SOURCE_ROOT="$TASK_PUBLIC" ;;
    Affine*) TASK_SOURCE_ROOT="$TASK_AFFINE" ;;
    *) TASK_SOURCE_ROOT="$TASK_HELPERS" ;;
  esac
  ../.tools/elan/bin/lake env bash -c '
    export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
    lean --root="$2" -j2 -M8192 -DautoImplicit=false \
      -o "$1/ResearchBounds/$3.olean" -i "$1/ResearchBounds/$3.ilean" \
      "$2/ResearchBounds/$3.lean"
  ' _ "$TASK_OBJECTS" "$TASK_SOURCE_ROOT" "$TASK_MODULE" \
    >"$TASK_OBJECTS/logs/$TASK_MODULE.stdout.log" \
    2>"$TASK_OBJECTS/logs/$TASK_MODULE.stderr.log"
done
for TASK_MODULE in AffineFiniteWordDegreeBounds AffinePublicSamplerDegree; do
  TASK_AUDIT="ResearchBounds_$TASK_MODULE"
  ../.tools/elan/bin/lake env bash -c '
    export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
    lean --root="$2/audit-source" -j2 -M8192 -DautoImplicit=false \
      "$2/audit-source/Checkpoint12Audits/$3.lean"
  ' _ "$TASK_OBJECTS" "$TASK_AFFINE" "$TASK_AUDIT" \
    >"$TASK_OBJECTS/logs/$TASK_AUDIT.stdout.log" \
    2>"$TASK_OBJECTS/logs/$TASK_AUDIT.stderr.log"
  python3 "$TASK_AFFINE/audit/check_lean_axioms.py" \
    "$TASK_AFFINE/audit-source/Checkpoint12Audits/$TASK_AUDIT.lean" \
    <"$TASK_OBJECTS/logs/$TASK_AUDIT.stdout.log"
done
```

Do not run `lake update`. `-M8192` is an allocation cap, not a wall-clock limit or measured sampler runtime. Preserve compiler banner/digest, exact sources/import objects and snapshots before/after, all exits/timeouts and both streams for an evidentiary replay. A shell/checker pass alone does not reconstruct the authenticated native provenance. Retain failures and version repairs separately.
