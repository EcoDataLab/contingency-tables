# Conditional degree for the fixed public sampler

The exact source passed ordinary native compilation and its three ordered named axiom reports passed saved-log replay. Both checks used authenticated reused native prerequisites and official caches. The result is conditional: no numerical count or draw degree is supplied.

[PublicSamplerDegree.lean](ResearchBounds/PublicSamplerDegree.lean) connects the generic degree certificates to the **existing `Math115.PublicLatticeSampler.machine`**, its exact input encoding and its complete word-count and supplied-word draw realizers. The theorem is conditional on two numerical degree certificates; it does not supply values for them or establish a concrete complete sampler exponent.

Let

```
D(e,t) = 340 * max(1,t) * max(e,6)
S = Algorithms.samplingSize n r h
```

The [original AI semantic source review](reviews/source01/review.md) and [qualification addendum](reviews/source02/addendum.md) remain preserved with their source-review scope. They are not compiler results or human review. Original hash-registry role placeholders identify raw artifacts; redacted logs have separate published hashes.

The two explicit hypotheses are

```lean
DegreeBounds.Typed PublicLatticeSampler.wordCountRealizer e
DegreeBounds.Typed PublicLatticeSampler.publicDrawRealizer t
```

With those hypotheses, the source proves a positive constant `Ctime` such that, for every pair of natural dimensions `m,n`, natural row/column margins `r,c` with equal totals, and **numeric precision `h >= 1`**, the fixed machine's charged execution time on `Algorithms.encodeSamplingInput r c h` is at most `Ctime*S^D(e,t)`. The constant may depend on the supplied certificates, but is chosen before the dimensions, margins and precision.

At that time bound, **every tape `bits : Fin time → Bool` outputs a feasible `Table r c` through `Algorithms.OutputsTable`**. The induced output law has total variation error at most `2^-h` from the uniform law on those tables:

```
(sum_X |tableMass(machine,input,time,X.val) - 1/card(Table r c)|) / 2 <= 2^-h
```

The authoritative [exact Lean statements](ResearchBounds/PublicSamplerDegree.lean) are `machineTime_public_degree` and `fixedMachineBoundedSampling_with_degree`; `publicDegree` is the audited definition. All the codec, random-tape, output and mass terms are the existing `Algorithms`/public-sampler definitions. The theorem preserves both sampler branches and fallback through the same public realizer; it introduces no substitute sampler, runtime oracle or strict Comparator submission.

The finite-word measure underneath this lift is `weight(input) + wordCount(input)`, where the count is numeric reserved bits. Its generic machine-time degree is `2*max(1,t)*max(e,6)`; the existing public word-measure envelope contributes the factor 170 under equal-total margins and `h >= 1`. Neither `d^17` nor `170` is the complete runtime degree. A numerical degree still requires certificates for the actual complete count and draw DAGs, including parser/catalogue, both branches/fallback, preparation, every trial, copying and output.

## Evidence boundaries

The executed [three-name driver](ResearchBounds/PublicSamplerDegreeAudit.lean) requests the definition and the two theorem names. It is a scoped named audit, not exhaustive environment enumeration. The ordinary native diagnostic reuses authenticated accepted R10 prerequisite objects and the [seven-helper packet](../generic-helpers-v1/README.md), with pinned official caches. It is separate from fresh Linux/default-target verification and strict Comparator acceptance. Full cache/closure snapshots and binary objects are omitted from this compact packet; [Provenance bindings](provenance-bindings.json) retain raw digests and explicit source/object identities for that boundary. Public replay remains unperformed. [Verification](verification.json), the [compilation receipt](compilation/receipt.json), [compilation stdout](compilation/stdout.log), [audit receipt](audit/receipt.json), [audit stdout](audit/stdout.log), [exact records](audit/records.json), [AI artifact/log readback](audit/readback.json) and [root AI result readback](audit/root-result-review.json) bind the current evidence. The original helper trust label saying "generic named audit pending" is retained as recorded protocol metadata; the adjacent seven-helper packet separately records its actual 47/21 audit results. This new 3-name audit does not rerun or add to those scopes or the default-target audit roster.

[Selected attempt 01](history/attempt01/receipt.json) failed on the unqualified `polynomial_eval_monotone` identifier. Its [exact source](history/attempt01/ResearchBounds/PublicSamplerDegree.lean), [complete stdout](history/attempt01/stdout.log) and [stderr](history/attempt01/stderr.log) remain failed; no object was promoted. The repaired source qualifies the existing pinned lemma and preserves the statements. This is one selected failure, not complete project history. [Redaction mappings](redaction-manifest.json) separately bind original and published bytes. Source and audit bytes/attribution remain unchanged; logs preserve all diagnostics with workspace-prefix substitution. Public receipts omit process identities. Receipt stream hashes refer to original logs.

## Reproduction after publication

Location: `research/runtime-degree/checkpoints/public-sampler-degree-v1/`. Use the exact adjacent generic-helper packet and one coherent fresh `ResearchBounds` object prefix for all eight modules. Separate partial ResearchBounds trees can shadow one another. These contributor commands passed shell syntax checking but were not executed during publication preparation:

```sh
set -euo pipefail
bash scripts/bootstrap_lean.sh
export ELAN_HOME="$PWD/.tools/elan"
export ELAN_TOOLCHAIN="$(cat formal/lean-toolchain)"
export MATHLIB_CACHE_DIR="$PWD/.tools/mathlib-cache"
TASK_REPO="$PWD"
TASK_HELPERS="$TASK_REPO/research/runtime-degree/checkpoints/generic-helpers-v1"
TASK_PUBLIC="$TASK_REPO/research/runtime-degree/checkpoints/public-sampler-degree-v1"
TASK_OBJECTS="$TASK_REPO/.local/public-sampler-degree-replay-v1"
test ! -e "$TASK_OBJECTS"
mkdir -p "$TASK_OBJECTS/ResearchBounds" "$TASK_OBJECTS/logs"
cd formal
../.tools/elan/bin/lake build \
  OAI.Combinatorics.MatchingCount.Complexity.TreeCostMeasure \
  OAI.Combinatorics.MatchingCount.Complexity.OnlineWordCost \
  OAI.Combinatorics.ContingencyTables.Machines.FiniteWordMachine \
  Math115.LatticeScheduleProgram Math115.PublicLatticeSampler
for TASK_MODULE in TreeDegreeBounds PolynomialCompilerDegree FreshBitDegreeBounds FiniteWordDegreeBounds TreeArithmeticDegree ScalarOutputSizeDegree WordCountSeedDegrees; do
  ../.tools/elan/bin/lake env bash -c '
    export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
    lean --root="$2" -j2 -M8192 -DautoImplicit=false \
      -o "$1/ResearchBounds/$3.olean" -i "$1/ResearchBounds/$3.ilean" \
      "$2/ResearchBounds/$3.lean"
  ' _ "$TASK_OBJECTS" "$TASK_HELPERS" "$TASK_MODULE" \
    >"$TASK_OBJECTS/logs/$TASK_MODULE.stdout.log" \
    2>"$TASK_OBJECTS/logs/$TASK_MODULE.stderr.log"
done
../.tools/elan/bin/lake env bash -c '
  export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
  lean --root="$2" -j2 -M8192 -DautoImplicit=false \
    -o "$1/ResearchBounds/PublicSamplerDegree.olean" \
    -i "$1/ResearchBounds/PublicSamplerDegree.ilean" \
    "$2/ResearchBounds/PublicSamplerDegree.lean"
' _ "$TASK_OBJECTS" "$TASK_PUBLIC" \
  >"$TASK_OBJECTS/logs/PublicSamplerDegree.stdout.log" \
  2>"$TASK_OBJECTS/logs/PublicSamplerDegree.stderr.log"
../.tools/elan/bin/lake env bash -c '
  export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
  lean --root="$2" -j2 -M8192 -DautoImplicit=false \
    "$2/ResearchBounds/PublicSamplerDegreeAudit.lean"
' _ "$TASK_OBJECTS" "$TASK_PUBLIC" \
  >"$TASK_OBJECTS/logs/PublicSamplerDegreeAudit.stdout.log" \
  2>"$TASK_OBJECTS/logs/PublicSamplerDegreeAudit.stderr.log"
python3 "$TASK_PUBLIC/audit/check_lean_axioms.py" \
  "$TASK_PUBLIC/ResearchBounds/PublicSamplerDegreeAudit.lean" \
  <"$TASK_OBJECTS/logs/PublicSamplerDegreeAudit.stdout.log"
```

Do not run `lake update`. `-M8192` is an allocation cap, not a wall-clock limit or measured sampler runtime. An evidentiary replay also records compiler/toolchain, exact source/import-object/snapshot hashes before/after, exits/timeouts and both streams. Preserve failures and version any repair. A shell/checker pass alone does not recreate the original authenticated native provenance.
