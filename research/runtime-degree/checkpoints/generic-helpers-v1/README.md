# Generic runtime-degree certificates

Seven exact Lean helper modules passed ordinary native compilation, with two distinct named axiom audits: **47 declarations for the four core helpers** and **21 declarations for arithmetic, scalar-output and word-count seeds**. Saved-log replay confirms every requested name in order, using only subsets of `propext`, `Classical.choice`, and `Quot.sound`. This establishes generic degree certificates and selected building blocks; a numerical degree for the complete contingency-table sampler remains open.

| Module | Source/compilation evidence | Named audit scope |
| --- | --- | --- |
| Tree degree certificates | [source](ResearchBounds/TreeDegreeBounds.lean), [receipt](compilation/TreeDegreeBounds/receipt.json) | [Core 47](audit/generic47/receipt.json) |
| Pure compiler polynomial algebra | [source](ResearchBounds/PolynomialCompilerDegree.lean), [receipt](compilation/PolynomialCompilerDegree/receipt.json) | Core 47 |
| Fresh-bit degree certificates | [source](ResearchBounds/FreshBitDegreeBounds.lean), [receipt](compilation/FreshBitDegreeBounds/receipt.json) | Core 47 |
| Finite-word machine degree lift | [source](ResearchBounds/FiniteWordDegreeBounds.lean), [receipt](compilation/FiniteWordDegreeBounds/receipt.json) | Core 47 |
| Arithmetic realizers | [source](ResearchBounds/TreeArithmeticDegree.lean), [receipt](compilation/TreeArithmeticDegree/receipt.json) | [Extension 21](audit/extension21/receipt.json) |
| Scalar output size and fixed powers | [source](ResearchBounds/ScalarOutputSizeDegree.lean), [receipt](compilation/ScalarOutputSizeDegree/receipt.json) | Extension 21 |
| Word-count seed realizers | [source](ResearchBounds/WordCountSeedDegrees.lean), [receipt](compilation/WordCountSeedDegrees/receipt.json) | Extension 21 |

The tree certificates hold the codec and realizer fixed. The fresh-bit bound has degree 6 in the measure **`n + weight(n)`**, where `n` is the numeric requested bit count and `weight(n)` is its codec weight. The finite-word lift bounds the actual pinned compiler's machine time by a polynomial of degree `2*max(1,t)*max(e,6)` in **`FiniteWordExecution.wordMeasure n input = weight(input) + n(input)`**; `n(input)` is the numeric reserved-bit count. Its hypotheses are `Typed N e` and `Typed F t` for the deterministic word-count and supplied-word draw realizers used by that compiler.

Under equal-total margins and numeric precision **`h >= 1`**, applying the established degree-170 public word-measure envelope would give **`340*max(1,t)*max(e,6)`**. The complete sampler's numerical certificates `e` and `t` are still missing. Neither `d^17` nor `170` is its complete runtime degree. The compiler lift includes packing, stack execution, tape erasure, unpacking and output printing, retaining the same program.

The new arithmetic layer proves conservative degree certificates for the actual supplied realizers, including multiplication. The scalar layer proves degree **6 for each fixed program `k`** in `LatticeScheduleProgram.fixedPowerRealizer k`; coefficients may depend on `k`. It does not give a uniform degree claim with `k` as an extra runtime input. The seed layer certifies subtraction, predecessor, list length/sum, digits, bit size and ceiling log two. Catalogue and parser certificates, and assembly of the complete public word-count and draw DAGs, remain unresolved.

## Evidence and limits

[verification.json](verification.json) binds all seven source/object/raw-receipt hashes and separates the two audit scopes. Actual [core log](audit/generic47/stdout.log), [core records](audit/generic47/records.json), [core AI readback](audit/generic47/readback.json), [extension log](audit/extension21/stdout.log), [extension records](audit/extension21/records.json) and [extension AI readback](audit/extension21/readback.json) come from the coherent final native observation. The [earlier core-audit observation](audit/generic47-observation01/readback.json) is preserved; its stdout is byte-identical to the repeated final core audit. The core's 40-public-theorem count is a static source classification, distinct from its 47 actual declaration reports. Neither named audit is exhaustive environment enumeration.

The diagnostics and audits reuse authenticated accepted native prerequisite objects and pinned official package/toolchain caches. They are not fresh normal rebuilds. This compact packet omits full closure and cache snapshots; [provenance bindings](audit/provenance-bindings.json) retain their raw artifact digests, runtime/compiler pins and exact helper object bindings. The [root result review](audit/root-result-review.json) and AI saved-log readbacks record scoped review, not human review. No fresh Linux/default-target verification, strict Comparator acceptance or measured sampler runtime is asserted here. Public reproduction remains unperformed.

[Redaction mappings](redaction-manifest.json) distinguish original and published hashes. All seven source files and both executed audit drivers retain exact bytes and attribution. Header comments describing a source as a private, uncompiled draft describe its creation-time scope; the linked receipts record its later checked status. Public logs retain warnings/errors and line numbers, replacing owned-workspace prefixes; receipts omit process identities and use path placeholders. Receipt stream hashes bind original logs; the redaction map separately binds published logs. Binary objects are identified by digest, not distributed.

[Selected failure history](history/README.md) retains two fresh-bit proof failures, the original finite-word import-layout failure followed by its actual elaboration failure, and the original scalar elaboration failure. This selected set is not advertised as complete history. The [earlier runtime-degree archive](../../README.md) remains unchanged.

## Reproduction

Versioned layout: `research/runtime-degree/checkpoints/generic-helpers-v1/`. All seven modules share the **ResearchBounds module prefix**; their declarations use `Math115.DegreeBounds`, `Math115.ScalarOutputDegree` and `Math115.WordCountSeedDegrees`. Build into one fresh ResearchBounds object tree, because separate partial prefix trees can shadow one another in Lean's search path.

From a fresh public checkout containing this packet, use the existing pinned bootstrap and manifest; do not run `lake update`. These contributor commands were syntax-checked but not executed during publication preparation:

```sh
set -euo pipefail
bash scripts/bootstrap_lean.sh
export ELAN_HOME="$PWD/.tools/elan"
export ELAN_TOOLCHAIN="$(cat formal/lean-toolchain)"
export MATHLIB_CACHE_DIR="$PWD/.tools/mathlib-cache"
TASK_REPO="$PWD"
TASK_PACKET="$TASK_REPO/research/runtime-degree/checkpoints/generic-helpers-v1"
TASK_OBJECTS="$TASK_REPO/.local/generic-degree-replay-v1"
# Use a new output path for every replay and retain failures.
test ! -e "$TASK_OBJECTS"
mkdir -p "$TASK_OBJECTS/ResearchBounds" "$TASK_OBJECTS/logs"
cd formal
../.tools/elan/bin/lake build \
  OAI.Combinatorics.MatchingCount.Complexity.TreeCostMeasure \
  OAI.Combinatorics.MatchingCount.Complexity.OnlineWordCost \
  OAI.Combinatorics.ContingencyTables.Machines.FiniteWordMachine \
  Math115.LatticeScheduleProgram
for TASK_MODULE in TreeDegreeBounds PolynomialCompilerDegree FreshBitDegreeBounds FiniteWordDegreeBounds TreeArithmeticDegree ScalarOutputSizeDegree WordCountSeedDegrees; do
  ../.tools/elan/bin/lake env bash -c '
    export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
    lean --root="$2" -j2 -M8192 -DautoImplicit=false \
      -o "$1/ResearchBounds/$3.olean" -i "$1/ResearchBounds/$3.ilean" \
      "$2/ResearchBounds/$3.lean"
  ' _ "$TASK_OBJECTS" "$TASK_PACKET" "$TASK_MODULE" \
    >"$TASK_OBJECTS/logs/$TASK_MODULE.stdout.log" \
    2>"$TASK_OBJECTS/logs/$TASK_MODULE.stderr.log"
done
for TASK_AUDIT in GenericDegreeNamedAudit NewDegreeNamedAudit; do
  ../.tools/elan/bin/lake env bash -c '
    export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
    lean --root="$2" -j2 -M8192 -DautoImplicit=false \
      "$2/ResearchBounds/$3.lean"
  ' _ "$TASK_OBJECTS" "$TASK_PACKET" "$TASK_AUDIT" \
    >"$TASK_OBJECTS/logs/$TASK_AUDIT.stdout.log" \
    2>"$TASK_OBJECTS/logs/$TASK_AUDIT.stderr.log"
  python3 "$TASK_PACKET/audit/check_lean_axioms.py" \
    "$TASK_PACKET/ResearchBounds/$TASK_AUDIT.lean" \
    <"$TASK_OBJECTS/logs/$TASK_AUDIT.stdout.log"
done
```

`-M8192` caps Lean allocation; it is not a wall-clock limit or a measured runtime result. Dependency build resources and results vary by platform. For an evidentiary replay, preserve compiler banner/digest, source and complete import-object/snapshot hashes before/after, exits/timeouts and both streams. A shell/checker pass alone does not recreate the authenticated native provenance receipts. Record any failure, repair sources as new versions and retain the original attempts.

The next mathematical contribution is to supply degree certificates for the actual complete word-count and public-draw DAGs, including both branches/fallback, preparation, every trial, copying and output. An existential polynomial-time theorem or a certificate for a replacement program does not determine the missing `e` and `t`.
