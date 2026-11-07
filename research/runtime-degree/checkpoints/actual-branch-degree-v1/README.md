# Actual large-block branch runtime degree

11 October 2026. A polynomial of degree at most **1008** bounds charged work
plus encoded Boolean output of the exact frozen
`Math115.LatticeSamplerPreparation.bothLargeTestRealizer`, uniformly over every
pair of natural margin lists, including empty lists and unequal totals.

The actual compiler readback is:

```
exists p : Polynomial Nat,
  p.natDegree <= 1008 and
  forall z : List Nat * List Nat,
    bothLargeTestRealizer.cost z + weight (bothLargeTest z)
      <= p.eval (weight z)
```

The certificate is `Math115.DrawRuntimeNext.typed_actual_bothLargeTest` in
[BranchDegree.lean](DrawRuntime/BranchDegree.lean); the explicit pointwise
endpoint is `actual_bothLargeTest_polynomial`. [Verification](verification.json)
and the [exact named audit/readback](audit/stdout.txt) record the checked types.

This closes the `branch` field among the seven previously unresolved fields
of `Math115.DrawDegree.ActualDrawSeams`. The six remaining certificates are
`printer`, `initial`, `fallback`, `referenceTrial`, `unitTrial` and `retryWords`,
for their unchanged actual realizers listed in the
[earlier helper packet](../actual-count-draw-helpers-v1/README.md#remaining-numerical-draw-certificates).
The complete word-count degree remains 1008. A complete numerical draw degree
`t`, and hence a complete numerical sampler runtime degree, remains unresolved.
The current affine composition is still conditional `340*max(1008,t)`.

## Exact program and degree derivation

No predicate, realizer, codec, frozen machine or original source statement is
replaced. The certificate covers threshold preparation, both complete index
ranges/filter passes, indexed margin reads, both list-length folds,
comparisons, Boolean conjunction and final encoded output. It does not assume
that a failed first row test skips construction of the column list.

The actual indexed predicate has degree 2; the numeric range is generated from
stored list length and has degree 3. The existing actual filterWith helper gives
degree 336, yielding degree 1008 for largeIndices. The cutoff is an affine-output
scalar circuit of degree 6. A separate bound proves that the actual filtered
index list has weight at most `4S^2+2S+1`, independently of its threshold.
Composing the degree 2 length routine with that output bound preserves the
1008 degree instead of multiplying it into 2016. These size premises are proved
from the actual lists, not supplied as assumed runtime conclusions.

[RangeSeed.lean](DrawRuntime/RangeSeed.lean) isolates the published deterministic
numeric-range proof from the earlier fresh-word module so its unrelated online
compiler prerequisites need not be imported. The range implementation and cost
model remain identical. The getDFast and bounded-range bridges use the same
actual realizers as the earlier helper packet.

## Evidence and limits

RangeSeed has fresh successful native Windows x86_64 compilation from attempt 03;
that byte-identical source/object and original receipt are explicitly reused in
attempt 04. BranchDegree has fresh successful compilation in attempt 04. The
ordered 20-name audit is a fresh native execution against those exact objects.
All 20 transitive named reports use only `propext`, `Classical.choice` and
`Quot.sound`. Exact 20-name/type readback passed. Independent AI review checked the degree and size argument; the final elaboration repairs preserve its witnesses and semantics.

The trusted pinned compiler is Lean 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`, on x86_64-w64-windows-gnu.
Its byte identity is recorded. 1660 existing imported-object bindings, the new
source hashes and owned executor bindings were checked. Existing authenticated
complete-sampler objects and official caches were reused. Compiler stages use
`-j2`, `-M6144` and `-DautoImplicit=false`, with 600-second caps. Owned Windows Job receipts
confirm terminal/reaped compiler processes and descendants. The original source,
commands, control paths, full identity/resource logs and cache bindings remain
private; no binary objects are distributed.

[Preserved failures](history/failures.json) distinguish the initial ambiguous
head helper, three function-index alias errors, and a later missing input-type
annotation. They are corrected by qualifying the existing lemma, reusing the
same witnesses pointwise, and specifying the actual input type. No endpoint
hypothesis, realizer or degree was changed. Diagnostics are complete apart from
the declared path-role projection in [redaction-manifest.json](redaction-manifest.json).
Source/audit driver bytes are unchanged. The focused checker accepts only the ordered 20 axiom reports plus the exact captured theorem readback. The [manifest](manifest.json) hashes
this focused public packet.

This is ordinary native compilation and named transitive axiom inspection with
the recorded compiler/cache trust boundary. It is not a full environment
inventory, fresh Linux/default-target verification, strict Comparator replay,
measured sampler timing, or a complete draw/sampler degree certificate.
Compilation times in receipts are proof-checking times.

## Reproduce

Prepare the existing pinned complete-sampler objects and the exact prerequisites
of the earlier [actual helper packet](../actual-count-draw-helpers-v1/REPRODUCE.sh).
Do not update the toolchain or lake dependencies. With those helper objects
available, use [REPRODUCE.sh](REPRODUCE.sh) and a new output root. These are prepared
contributor instructions; the public-path shell replay has not been run.
