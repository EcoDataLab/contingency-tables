# Actual matrix printer runtime degree

11 October 2026. A polynomial of degree at most **4** bounds the charged work
plus encoded Symbol output of the exact frozen
`OAI.ContingencyTables.GreedyFeasibleTable.printMatrixRealizer`, uniformly over
all `List (List Nat)` inputs, including arbitrary ragged and empty matrices.
There is no feasibility, rectangularity, equal-total, successful-parse, or
assumed printing-cost premise.

The [actual compiled readback](audit/type-readback.txt) is:

```
exists p : Polynomial Nat,
  p.natDegree <= 4 and
  forall rows : List (List Nat),
    printMatrixRealizer.cost rows + weight (printMatrix rows)
      <= p.eval (weight rows)
```

The actual source program is exactly
`flatMapPoly (flatMapPoly LiteralCodec.natWordRealizer)`.
[LinearCollections.lean](PrinterRuntime/LinearCollections.lean) certifies the
unchanged append program with degree 2 and flatten with degree 3. Eager map has
degree `e+1` when the mapped function has an independently proved affine output
bound; every intermediate and final output, including the final reversal, is
charged. [PrinterDegree.lean](PrinterRuntime/PrinterDegree.lean) derives degree 2
for the actual bits/map/append natural-word encoder, degree 3 for row printing,
and degree 4 for the nested matrix printer. Symbol output uses the actual
literal codec fact `weight_word = 18*length+1`.

The headline is `Math115.PrinterRuntimeNext.typed_actual_printMatrix`; its explicit
pointwise endpoint is `actual_printMatrix_polynomial`. The generic affine-output
premises are proved for the actual printer leaves before specialization. No
printer, codec, realizer, machine, or frozen source statement is replaced.

This closes `ActualDrawSeams.printer` in addition to the earlier
[branch certificate](../actual-branch-degree-v1/README.md). Five of the original
seven draw fields remain: `initial`, `fallback`, `referenceTrial`, `unitTrial`
and `retryWords`, for the exact realizers in the
[historical helper packet](../actual-count-draw-helpers-v1/README.md#remaining-numerical-draw-certificates).
The complete numerical draw degree `t` remains unknown; the complete word-count
certificate is still 1008, and the affine public runtime degree remains
conditional `340*max(1008,t)`.

## Verification

Both exact new source modules have successful fresh ordinary local compilation
with pinned Lean 4.34.1, `-j2`, `-M8192` and `-DautoImplicit=false`. Their first
successful sources were frozen before one relevant audit of all 25 new
definitions/lemmas and the actual headline types. Every transitive named axiom
report uses only `propext`, `Classical.choice` and `Quot.sound`.
[Verification](verification.json), module receipts and
[complete named/type output](audit/stdout.txt) bind the exact source/object,
compiler and driver bytes. Compile times are proof-checking times.
The separate [AI source review](SOURCE_REVIEW.md) passed for the actual program,
output charges and saved evidence. It is not a human review or a second compiler run.

Fourteen thin pinned prerequisites were compiled privately, with exact source
and object hashes in [prerequisite-bindings.json](prerequisite-bindings.json).
Their sources are not duplicated. Two exact existing degree helpers and trusted
baseline dependency/cache objects were reused. Baseline objects and previous
packets were not changed. The [two M4096 failures](history/memory-failures.json)
retain exact lossless interpreter-memory diagnostics; the larger bounded
allocation cap then succeeded. Other development/elaboration diagnostics remain
private. New source and audit-driver bytes are unchanged; any diagnostic path
projection is declared in [redaction-manifest.json](redaction-manifest.json).

This is ordinary local compiler execution with reused trusted imports and
named transitive axiom/type inspection. It is not a full environment inventory,
a default-target rebuild, a fresh Linux or strict Comparator replay, measured
sampler timing, or a complete numerical draw/sampler degree certificate.

## Reproduce

Use the existing pinned baseline containing
`OAI.Combinatorics.ContingencyTables.Sampling.GreedyPublicProgram` and the two
unchanged generic helper objects `ResearchBounds.TreeDegreeBounds` and
`ResearchBounds.TreeArithmeticDegree` from the
[generic helper packet](../generic-helpers-v1/README.md). [REPRODUCE.sh](REPRODUCE.sh)
takes their object root and a fresh output directory, resolving relative paths
before changing directory. It compiles only the two new modules and runs the
focused ordered axiom/type checker. These prepared public-path commands have
not themselves been replayed; no dependency update or broad duplicate audit is
required.
