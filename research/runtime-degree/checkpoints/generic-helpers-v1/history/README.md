# Selected newer failed diagnostics

This packet preserves five selected failed attempts with exact saved source bytes, projected receipts and both logs. The [index](index.json) binds source and original receipt hashes. The [redaction map](../redaction-manifest.json) distinguishes original versus published receipt/log bytes. All five receipts record exit 1; no failed object was promoted.

| Attempt | Actual outcome | Source/receipt/log |
| --- | --- | --- |
| Fresh original (v1) | Proof elaboration failure | [source](fresh-v1/ResearchBounds/FreshBitDegreeBounds.lean), [receipt](fresh-v1/receipt.json), [stdout](fresh-v1/stdout.log), [stderr](fresh-v1/stderr.log) |
| Fresh v2 | Proof elaboration failure with unsolved goals | [source](fresh-v2/ResearchBounds/FreshBitDegreeBounds.lean), [receipt](fresh-v2/receipt.json), [stdout](fresh-v2/stdout.log), [stderr](fresh-v2/stderr.log) |
| Finite original, first layout | Import-layout failure before theorem elaboration | [source](finite-original-layout/ResearchBounds/FiniteWordDegreeBounds.lean), [receipt](finite-original-layout/receipt.json), [stdout](finite-original-layout/stdout.log), [stderr](finite-original-layout/stderr.log) |
| Scalar original (`aff58…`) | Proof elaboration/type mismatch failure; no accepted object | [source](scalar-original-elaboration/ResearchBounds/ScalarOutputSizeDegree.lean), [receipt](scalar-original-elaboration/receipt.json), [stdout](scalar-original-elaboration/stdout.log), [stderr](scalar-original-elaboration/stderr.log) |
| Finite original, merged layout | Actual proof elaboration failure | [source](finite-original-elaboration/ResearchBounds/FiniteWordDegreeBounds.lean), [receipt](finite-original-elaboration/receipt.json), [stdout](finite-original-elaboration/stdout.log), [stderr](finite-original-elaboration/stderr.log) |

The finite-word attempts use the same original source hash. The first failed because Lean selected the first ResearchBounds directory, which lacked TreeDegreeBounds.olean; it did not test the candidate's mathematics. After the namespace library was merged, the unchanged source reached elaboration and failed. The later repaired source in the [current packet](../README.md) passed ordinary compilation; its actual 47-name audit passed. The repaired scalar source11c1 subsequently passed ordinary compilation and the separate21-name audit in the current packet; this historical attempt remains failed.

These five attempts were selected from the named saved collections. This is not an enumeration of every diagnostic in the project and is not advertised as complete history. The [older runtime-degree archive](../../../README.md) remains unchanged. Logs retain all recorded diagnostics, including warnings and line numbers, with owned-workspace prefixes replaced. Receipts retain original stream digests, while the redaction map binds published stream digests.

Historical sources are reproduction targets for their recorded failures, not successful inputs. They live under separate versioned source roots and must not be mixed into the accepted ResearchBounds namespace library. No public replay of these failures or of the successful current helpers was performed in this preparation.
