# Actual joint denominator at the smaller scales

24 October 2026. Ordered distinct labels and the repaired full table encode every actual defect/completion pair injectively. Combining this encoding with the existing marked-padding count theorem gives Z<=2*p*(p-1)*N at U=11*d*(m+n-2), L=7.

This instantiates the actual large-cell mask in `Research.ReciprocalCount.shape_padding_count_le_twice`; it does not assume a count ratio or reuse the old 5d^3 cutoff. Attempt04 compiled but its audit exhausted disk space. Attempt05 compiled the same source and completed the audit. The let-bound cell-count name was changed to avoid an existing notation; the full candidate diff records this.

| English claim | Lean statement | Hypotheses |
|---|---|---|
| Actual joint encoding is injective | `terminalRepairEncoding_injective` | Arbitrary natural margins and scales; actual inputs |
| Each successful ordinary fibre has at most p*(p-1) members | `terminalOutputFibre_card_le` | An ordinary target |
| Actual padded count is at most twice the ordinary count | `actualShape_padded_count_le_twice` | U=11*d*(m+n-2), L=7 |
| Z<=2*p*(p-1)*N | `actualShape_defectJoint_card_le` | Same scales |

Ordinary compilation of the [source](formal/ResearchPhysicalTraceJoin/GeneralCount.lean) passed in 44.83 seconds; the full assumption audit passed in 58.38 seconds. The [receipt](attempt-05/verification.json) records 4 complete headline dependency closures and the loaded object hashes. Only `propext`, `Classical.choice` and `Quot.sound` occur. The compiler and reused dependencies remain trusted; this is separate from default-target Linux or Comparator verification. See the [consolidated AI source review](../physical-trace-general-terminal-law/AI-SOURCE-REVIEW.md) and [composed ideal output law](../physical-trace-general-terminal-law/). No new complete sampler or runtime exponent is claimed.

Prepare the pinned Lean4.34.1 compiler and the dependency objects named by the imports, including `ResearchAudit.EnvironmentAudit`, then run:

```sh
LEAN_PATH=<prepared-object-roots> bash REPRODUCE.sh /absolute/path/to/new-output-directory
```

The script compiles this module and audits its loaded environment; it downloads or rebuilds no dependencies. Saved source and compressed audit bytes are unchanged. Public diagnostic paths are projected. [Attempt history](attempts.json) preserves each actual failed compiler or audit stage and dependency preflight.
