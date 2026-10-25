# Exact ordinary support and slack count

24 October 2026. For L>=1, inverse feasibility is exactly positive ordinary crossing support when the crossing is small, or positive ordinary row and column residual slack when it is large. The finite sum over ordered small labels equals the actual successful ordinary-output multiplicity.

Positive padding cannot substitute for ordinary slack. The count is an explicit label sum; the compact D0+abuv factorization and its executable cost are separate.

| English claim | Lean statement | Hypotheses |
|---|---|---|
| Arithmetic test equals the support/slack predicate | `inverseLocalTest_iff_support` | Ordinary target; L>=1 |
| The count is the actual repair-matrix fibre cardinality | `terminalRepairFibre_card_eq_supportCount` | Same |
| Repair-matrix and successful-output fibres agree | `repairFibreOutputEquiv`, `terminalOutput_card_eq_supportCount` | Same |

Ordinary compilation of the [source](formal/ResearchPhysicalTraceJoin/GeneralInverseSupport.lean) passed in 88.69 seconds; the full assumption audit passed in 74.75 seconds. The [receipt](attempt-01/verification.json) records 4 complete headline dependency closures and the loaded object hashes. Only `propext`, `Classical.choice` and `Quot.sound` occur. The compiler and reused dependencies remain trusted; this is separate from default-target Linux or Comparator verification. See the [consolidated AI source review](../physical-trace-general-terminal-law/AI-SOURCE-REVIEW.md) and [composed ideal output law](../physical-trace-general-terminal-law/). No new complete sampler or runtime exponent is claimed.

Prepare the pinned Lean4.34.1 compiler and the dependency objects named by the imports, including `ResearchAudit.EnvironmentAudit`, then run:

```sh
LEAN_PATH=<prepared-object-roots> bash REPRODUCE.sh /absolute/path/to/new-output-directory
```

The script compiles this module and audits its loaded environment; it downloads or rebuilds no dependencies. Saved source and compressed audit bytes are unchanged. Public diagnostic paths are projected. [Attempt history](attempts.json) preserves each actual failed compiler or audit stage and dependency preflight.
