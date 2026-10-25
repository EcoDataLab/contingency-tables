# Literal matrix-list zero restoration

23 October 2026. The [Lean module](formal/ResearchPhysicalTraceJoin/ZeroMarginMatrix.lean), `ResearchPhysicalTraceJoin.ZeroMarginMatrix`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

`restoreZeroMarginMatrix` is an ordinary total list function. It computes each
positive original position's rank in `largeIndices (1, xs)`, reads the reduced
matrix at those ranks, and inserts zero at every removed row or column.
Its definition does not invoke a table equivalence or select a feasible table.

| English claim | Lean statement | Hypotheses |
|---|---|---|
| The computed rank equals the inverse ordered-index correspondence | `retainedRank_at_positive` | A positive original margin position |
| Literal list output equals the checked table zero-restoration code | `restoreZeroMarginMatrix_code` | The input is the code of an actual filtered table |
| Every output row has the original column-list length | `restoreZeroMarginMatrix_row_length` | Any supplied matrix list; valid original row index |

The outer output length also equals the original row-list length, including
empty inputs. Repeated margin values retain distinct positions. Default reads
make the function total on malformed codes, but no feasibility or accuracy is
claimed for such inputs. The correspondence connects it to the exact uniform/TV
transport in [the ordered-list packet](../physical-trace-zero-margin-lists/).
Encoded realization and charged costs remain separate.
## Evidence and replay

Ordinary Lean compilation passed in 118.59 seconds;
the compiled-environment audit passed in 207.69 seconds. The
[receipt](attempt-01/verification.json) binds the source, compiled object,
all module declarations and 3 complete headline dependency closures.
Only `propext`, `Classical.choice` and `Quot.sound` occur. The dependency
objects match the recorded accepted or newly compiled input hashes.

The pinned compiler and reused baseline objects remain trusted. This is
separate from the historical default-target Linux build and strict Comparator
task. [AI source review](AI-SOURCE-REVIEW.md) is not human review or independent
kernel verification. Failed compiler attempts are retained when present;
the [scope check](attempt-01/scope-check.json) and [proof diff](attempt-01/proof-only.diff)
record proof repairs. Source and compressed audit bytes are unchanged;
public diagnostic paths and trailing whitespace are projected.

Prepare the pinned Lean compiler and the dependency objects named by this
module's imports, including `ResearchAudit.EnvironmentAudit`, then run:

```sh
LEAN_PATH=<prepared-object-roots> bash REPRODUCE.sh /absolute/path/to/new-output-directory
```

The script compiles this additive module and audits its loaded environment.
It downloads or rebuilds no dependencies. The script is syntax-checked; the
saved run used the same source and compiler options. The claims-ledger
validator checks the saved source, statements, closures and object inventory.
