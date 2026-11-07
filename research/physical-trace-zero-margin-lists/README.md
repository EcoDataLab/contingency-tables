# Ordered positive-margin lists

23 October 2026. The [Lean module](formal/ResearchPhysicalTraceJoin/ZeroMarginLists.lean), `ResearchPhysicalTraceJoin.ZeroMarginLists`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

`positiveMargins` is literal stable filtering by positivity. The retained index
list reuses `largeIndices (1, xs)`, so repeated margin values remain distinct
positions. Its explicit ordered equivalence connects the filtered lists to the
[zero-margin table theorem](../physical-trace-zero-margins/).

| English claim | Lean statement | Hypotheses |
|---|---|---|
| Retained positions remain in strict original order | `positiveIndexEquiv_strictMono` | Any natural margin list |
| The filtered value equals its retained original value | `filteredMargin_at_retained` | A valid filtered index |
| Restoration reinserts zero rows and columns at their original positions | `zeroMarginListEquiv_extend_entry` | A table with the filtered margins |
| Restoration preserves error relative to the correct uniform table law exactly | `restoreZeroMarginListsLaw_uniform_variation` | Equal original totals; any rational law on filtered tables |

Both total sums are preserved. Empty lists, zero totals and repeated values are
included. The table bijection needs no equal-total premise; uniform-law results
use equal totals to derive nonempty table spaces.

[Matrix-list restoration](../physical-trace-zero-margin-matrix/) supplies the
literal output function. [Reduced preparation](../physical-trace-zero-margin-preparation/)
connects these lists to recomputed physical scales and the reference schedule.
This packet alone does not select a branch, construct a defect, or supply costs.
## Evidence and replay

Ordinary Lean compilation passed in 69.06 seconds;
the compiled-environment audit passed in 132.68 seconds. The
[receipt](attempt-02/verification.json) binds the source, compiled object,
all module declarations and 4 complete headline dependency closures.
Only `propext`, `Classical.choice` and `Quot.sound` occur. The dependency
objects match the recorded accepted or newly compiled input hashes.

The pinned compiler and reused baseline objects remain trusted. This is
separate from the historical default-target Linux build and strict Comparator
task. [AI source review](AI-SOURCE-REVIEW.md) is not human review or independent
kernel verification. Failed compiler attempts are retained when present;
the [scope check](attempt-02/scope-check.json) and [proof diff](attempt-02/proof-only.diff)
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
