# An actual empty-defect initialization obstruction

23 October 2026. The [Lean module](formal/ResearchPhysicalTraceJoin/InitializationObstruction.lean), `ResearchPhysicalTraceJoin.InitializationObstruction`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

The defect-walk results require a supplied actual starting defect. The
remaining scale and margin hypotheses alone do not guarantee that one
exists. The module proves an obstruction in the actual physical state
space, rather than only in an abstract support graph.

The general hypothesis is

```
firstPaperSmall(r,c,U,i,j) = true  implies  r_i = 0.
```

For every positive-weight physical state, the original residual row test
gives `smallRow(X,i) ≤ r_i`. Every small entry in a zero-margin row must
therefore vanish. An actual single defect requires a strictly positive
small entry at its positive defect cell. These facts exclude every actual
defect under the displayed hypothesis, for arbitrary natural `U,L`.

The concrete fixture is

```
r = [0,4,4],   c = [4,4],   U = 2,   L = 7.
```

Its original totals both equal eight. Its computed large-row indices are
`[1,2]` and large-column indices are `[0,1]`, so both lists are nonempty.
The two cells in row zero are small, proving the required small-cell
count is at least two. Every small cell belongs to that zero-margin row,
so the actual defect type is empty despite those conditions.

| English claim | Lean statement | Explicit hypotheses |
|---|---|---|
| Small entries in zero-margin rows vanish in every actual physical state. | `actual_small_entry_zero_of_row_zero` | Actual positive-weight state; small-cell predicate; original row margin zero; arbitrary `U,L`. |
| If all small cells lie in zero-margin rows, the actual defect type is empty. | `defects_isEmpty_of_zero_small_rows` | The displayed mask-to-zero-row hypothesis; no scale lower bound, large-list, total-equality or margin-positivity premise. |
| The fixture has equal totals and two nonempty computed large lists. | `obstruction_equal_totals`, `obstruction_large_rows`, `obstruction_large_columns`, `obstruction_both_large` | Concrete margins and `U=2`. |
| The fixture has at least two small cells, all in zero-margin rows. | `obstruction_two_small_cells`, `obstruction_small_rows_zero` | Concrete margins and `U=2`; cell count proved by an injection from `Fin 2`. |
| The fixture has no actual defect that could initialize the walk. | `obstruction_defects_isEmpty`, `obstruction_no_defect_start` | Concrete margins, `U=2,L=7`. |

This obstruction preserves the supplied-start hypothesis in the existing
defect-walk interface. It does not rule out other initialization methods
on nonempty supports, add a sampler branch for empty support, or identify
a uniform original-table output law. No runtime claim is supplied.

## Separate finite counts

The [bounded reference enumeration](CHECK_COUNTS.py) confirms one balanced
physical state, zero defects and 19 completions for the 3-by-2 fixture.
Its large 2-by-2 block has row and column totals 18, so its matrices are
`[[a,18-a],[18-a,a]]` for a=0,...,18. The five original tables have the
same form with 4 replacing 18 and a zero first row. A smaller 2-by-2
fixture r=[0,4], c=[2,2] has zero defects and a unique completion.

These counts are [exact finite Python results](counts.json), separate from
the Lean statements proving branch conditions and emptiness. Reproduce:

```sh
python3 research/physical-trace-initialization-obstruction/CHECK_COUNTS.py
```

## Evidence and replay

Ordinary Lean compilation passed in 114.21 seconds;
the compiled-environment audit passed in 155.61 seconds. The
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
