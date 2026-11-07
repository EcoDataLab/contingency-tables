# Computed trace scales and branch preparation

23 October 2026. The [Lean module](formal/ResearchPhysicalTraceJoin/TracePreparation.lean), `ResearchPhysicalTraceJoin.TracePreparation`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

The list function `traceCutoff` computes `11d(m+n-2)` using
`d=10+(m+1)(n+1)` from its supplied list lengths. The small-cell catalog and
large-row/column lists reuse the existing programs at that exact cutoff.
`traceInputBranch` is a preparation classifier: dimensions at most one come
first, followed by the no-small, unit and reference cases.

| English claim | Lean statement | Hypotheses |
|---|---|---|
| The list cutoff equals the proved shape cutoff | `traceCutoff_ofFn` | Any finite natural margins |
| The reference tag gives precisely the required dimensions, small-cell count and large lists | `traceInputBranch_reference_iff` | Any finite natural margins |
| Beyond the deterministic dimensions, the no-small tag means zero small cells | `traceInputBranch_noSmall_iff` | Any finite natural margins |
| A feasible table in the deterministic dimension branch has the exact uniform law | `deterministicBranch_pointLaw_uniform` | Equal totals, deterministic tag, a supplied feasible table |
| Retuning after zero removal can change the branch | `traceBranch_retuning_fixture` | The displayed fixed lists |

The first-paper mask is a union of full rows and columns. When both dimensions
are at least two, its cell count is zero or at least two, never one.
For `[0,600,600]` by `[600,600]`, the cutoff is 726 and the tag is unit.
After zero removal the cutoff is 418 and the tag is no-small.

These tags do not implement the unit or no-small samplers. The reference tag
does not construct a defect start. Recomputing dimensions can change physical
capacities, masks and budgets; no equality of the old and reduced chains is
claimed. The deterministic law theorem uses a supplied feasible table rather
than constructing an executable output.
## Evidence and replay

Ordinary Lean compilation passed in 80.89 seconds;
the compiled-environment audit passed in 84.73 seconds. The
[receipt](attempt-03/verification.json) binds the source, compiled object,
all module declarations and 5 complete headline dependency closures.
Only `propext`, `Classical.choice` and `Quot.sound` occur. The dependency
objects match the recorded accepted or newly compiled input hashes.

The pinned compiler and reused baseline objects remain trusted. This is
separate from the historical default-target Linux build and strict Comparator
task. [AI source review](AI-SOURCE-REVIEW.md) is not human review or independent
kernel verification. Failed compiler attempts are retained when present;
the [scope check](attempt-03/scope-check.json) and [proof diff](attempt-03/proof-only.diff)
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
