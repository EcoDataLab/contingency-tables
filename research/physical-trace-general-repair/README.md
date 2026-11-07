# Completion-retaining repair of the actual defect joint

24 October 2026. The [Lean module](formal/ResearchPhysicalTraceJoin/GeneralRepair.lean), `ResearchPhysicalTraceJoin.GeneralRepair`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

The [successor correction packet](../physical-trace-general-terminal-law/) now supplies the exact inverse count and ideal accepted-output law. The scope below records this repair-map checkpoint.

The input is the exact `DefectJoint` returned by the checked
[terminal draw](../physical-trace-terminal/). Canonical defect labels select
the existing full-view repair. The sampled dense completion stays present:
every dense entry is unchanged except a large crossing, which gains one.
The repaired matrix has the padded margins and satisfies the original
small-row and small-column constraints. Its actual source capacities are
derived from those constraints.

The same matrix is packaged into the existing balanced joint. After testing
every large entry against `L`, `terminalRepairOutput` removes precisely the
large-cell padding and returns a `Table r c`. Re-padding recovers the actual
repaired matrix. This defines the mathematical success-output map; it does
not yet give an executable list program or an accepted-output law.

| English claim | Lean statement | Hypotheses |
|---|---|---|
| Ordered labels and the repaired full table uniquely determine the actual input pair | `terminalRepair_labels_table_injective` | Actual defect/completion pairs |
| Dense entries retain their sampled values, with exactly one increment at a large crossing | `terminalRepairedTable_large_entry` | Actual input pair; designated entry is large |
| The balanced joint contains exactly the completion-retaining repaired matrix | `terminalRepairedJoint_table` | Actual input pair |
| Successful output subtracts padding only on large cells | `terminalRepairOutput_entry` | Actual repaired matrix passes every large-entry padding test |
| The returned ordinary table corresponds to exactly that successful repaired joint | `terminalRepairOutput_successfulJoint` | The same actual success test |

The map works at arbitrary natural `U,L` whenever an actual input pair exists;
it does not need positive margins or a new count/accuracy premise. Positive
reduced margins and nontrivial small geometry will be needed for the separate
acceptance lower bound. Fixed-label recovery is only on the actual repaired
image; it does not establish the feasibility or number of inverse pairs for
every target table.

The remaining correction needs the exact successful inverse-fibre formula
`ell_D`, the bound `0<c0<=ell_D`, and an ideal rational acceptance rule with probability
`c0/ell_D`, plus a bounded dyadic coin and its rounding-error law. Its success
bound must then be composed with the existing
new-scale padded-count theorem and the checked defect-joint schedule.
Initialization, remaining branches, zero restoration, outer retries and
encoded costs still require assembly. No complete sampler or runtime
exponent changes in this packet.

## Evidence and replay

Ordinary Lean compilation passed in 73.56 seconds;
the compiled-environment audit passed in 197.93 seconds. The
[receipt](attempt-02/verification.json) binds the source, compiled object,
all module declarations and 5 complete headline dependency closures.
Only `propext`, `Classical.choice` and `Quot.sound` occur. The dependency
objects match the recorded accepted or newly compiled input hashes.

The pinned compiler and reused baseline objects remain trusted. This is
separate from the historical default-target Linux build and strict Comparator
task. [AI source review](AI-SOURCE-REVIEW.md) is not human review or independent
kernel verification. Failed compiler attempts are retained when present;
the [scope check](attempt-02/scope-check.json) and [proof diff](attempt-02/proof-only.diff)
record proof repairs and the reviewed name qualification. Source and compressed audit bytes are unchanged;
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
