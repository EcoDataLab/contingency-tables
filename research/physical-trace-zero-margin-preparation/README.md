# Filtered-list preparation and the finite-word reference schedule

23 October 2026. The [Lean module](formal/ResearchPhysicalTraceJoin/ZeroMarginPreparation.lean), `ResearchPhysicalTraceJoin.ZeroMarginPreparation`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

The actual stable [positive-margin lists](../physical-trace-zero-margin-lists/)
feed the [computed scale and branch classifier](../physical-trace-preparation/).
The reference branch then calls the existing
[finite-word schedule](../physical-trace-schedule/) at the reduced dimensions,
recomputed `U=11d(m+n-2)` and `L=7`. Its actual starting defect remains an input.

| English claim | Lean statement | Hypotheses |
|---|---|---|
| At fixed U, each reduced small-cell test is its literal retained original test | `filteredSmallMask_entry` | Any lists, cutoff and retained indices |
| A reference tag supplies the actual reduced dimension, count and computed-list conditions | `positiveTraceReference_conditions` | The computed reference tag |
| The resulting finite-word draw is within 2^-h of uniform on reduced defect/completion pairs | `positiveTraceReferenceWord_accuracy` | Equal original totals, reference tag, actual reduced defect start, natural h |
| A feasible reduced table in the deterministic branch restores to original uniform | `positiveTraceDeterministic_restored_uniform` | Equal totals, deterministic tag, supplied reduced table |
| Stable zero filtering gives the stated retuned fixture | `positiveTraceBranch_retuning_fixture` | The displayed fixed lists |

Cutoff lower bounds, p≥2 and both large lists are derived from preparation,
not supplied independently. Completion accuracy comes from the existing
verified backend. All walk budgets and input widths use the same reduced
data. The supplied start gives the needed nonempty defect space.

The reference output is still a **reduced defect-labelled physical completion
pair**. The ordinary-table restoration theorem cannot yet be applied to that
pair: general repair/acceptance is still required. Initialization, empty support,
the other branch programs, fresh outer retries and encoded costs remain open.
This is no new complete-sampler or runtime exponent claim.
## Evidence and replay

Ordinary Lean compilation passed in 123.92 seconds;
the compiled-environment audit passed in 265.57 seconds. The
[receipt](attempt-02/verification.json) binds the source, compiled object,
all module declarations and 5 complete headline dependency closures.
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
