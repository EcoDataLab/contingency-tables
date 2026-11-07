# One common fresh word realizes the joined transition

23 October 2026. The [Lean module](formal/ResearchPhysicalTraceJoin/Word.lean), `ResearchPhysicalTraceJoin.Word`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

`joinedWord` splits exactly A_d+W fair bits. The first block runs the literal incoming proposal, frozen source completion and list acceptance. The reached state then selects a prefix from the independent second block. A balanced arrival uses its exact J·[s+q_b(hExit)]-bit retry; a defect arrival ignores that block.

The common W is fixed before the first draw and must bound the exit width for every balanced state, including states reached only by the approximate incoming law. The upstream prefix-word law preserves each exit distribution exactly. `joinedWord_law` identifies the resulting word law with `actualJoinedLaw`, without adding error or substituting an ideal draw. `scheduledJoinedWord_accuracy` transfers the already derived TV≤2^−t bound.

The exact identity requires the supplied width bound, source defect and nonempty computed large-line lists. Accuracy additionally requires equal total margins, p≥2 and L≥7. Original zero margins and arbitrary natural U remain allowed. The generic `freshPrefixDraw_law` states the same independent-prefix construction for any finite state-dependent draw family.

This is a one-step realization conditional on W. An explicit numerical width, repeated-walk reservation and encoded costs remain separate; no efficient maximum enumeration or runtime bound is asserted.

The [uniform-width packet](../physical-trace-width/) discharges the supplied
width premise with an explicit backend bound.

## Evidence and replay

Ordinary Lean compilation passed in 91.79 seconds;
the compiled-environment audit passed in 88.79 seconds. The
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
