# Ideal incoming and weighted exit equal the canonical trace

23 October 2026. The [Lean module](formal/ResearchPhysicalTraceJoin/Ideal.lean), `ResearchPhysicalTraceJoin.Ideal`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

The incoming comparison law uses the canonical rational proposal clock and a uniform source completion. A defect arrival is preserved. A balanced arrival follows its conductance-weighted exit; a zero star returns to the supplied source defect. For distinct defects d,e the resulting law has real mass

```
[W(d,e) + sum_b S(b,d) S(b,e)/sum_f S(b,f)] / [2(4p−3) w(d)].
```

`idealJoinedLaw_mass_ne` identifies this with the checked computed-reference trace. `idealJoinedLaw_row` obtains the diagonal from the two laws' normalization, so it identifies the whole row. The same computed reference pair is used throughout; different reference kernels are not equated.

Hypotheses are equal-total natural margins, both computed large-line lists nonempty, p≥2 small cells and a supplied actual defect. The supplied defect provides nonempty support. This ideal identity needs neither L≥7 nor a positive-star premise: zero-star terms vanish and the fallback has no off-diagonal mass. Cutoff and padding remain arbitrary natural numbers; original zero margins are permitted.

This is an ideal law identity. Approximate incoming draws, bounded exits, a common finite word, global walk and encoded costs require their separate interfaces. It changes no inverse-gap or runtime exponent.

The [actual composition](../physical-trace-actual/) and
[finite-word walk](../physical-trace-walk/) provide the following checked
interfaces.

## Evidence and replay

Ordinary Lean compilation passed in 94.77 seconds;
the compiled-environment audit passed in 126.64 seconds. The
[receipt](attempt-03/verification.json) binds the source, compiled object,
all module declarations and 2 complete headline dependency closures.
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
