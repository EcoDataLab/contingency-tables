# Actual local experiments approximate the identified trace row

23 October 2026. The [Lean module](formal/ResearchPhysicalTraceJoin/Actual.lean), `ResearchPhysicalTraceJoin.Actual`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

`actualJoinedLaw` binds the literal incoming experiment to the bounded exit law at the reached state. Defect arrivals remain unchanged; balanced arrivals use the checked physical retry and fallback to the original source. The law never computes symbolic star conductances.

The generic `variation_bind_ideal_support` comparison charges exit errors using the ideal incoming law. Only its positive support requires a uniform exit bound. For a balanced state in that support, the exact incoming mass implies adjacency to the source defect; symmetry and L≥7 supply the checked exit bound. Actual mass outside ideal support is charged once, through the incoming TV error.

```
TV(actualJoinedLaw, idealJoinedLaw)
  ≤ 2^−N + 2^−hIn + (1−rho/2)^J + J·2^−hExit.
```

`actualJoinedLaw_accuracy` proves this estimate. `scheduledJoinedLaw_accuracy` sets N=hIn=t+2 and uses the explicit physical exit schedule, giving TV≤2^−t. The ideal law is identified with the entire canonical computed-reference trace row in the preceding module.

The margin totals must agree, both computed large-line lists must be nonempty, p≥2, L≥7 and a source actual defect is supplied. There is no positive-original-margin or U lower-bound premise. Zero and unreachable stars are retained. Each local exit has its own fresh state-dependent word bank; this module does not yet identify one common input word or an encoded outer machine.

The [word](../physical-trace-word/) and [width](../physical-trace-width/)
packets now realize this law on a fixed fair-bit input.

## Evidence and replay

Ordinary Lean compilation passed in 51.88 seconds;
the compiled-environment audit passed in 196.71 seconds. The
[receipt](attempt-02/verification.json) binds the source, compiled object,
all module declarations and 3 complete headline dependency closures.
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
