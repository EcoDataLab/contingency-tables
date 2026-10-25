# Incoming rational-clock acceptance step

23 October 2026. The [Lean module](formal/ResearchRationalClockStep/Step.lean), `ResearchRationalClockStep.Step`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

At a fixed actual defect `x`, the step splits a fair word into a
capped rational-clock proposal and a frozen completion draw. With
`Q = 4p−3`, it reserves exactly

```
N·clog₂(2Q) + q_x(h)
```

bits. The completion margins and exact completion width always belong to
the **source** `x`, including when the proposal selects a balanced target.
The literal list `translationValid` test accepts the proposed state or
holds at `x`. Missing proposals, accepted hold slots, exhaustion and failed
translation tests all hold. Accepted balanced outputs are retained in the
full physical state space for a later exit step.

The ideal comparison uses the rational-clock proposal law and a uniform
source completion. The bound is

```
TV(actual incoming step, ideal incoming step) ≤ 2^(−N) + 2^(−h).
```

For a target `y ≠ x`, equal original totals identify its ideal mass as

```
if adjacent(x,y): acceptedCount(x,y) / [2Q·blockCount(x)],
otherwise:       0.
```

The real-valued form is `referenceConductance(x,y) / [2Q·defectWeight(x)]`
at the computed reference pair. Source holding follows from the normalized
law and includes all rejections; the off-diagonal formula is not applied
to `y=x`.

| English claim | Lean statement | Explicit hypotheses |
|---|---|---|
| A normalized arbitrary proposal law has the stated off-diagonal acceptance mass. | `decisionBind_mass_ne` | Finite spaces; supplied completion law; distinct source and target. |
| The literal fair-word/list test has the source-oracle bind law. | `incomingLaw_eq` | Actual defect `x`; both computed large-line lists nonempty; arbitrary natural `U,L,N,h`. |
| Clock and completion errors add before later exits. | `incomingLaw_accuracy` | The literal-law hypotheses and `p ≥ 2`; no equal-total premise is needed for this constructed-law comparison. |
| The ideal off-diagonal mass has the exact rational-clock accepted-count formula. | `idealIncomingLaw_mass_ne` | Equal original totals; `p ≥ 2`; both large-line lists nonempty; `x ≠ y`. |
| Its real denominator is the source defect weight. | `idealIncomingLaw_mass_ne_cast` | The same off-diagonal hypotheses. |

Original margins may contain zeros. No padding lower bound is added for
this acceptance interface. The proof uses only this fixed source's two
independent word segments; it assumes neither equal completion widths
across states nor an adaptive outer word-bank law.

The incoming step is not yet the canonical defect-only transition: accepted
balanced outputs still need their weighted exits. Composition of these
interfaces, state-dependent error accounting, adaptive freshness and outer
caps, initialization, mixing, output correction, degenerate branches and
encoded costs remain open here. No new full-sampler theorem, runtime
exponent or inverse-gap bound is claimed.

## Evidence and replay

Ordinary Lean compilation passed in 107.36 seconds;
the compiled-environment audit passed in 162.46 seconds. The
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
