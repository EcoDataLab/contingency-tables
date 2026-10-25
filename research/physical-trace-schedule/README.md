# Explicit accuracy schedule for the physical defect joint

23 October 2026. The [Lean module](formal/ResearchPhysicalTraceJoin/Schedule.lean), `ResearchPhysicalTraceJoin.Schedule`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

The target remains the uniform law on labelled physical completion pairs

```
DefectJoint = Sigma d : DefectVertices, Fibre(d).
```

The starting defect is supplied. For any natural accuracy request `h`, the
program chooses all walk and precision parameters as natural numbers and
derives total variation at most `2^(−h)` for the resulting literal program.
No desired-error bound is added as a hypothesis.

Write `a = smallLineCount(r,U)+smallLineCount(c,U)`,
`p = card(Cells(firstPaperSmall(r,c,U)))`, and `D=10+(m+1)(n+1)`. The schedule is

```
Cnat = U·(U−1) + 4·(a·U²+p·U),
G = 32·p³·Cnat,
base = Σ_i r_i + D·L + U + 3,
ell = h+2 + 2D·clog₂(base),
T = G·ell,
t = h+2 + clog₂(T),
hTerm = h+2.
```

The subtraction in `Cnat` is natural subtraction. The hypothesis `U≥2`
justifies its cast: `(G:Real)` equals the existing aggregate mixing
allowance `32 p³·aggregateCT(r,c,U)` exactly. Positivity is derived from
the existing lower bound on that allowance.

The existing local step schedule is used unchanged at accuracy target
`t`: `N=hIn=t+2`, `J=attempts(D,t)`, and `hExit=precision(D,t)`.
The reserved input width is exactly

```
T * uniformStepWidth(r,c,U,L,t+2,t+2,attempts(D,t),precision(D,t))
  + uniformCompletionBits(r,c,U,L,h+2).
```

Existing exponential and dyadic-charge lemmas give

```
T·2^(−t)                          ≤ 2^(−(h+2)),
base^(2D)·exp(−T/G)               ≤ 2^(−(h+2)),
2^(−hTerm)                        = 2^(−(h+2)).
```

Their sum is at most `¾·2^(−h)`, hence at most the requested `2^(−h)`.
The final theorem instantiates the literal terminal-joint accuracy theorem
with these choices.

| English claim | Lean statement | Explicit hypotheses |
|---|---|---|
| The natural gap count casts exactly to the existing real mixing allowance. | `terminalGapCount_cast` | `U≥2`; actual original-margin small-line and cell counts. |
| Gap count and scheduled walk length are positive. | `terminalGapCount_positive`, `terminalScheduleSteps_positive` | `U≥2`, `p≥2`; natural accuracy request. |
| The chosen walk length pays for the full mass allowance. | `terminalSchedule_mixing_budget` | `U≥2`, `p≥2`; arbitrary natural padding and original margins. |
| Ceiling-log step precision pays for all steps. | `terminalSchedule_step_budget` | Natural schedule parameters; no mixing or error premise. |
| The three scalar errors fit the requested dyadic budget. | `terminalSchedule_error_budget` | `U≥2`, `p≥2`; natural request `h`. |
| The scheduled literal program is within `2^(−h)` of uniform defect-labelled joints. | `terminalScheduleWord_accuracy` | Equal original totals; both computed large-line lists nonempty; `U≥2`, `L≥7`, `p≥2`; nonempty defect support and supplied starting defect. |

Original margins may contain zeros. The schedules are all-natural formulas;
the displayed bank is reserved input, not bits inspected, an extracted
machine cost or a running-time bound. The result does not supply a starting
defect, degenerate branches, repair, original-table uniformity, output
correction or a complete table sampler. No further gap or runtime exponent
is claimed.

## Evidence and replay

Ordinary Lean compilation passed in 56.75 seconds;
the compiled-environment audit passed in 249.83 seconds. The
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
