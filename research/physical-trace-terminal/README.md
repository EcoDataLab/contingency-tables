# Terminal completion of the physical defect walk

23 October 2026. The [Lean module](formal/ResearchPhysicalTraceJoin/Terminal.lean), `ResearchPhysicalTraceJoin.Terminal`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

The output retains both the reached defect and a physical completion of
that same defect:

```
DefectJoint = Sigma d : DefectVertices, Fibre(d).
π_D(d) = card(Fibre(d)) / Σ_defects e card(Fibre(e)).
```

Drawing a defect from `π_D` and then a uniform member of its fibre gives
the uniform distribution on `DefectJoint`. The defect label remains part
of the output; this identity does not identify a uniform distribution on
original tables.

The literal program splits its reserved input into two disjoint banks.
The first runs the existing bounded defect walk. The second is a fresh
terminal bank of width `F(hTerm) = uniformCompletionBits(r,c,U,L,hTerm)`.
Only a prefix of that second bank is supplied to the frozen legacy
completion program at the reached defect. The proved uniform width bound
covers every reached state. The exact reserved bank is

```
T * uniformStepWidth(r,c,U,L,N,hIn,J,hExit) + F(hTerm).
```

The exact word law is the dependent joint of the actual joined-walk law
and the actual frozen completion laws. It reuses the existing independent
dependent-product and prefix-padding identities. No approximation is added
by either word conversion.

For the existing schedule

```
N = hIn = t+2,
J = attempts(D,t),   hExit = precision(D,t),
D = 10+(m+1)(n+1),
```

the total-variation bound is

```
TV(literal terminal joint, uniform DefectJoint)
  ≤ T·2^(−t) + Bmass·exp(−T/K) + 2^(−hTerm),
K = 32 p³·aggregateCT(r,c,U),
Bmass = [Σ_i r_i + D·L + U + 3]^(2D),
p = card(Cells(firstPaperSmall(r,c,U))).
```

| English claim | Lean statement | Explicit hypotheses |
|---|---|---|
| Count-weighted defects followed by uniform same-defect fibres give a uniform labelled joint. | `defectStationaryJointLaw_uniform` | Nonempty defect support; no mixing or padding lower bound. |
| The fixed terminal prefix preserves the actual frozen completion law. | `terminalCompletion_law` | Both computed large-line lists nonempty; supplied reached defect; arbitrary natural `U,L,hTerm`. |
| The fresh terminal completion is within `2^(−hTerm)` of its uniform fibre. | `terminalCompletion_accuracy` | The same hypotheses; accuracy comes from the existing frozen draw theorem. |
| The literal split word realizes the actual dependent joint law. | `terminalJoinedWord_law` | Both large-line lists nonempty; supplied starting defect; natural walk and precision parameters. |
| The terminal joint error is at most base-law error plus terminal error. | `terminalJoinedLaw_variation` | Nonempty defect support; both large-line lists nonempty; no conditioning or success-probability premise. |
| The scheduled literal terminal joint satisfies the displayed bound. | `scheduledTerminalJoinedWord_accuracy` | Equal original totals; `U ≥ 2`; `L ≥ 7`; `p ≥ 2`; both large-line lists nonempty; nonempty defects and supplied starting defect. |

Original margins may contain zeros. The supplied start is fixed before
the fresh input word. `T=0` remains within the finite-word definitions.
The displayed length is reserved input, not bits inspected or machine
time. The bound has free `T,t,hTerm`; the [explicit schedule](../physical-trace-schedule/)
now chooses them for any natural accuracy request. This theorem does not assert exact convergence
of the fixed-precision actual walk as `T` grows. No initialization,
repair, original-table uniformity, output correction, whole-sampler restart
or runtime claim is supplied.

## Evidence and replay

Ordinary Lean compilation passed in 74.32 seconds;
the compiled-environment audit passed in 270.86 seconds. The
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
