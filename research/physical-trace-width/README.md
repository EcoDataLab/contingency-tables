# A uniform-width physical trace step

23 October 2026. The [Lean module](formal/ResearchPhysicalTraceJoin/Width.lean), `ResearchPhysicalTraceJoin.Width`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

Let `D = 10+(m+1)(n+1)`, `M = Σ_i r_i`, and let `R,C` count the original
margins at least `U`. The standalone completion-width bound supplies

```
Mstar = M + LRC,
C0 = 12672000000 · 37^62,
F(h) = C0 · [D + clog₂(Mstar+2) + h + 3]^85,
q_x(h) ≤ F(h)                         for every actual physical state x.
```

The coefficient and exponent come from the existing frozen sampler's
reserved-bit theorem. The source gives separate proofs for the actual residual
total, selected request dimensions and logarithmic input-size inequalities;
the bound does not enumerate a maximum over physical states.

Write `Q = 4p−3`, `k = clog₂(2Q)` and `s = clog₂(32D²)`. For clock attempts
`N`, incoming completion precision `hIn`, exit attempts `J` and exit
completion precision `hExit`, define

```
Wexit = J · [s + F(hExit)],
B = N·k + F(hIn) + Wexit.
```

`uniformStepWidth` is exactly `B`. It depends on the margins and chosen
parameters, not the starting defect. At a starting defect `d`, the existing
step needs the prefix of length `N·k + q_d(hIn) + Wexit`, which is at most
`B`. The new map takes that prefix and ignores the remaining suffix.
Within the prefix, the literal incoming proposal/draw/list test and the
fresh exit block remain disjoint. A reached balanced state uses only the
needed prefix of the exit block; a defect output ignores that block.

| English claim | Lean statement | Explicit hypotheses |
|---|---|---|
| The common exit block covers every balanced exit bank. | `balancedExitWidth_le_common` | Both computed large-line lists nonempty; actual balanced state; arbitrary natural `U,L,J,hExit`. |
| Every starting defect's exact step width is at most `B`. | `joinedWidth_le_uniform` | Both large-line lists nonempty; actual defect; chosen natural parameters. |
| The uniform-width word has exactly the existing actual joined law. | `uniformJoinedWord_law` | The same local hypotheses; uniform word of exactly `B` bits. |
| Padding adds no error to the joined-step approximation. | `uniformJoinedWord_accuracy` | Equal original totals; `L ≥ 7`; `p ≥ 2`; both large-line lists nonempty; actual source defect. |
| The concrete local schedule gives TV at most `2⁻ᵗ` on a width shared by every source defect. | `scheduledUniformJoinedWord_accuracy` | The accuracy hypotheses; `N=hIn=t+2`, with `J` and `hExit` from the physical exit schedule. |

The generic error bound remains

```
2^(−N) + 2^(−hIn) + (1−ρ/2)^J + J·2^(−hExit),
ρ = 2^(−clog₂(32D²)).
```

The completion-width bound and exact padded law retain arbitrary `U,L` and
permit zero original margins. The starting defect is fixed before the fresh
`B`-bit word is drawn. This is a uniform one-step realization; repeated-walk
execution, its fresh-bank law and total reservation are checked in the
[walk packet](../physical-trace-walk/).
No extracted machine, encoded copying cost, machine-time bound, complete
sampler or new inverse-gap/runtime exponent is claimed.

## Evidence and replay

Ordinary Lean compilation passed in 38.77 seconds;
the compiled-environment audit passed in 104.80 seconds. The
[receipt](attempt-01/verification.json) binds the source, compiled object,
all module declarations and 4 complete headline dependency closures.
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
