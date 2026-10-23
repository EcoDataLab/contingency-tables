# Concrete bounded-exit schedule

23 October 2026. The [Lean module](formal/ResearchPhysicalStarBudget/Schedule.lean), `ResearchPhysicalStarBudget.Schedule`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

For target accuracy index `t`, the local balanced-star exit uses

```
s = clog₂(32d²)
A = 2·2^s
J = A(t+2)
h = t+2+clog₂ J.
```

The source-backed success bound is `ρ/2 = 1/A`. A finite geometric-sum argument proves `(1−1/A)^A ≤ 1/2`. Thus retry exhaustion contributes at most `2^−(t+2)`, and the chosen completion precision bounds `J·2^−h` by the same amount. The total exit error is at most `2^−(t+1)`.

The exact reserved bank is `J·[s+q_b(h)]` bits at this fixed balanced source. Unused bits are included. The schedule does not require computing the star conductances.

| English claim | Lean statement | Hypotheses |
|---|---|---|
| A block of A trials halves the failure allowance. | `reciprocal_block` | Natural `A>0`. |
| Retry and completion errors fit the explicit local budget. | `exit_budget` | Natural dimension parameter `d` and requested accuracy index `t`. |
| The actual physical exit obeys that budget on its exact bit bank. | `scheduledExit_variation` | Equal-total natural margins; both computed large-line lists nonempty; `L≥7`; actual balanced source and adjacent entering defect; arbitrary natural `U,t`. |

Original zero margins are allowed. The adjacency is written from the balanced source to the entering defect; physical symmetry permits reversing an incoming edge. The schedule reserves half the requested TV allowance for other errors. It does not allocate those other errors or prove a complete trace walk, adaptive global bank, machine cost or new inverse-gap/runtime exponent.
## Evidence and replay

Ordinary Lean compilation passed in 52.75 seconds;
the compiled-environment audit passed in 127.93 seconds. The
[receipt](attempt-02/verification.json) binds the source, compiled object,
all module declarations and 2 complete headline dependency closures.
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
