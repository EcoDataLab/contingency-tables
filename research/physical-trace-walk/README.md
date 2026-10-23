# A fresh finite-word physical trace walk

23 October 2026. The [Lean module](formal/ResearchPhysicalTraceJoin/Walk.lean), `ResearchPhysicalTraceJoin.Walk`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

Fix the margins, cutoff, padding and local step parameters. Let

```
B = N·clog₂(2Q) + F(hIn) + J·[clog₂(32D²) + F(hExit)],
Q = 4p−3.
```

Here `D` is the outer dimension allowance and `F` is the explicit common
completion-word bound. The deterministic walk takes a supplied starting
defect and exactly `T*B` fair bits. The existing word-bank equivalence
partitions them into `T` disjoint `B`-bit words. Each reached defect is
passed to the literal uniform-width joined-step map with the next fresh
block. Sources may depend on earlier blocks; the blocks themselves come
from one uniform word bank.

The exact law is `walkLaw(actualJoinedLaw)`. Its comparison with
the ideal joined walk uses the existing `walkLaw_variation` theorem:

```
E = 2^(−N) + 2^(−hIn) + (1−ρ/2)^J + J·2^(−hExit),
ρ = 2^(−clog₂(32D²)),
TV(actual word walk, ideal joined walk) ≤ T·E.
```

With the local scheduled parameters, the bound is `T·2^(−t)`.

| English claim | Lean statement | Explicit hypotheses |
|---|---|---|
| The existing rectangular-word walk flattens to exactly `T*B` bits. | `flatWordWalk_law` | Finite state space; fixed-width step map; supplied start; any natural `T,B`. |
| The physical word walk has the exact actual joined-walk law. | `joinedWalkWord_law` | Both computed large-line lists nonempty; actual starting defect; fixed natural step parameters and `T`; arbitrary natural `U,L`. |
| Uniform one-step errors add over the walk. | `joinedWalkWord_accuracy` | Equal original totals; `L ≥ 7`; `p ≥ 2`; both large-line lists nonempty; actual starting defect. |
| The local schedule gives error at most `T·2⁻ᵗ`. | `scheduledJoinedWalkWord_accuracy` | The same accuracy hypotheses; `N=hIn=t+2`, scheduled exit attempts and precision. |

The exact law retains zero original margins and includes zero-step and
zero-width cases through the existing equivalence and walk definitions.
Unused padding, holding slots and rejected-trial bits remain in the reserved
bank. No global equality of actual completion widths is assumed.

The initial defect is supplied. This packet does not prove initialization,
mixing from that defect, stationarity, a terminal output correction, retry
of a whole sampling attempt, or the remaining empty/degenerate branches.
It supplies no extracted machine, encoded cost bound, full-sampler theorem
or new inverse-gap/runtime exponent.
The [mixing packet](../physical-trace-mixing/) connects this finite walk to
the computed trace's completion-count stationary law on defects.

## Evidence and replay

Ordinary Lean compilation passed in 44.65 seconds;
the compiled-environment audit passed in 80.64 seconds. The
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
