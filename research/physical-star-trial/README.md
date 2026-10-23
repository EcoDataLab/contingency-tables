# Physical balanced-star trial

23 October 2026. The [Lean module](formal/ResearchPhysicalStar/Trial.lean),
namespace `Math115.PhysicalStarTrial`, compiles and passes its full assumption
audit. This closes the physical one-trial mass and accuracy interface.

The local trial uses the old executable proposal, completion draw and list
acceptance test at a fixed balanced physical state `b`. It reserves exactly
`k = clog₂(32d²) + q_b(h)` fresh fair bits: one segment for the proposal and
one for a completion at the **source** `b`. A defect output is a success;
holds, rejected proposals and balanced outputs are failures.

Its ideal comparison law uses uniform source completions. For a defect `e`,

```
Pr_ideal(success e) = ρ S(b,e) / w(b),
ρ = 2^(−clog₂(32d²)),
TV(actual trial, ideal trial) ≤ 2^(−h).
```

Here `S(b,e)` is the adjacency-filtered accepted completion count and `w(b)`
is the source completion count. The module defines these as exact rational
count expressions and proves their casts equal the computed-reference
trace's conductance and balanced weight. Neither the successful-mass identity
nor the trial accuracy is assumed. Uniform ideal completions define a
comparison law; the actual word algorithm uses the already checked draw.

| English claim | Lean statement | Hypotheses |
|---|---|---|
| The literal list trial has the reference proposal/completion/acceptance law. | `actualStep_law` | Equal-total natural margins; both computed large-line lists nonempty; actual balanced state `b`; arbitrary natural `U,L,h`; uniform word of exactly `k` bits. |
| Each ideal defect mass is `ρS(b,e)/w(b)`. | `idealTrialLaw_mass_some` | Both computed large-line lists nonempty; balanced `b` and defect `e`; arbitrary `U,L`. |
| The count formula is the computed-reference trace's real conductance formula. | `idealTrialLaw_mass_some_cast` | Same local mass hypotheses. |
| Actual and ideal trial laws have TV at most `2⁻ʰ`. | `actualTrialLaw_accuracy` | The executable-law hypotheses; accuracy derived from the frozen completion draw. |

The held balanced state projects to `none`, and a defect output has a unique
preimage. Equal-width completions across different states, padding at least
seven, positive original margins and positive total star mass are unnecessary
for this one-trial result. Both selected large-line lists must be nonempty;
singleton selected blocks are permitted. This is a typed finite-word law,
not a newly encoded complete outer machine.

## Remaining connection

The [weighted first-success helper](../weighted-exit/) can next be specialized
using this physical mass formula and accuracy, after supplying count
nonnegativity, a positive source weight and positive total star mass. The
retry bank must contain exactly `J*k` fresh bits at this fixed `b`. A useful
success lower bound and the zero-star case remain separate obligations.

The dyadic proposal rate cancels in the normalized ideal exit law. It does
not identify the incoming rational clock `1/[2(4p−3)]` in the canonical
trace. Clock implementation and its error, adaptive freshness across states,
outer caps, initialization, output correction and encoded costs remain open.
No inverse-gap, complete-sampler or runtime exponent changes here.

## Evidence

Ordinary Lean 4.34.1 compilation passed in 95.67 seconds;
the environment audit passed in 222.30 seconds. The
[receipt](attempt-05/verification.json) binds the exact source, compiled
object, all module declarations and four complete headline dependency
closures. Only `propext`, `Classical.choice` and `Quot.sound` occur. The
executable-law and accuracy closures include the checked list correspondence,
computed proposal law and frozen `LatticeSampler.draw_spec`.

The reused object inventory matches earlier accepted receipts. Imports and
the pinned compiler remain trusted; this is not a fresh rebuild of all
baseline dependencies. [Separate AI source review](AI-SOURCE-REVIEW.md)
found no semantic scope error. No human review, independent checker,
default-target rebuild, fresh platform replication or Comparator acceptance
is claimed.

Four failed attempts are preserved: one import-path failure, a missing
namespace and two proof-elaboration timeouts. The successful proof factors
word independence and pointwise acceptance into separate lemmas. All original
statements, mathematical definitions, hypotheses and resource limits remain
unchanged; [the scope check](attempt-05/scope-check.json) and
[proof diff](attempt-05/proof-only.diff) record the repair. Harmless deprecation/style warnings remain in the saved successful
log. Source and compressed audit bytes are unchanged; public diagnostic
paths and trailing whitespace are projected.

## Replay

Prepare the pinned compiler and dependency objects for the listed acceptance,
computed-reference trace, physical proposal, upstream word-completion laws
and environment auditor. Then, from this packet directory:

```sh
LEAN_PATH=<prepared-object-roots> bash REPRODUCE.sh /absolute/path/to/new-output-directory
```

The script merges partial reused namespace roots, compiles this one module
and runs the existing environment audit. It downloads or rebuilds no
dependencies. The script was syntax-checked; the saved successful run used
identical source and compiler options. The repository claims-ledger validator
checks the source, exact types, complete closures and imported-object inventory.
