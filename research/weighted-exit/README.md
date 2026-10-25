# Conditional weighted first-success law

23 October 2026. This compiled helper supplies the bounded-retry algebra for
a weighted balanced-star exit. It does **not** yet instantiate the actual
physical exit trial or its incoming trace clock.

Let an ideal trial law `q` and decoder `trial` satisfy
`Pr_q(trial=e)=ρ S(e)/w`, where `S≥0`, `ΣS>0` and `w>0`. Put
`a=ρΣS/w` and `ν(e)=S(e)/ΣS`. After `J` independent trials, returning the
first success or a fixed fallback, the ideal output is exactly

```
(1−(1−a)^J) ν + (1−a)^J δ_fallback.
```

If a fixed-word draw has trial-law error at most `δ` from `q`, the existing
`flatRetry` on a uniform bank of exactly `J*k` bits has TV error at most
`(1−a)^J + Jδ` from `ν`. The error comparison occurs before first-success
selection; it does not divide `δ` by a success probability. A positive
success lower bound must still be proved to select a useful retry budget.

The [compiled module](formal/ResearchWeightedExit/FirstSuccess.lean) is
`ResearchWeightedExit.FirstSuccess`, namespace `Math115.WeightedExit`.

| English claim | Lean statement | Hypotheses |
|---|---|---|
| First success gives the exact target/fallback mixture for any rational target law. | `weighted_retry_mass` | Finite spaces; ideal successful masses equal `a*target.mass`; supplied fallback; any natural `J`. |
| The same identity holds for normalized star weights. | `star_retry_mass` | `S≥0`, `ΣS>0`, `w>0`; ideal successful masses equal `ρS(e)/w`; supplied fallback. |
| Approximate independent trials incur failure probability plus `Jδ`. | `approximate_weighted_retry_variation` | The target-success identity and one-trial TV bound `≤δ`. |
| The existing fixed-word retry realizes that bound on exactly `J*k` fair bits. | `flat_star_retry_variation` | Supplied `k`-bit draw and decoder, ideal star-success identity, one-trial TV bound, positive star total and `w`, supplied fallback. |

`S` is a proof parameter. The retry routine takes only the supplied draw,
decoder and fallback; this helper introduces no requirement to compute star
conductances. A caller's own draw/decoder implementation remains its own
obligation. Individual weights may vanish, and `J=0` is covered. Zero total
star mass is outside the normalized target and needs a separate physical case.

## Remaining physical interface

The [physical one-trial packet](../physical-star-trial/) now proves that the
actual proposal plus the [checked list acceptance test](../listed-acceptance/)
has ideal successful mass `ρS(b,e)/w(b)`, and derives trial TV≤2^-h from the
physical completion adapter. The [physical retry](../physical-star-retry/)
and [explicit local schedule](../physical-star-budget/) now compile too,
including entering-edge success bounds and zero-star handling.
The completion-word width is fixed at that particular `b`; this does not
prove adaptive freshness or a common reservation across different states.

The old dyadic proposal rate cancels from the ideal successful exit law.
It does not thereby become the incoming defect trace rate `1/[2(4p−3)]`.
A fixed-length uniform fair-word event has dyadic probability, so that
generally non-dyadic coin cannot simply be identified with the old program.
Bounded rational rejection with error accounting, or an appropriate proved
dyadic trace comparison, is still needed. This observation is a source-level
interface diagnosis, not a new Lean clock theorem or an impossibility claim
about the complete transition kernel.

The helper reuses `retryLaw_mass`, `retryLaw_variation` and `flatRetry_law`.
Upstream also has `ExactIntegerChoice.retryIntegerLaw_some` for explicitly
supplied integer weights; using it directly would require obtaining those
weights. The physical one-trial construction establishes the successful-mass identity
through proposal and completion acceptance; composing its bounded retries
remains separate.

## Verification and replay

Ordinary Lean 4.34.1 compilation passed in 25.06 seconds; the environment
audit passed in 79.01 seconds. Its [receipt](attempt-02/verification.json)
binds all 18 module declarations, including 17 theorem-kind entries, and
three complete headline closures of 6,564, 6,780 and 7,604 declarations.
Only `propext`, `Classical.choice` and `Quot.sound` occur. The final closure
contains the existing executable `flatRetry_law`, `retryLaw_variation`,
weighted normalization and mixture identity. Reused object hashes match
accepted receipts. Compiler and imported objects remain trusted.

The initial typeclass failure is preserved. The repair derives `Nonempty D`
from the existing fallback within the proof and removes an unreachable
tactic; no theorem statement or hypothesis changes. The successful run's
`letI` style warning remains visible. Source and compressed audit bytes are
unchanged; public diagnostic paths and trailing whitespace are projected.
No independent review, default-target rebuild or Comparator run is claimed.

Prepare the pinned compiler and dependency objects for
`Math115.CompletionBooleanRetry` and `ResearchAudit.EnvironmentAudit`, then:

```sh
LEAN_PATH=<prepared-object-roots> bash REPRODUCE.sh /absolute/path/to/new-output-directory
```

The script compiles only this helper and runs the existing environment audit;
it downloads or rebuilds no dependencies. It was syntax-checked. The saved
run used the same options and identical source. The repository claims-ledger
validator replays the source, types, complete closures and object inventory.
