# Bounded physical balanced-star exit

23 October 2026. The [Lean module](formal/ResearchPhysicalStarRetry/Exit.lean), `ResearchPhysicalStarRetry.Exit`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

At a fixed balanced physical state `b`, write `S(b,e)` for the accepted
conductance to defect `e`, `w(b)` for the source completion count, and
`s_b = Σ_e S(b,e)`. The existing physical trial uses

```
ρ = 2^(−clog₂(32d²)),
k_b(h) = clog₂(32d²) + q_b(h),
a_b = ρ s_b / w(b),
ν_b(e) = S(b,e) / s_b                 (s_b > 0).
```

The exit applies the existing `flatRetry` to that trial on exactly
`J*k_b(h)` fair bits. It returns the first accepted defect or a supplied
defect fallback. An accepted result equal to the fallback is still a
success. The ideal law and actual error bound are

```
ideal output = (1−(1−a_b)^J) ν_b + (1−a_b)^J δ_fallback,
TV(actual output, ν_b) ≤ (1−a_b)^J + J·2^(−h).
```

For `L ≥ 7`, an actual edge from `b` to a supplied entering defect gives
`s_b ≥ w(b)/2` and `a_b ≥ ρ/2`. The specialized bound is therefore
`(1−ρ/2)^J + J·2^(−h)`. The source-directed acceptance theorem supplies
the half-weight bound; no target/source weight-ratio premise is introduced.
Physical adjacency is symmetric, so an entering edge can be reversed to
this source orientation.

| English claim | Lean statement | Explicit hypotheses |
|---|---|---|
| Counts are nonnegative and the actual source weight is positive. | `crossRat_nonnegative`, `weightRat_pos` | Actual balanced `b`; both computed large-line lists nonempty; arbitrary natural `U,L`. |
| Rational normalized weights equal the computed-reference real exit weights. | `targetLaw_mass_cast` | The same local data and `s_b > 0`. |
| The ideal bounded exit has the exact target/fallback mixture. | `idealExit_mass` | Positive star total; supplied defect fallback; any natural `J`. |
| The actual fixed-width bank has the stated TV bound. | `flatExit_variation` | Equal original totals; fixed `b,h`; positive star total; supplied fallback; any `J`. |
| An actual entering edge supplies a success lower bound. | `starMass_ge_half_weight`, `successProbability_ge_half_proposal` | `L ≥ 7`; actual adjacent balanced `b` and entering defect. |
| The entering-edge exit has error at most `(1−ρ/2)^J + J·2⁻ʰ`. | `flatExit_variation_of_edge` | Equal original totals and the entering-edge hypotheses. |
| A zero star has ideal failure only; actual retry stays within `J·2⁻ʰ` of fallback. | `idealTrialLaw_zero_star`, `flatExit_zero_star_variation` | `s_b = 0`; equal totals for the actual bound; supplied fallback. |

Original margins may contain zeros. The construction does not require a
lower bound on `U`, and singleton selected large-line blocks are permitted.
The bank fixes `b,h`; it does not equate completion widths at different
states. In the zero-star branch, the theorem does not infer pointwise actual
failure from a TV estimate.

The internal dyadic rate cancels in `ν_b`. It does not establish the incoming
trace clock `1/[2(4p−3)]`. Composition with that incoming step, adaptive
freshness and reservations, outer call caps, initialization, mixing, output
correction, degenerate branches and encoded costs remain separate interfaces.
No new full-sampler theorem, runtime exponent or inverse-gap bound is claimed.

## Evidence and replay

Ordinary Lean compilation passed in 170.30 seconds;
the compiled-environment audit passed in 348.43 seconds. The
[receipt](attempt-04/verification.json) binds the source, compiled object,
all module declarations and 4 complete headline dependency closures.
Only `propext`, `Classical.choice` and `Quot.sound` occur. The dependency
objects match the recorded accepted or newly compiled input hashes.

The pinned compiler and reused baseline objects remain trusted. This is
separate from the historical default-target Linux build and strict Comparator
task. [AI source review](AI-SOURCE-REVIEW.md) is not human review or independent
kernel verification. Failed compiler attempts are retained when present;
the [scope check](attempt-04/scope-check.json) and [proof diff](attempt-04/proof-only.diff)
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
