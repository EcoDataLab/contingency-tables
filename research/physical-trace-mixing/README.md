# Physical defect-walk mixing

23 October 2026. The [Lean module](formal/ResearchPhysicalTraceJoin/Mixing.lean), `ResearchPhysicalTraceJoin.Mixing`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

The target is the rational completion-count law on defects:

```
π_D(d) = card(Fibre(d)) / Σ_defects e card(Fibre(e)).
```

The source identifies its real cast with the computed reference trace's
stationary distribution. Its denominator includes only defect fibres. A
separate bound compares that defect total with the full physical total and
uses the existing full-mass allowance

```
Bmass = [M + D·L + U + 3]^(2D),
π_D(d) ≥ 1 / Bmass,
M = Σ_i r_i,   D = 10+(m+1)(n+1).
```

Let `p` count the small cells and set

```
K = 32 p³ · aggregateCT(r,c,U).
```

The aggregate coefficient is the existing proved margin-dependent Poincare
allowance. Under `U ≥ 2`, `L ≥ 7` and `p ≥ 2`, the source derives `K ≥ 1`
and applies the existing finite-chain exponential mixing theorem. From a
supplied starting defect, the ideal bound is

```
TV(ideal joined walk after T steps, π_D) ≤ Bmass · exp(−T/K).
```

The scheduled literal word walk takes a reserved input bank of exactly
`T * uniformStepWidth(r,c,U,L,t+2,t+2,attempts(D,t),precision(D,t))`
fair bits. Its bound is

```
TV(literal word walk, π_D) ≤ T·2^(−t) + Bmass·exp(−T/K).
```

This is a finite-accuracy statement with free `T,t`. It does not assert that
the actual kernel at fixed `t` has stationary law `π_D` or converges exactly
to it as `T` grows; the approximation term grows with `T`.

| English claim | Lean statement | Explicit hypotheses |
|---|---|---|
| Rational defect-fibre weights cast to the computed trace stationary law. | `defectStationaryRat_cast`, `defectStationaryLaw_cast` | Nonempty defect support; both computed large-line lists nonempty; `p ≥ 2`. |
| The defect total is bounded by the existing full physical mass allowance. | `defectTotalMass_le_full`, `defectTotalMass_le_allowance` | Arbitrary natural `U,L`; actual physical state definitions; no positive-original-margin premise. |
| Every trace stationary mass is at least `1/Bmass`. | `computedTrace_pi_lower` | Nonempty defect support; both large-line lists nonempty; `p ≥ 2`. |
| The ideal joined walk satisfies the proved trace mixing bound. | `idealJoinedWalk_mixing` | Equal original totals; `U ≥ 2`; `L ≥ 7`; `p ≥ 2`; both large-line lists nonempty; nonempty defects; supplied starting defect. |
| The literal scheduled word walk satisfies the combined error bound. | `scheduledJoinedWalkWord_mixing` | The same hypotheses; natural precision target `t` and step count `T`. |

Original margins may contain zeros. No stationary start is assumed, and no
new Poincare estimate is introduced as a hypothesis: the source reuses the
proved computed-reference aggregate theorem. The stationary target here is
a distribution on defects. A terminal table completion, output correction,
whole-attempt restart, initialization and the remaining degenerate branches
are not supplied. No full table sampler, extracted machine, encoded cost or
new runtime exponent is claimed.
## Evidence and replay

Ordinary Lean compilation passed in 66.68 seconds;
the compiled-environment audit passed in 187.23 seconds. The
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
