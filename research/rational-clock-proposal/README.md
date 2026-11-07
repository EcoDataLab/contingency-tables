# Capped rational-clock proposal

23 October 2026. The [Lean module](formal/ResearchRationalClock/Proposal.lean), `ResearchRationalClock.Proposal`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

For a positive natural interval size `V`, put `k = clog₂ V`. A `k`-bit word
is interpreted through `binaryWordEquiv k`. The trial accepts its index when
it is below `V` and rejects only indices at least `V`. The capped
sampler applies the existing `flatRetry` to `N` fresh trials and returns an
`Option (Fin V)` on exactly `N*k` fair bits. `none` records exhaustion; no
fallback index is selected.

```
a = V / 2^k,
Pr(capped index = none) = (1−a)^N,
TV(capped index, some(uniform Fin V)) ≤ (1/2)^N.
```

The comparison follows the weighted first-success law. The bound
`2^k < 2V`, including `V=1`, supplies the failure estimate. `N=0` returns
`none`; the zero-width singleton case is retained.

List lookup happens **after** capped index sampling. A valid index beyond
the list length is an accepted hold slot. It does not trigger another
trial. For a list `xs` with no duplicates and `xs.length ≤ V`, the ideal
proposal has mass `1/V` at each member and zero at nonmembers; the remaining
mass holds. The TV bound survives this deterministic lookup. After lookup,
`none` includes both accepted hold slots and index-sampling exhaustion, so
its mass is not generally just `(1−a)^N`.

| English claim | Lean statement | Explicit hypotheses |
|---|---|---|
| Each accepted integer index has one-trial mass `1/2^k`. | `intervalWordLaw_some` | Natural `V`; supplied `Fin V` index. |
| Capped exhaustion has exact mass `(1−a)^N`. | `cappedIndex_none` | `V > 0`; any natural `N`. |
| The exact `N*k`-bit bank is within `2⁻ᴺ` of a lifted uniform index. | `cappedIndex_variation` | `V > 0`; any `N`. |
| Lookup preserves that TV bound, including accepted hold slots. | `cappedList_variation` | `V > 0`; any finite list. |
| Each ideal list member has mass `1/V`. | `idealListLaw_mass` | `V > 0`; no duplicates; list length at most `V`. |
| The computed physical defect-neighbor list fits the degree allowance. | `physicalNeighbors_length` | Equal original totals; actual defect; arbitrary natural `U,L`. |
| The physical capped proposal approximates the rational-clock list law. | `physicalProposal_variation` | Actual defect; `p ≥ 2`; any `N`. |
| Every true physical neighbor has the exact ideal clock rate. | `idealPhysicalProposalLaw_mass`, `rational_clock_cast` | Equal totals and `p ≥ 2` for neighbor identification; the cast identity adds no premise. |

In the physical specialization,

```
p = number of small cells,
Q = 4p−3,
V = 2Q,
ideal mass of each physical neighbor = 1/[2(4p−3)].
```

The computed list's length is bounded by the actual defect degree theorem.
No large-line nonemptiness, padding-seven or positive-original-margin
hypothesis is needed for this proposal interface. The actual finite-word
law approximates the ideal rational law; it is not asserted to realize a
generally nondyadic rate exactly.

Source completion and acceptance, balanced-star exits and their composition,
adaptive freshness, outer reservations, initialization, mixing, output
correction and encoded costs remain separate. This packet supplies no
extracted machine, full-sampler theorem, runtime exponent or inverse-gap
claim.

The three [upstream integer-rejection dependencies](upstream-dependencies/)
were compiled unchanged from the pinned source. The initial missing-object
preflight and later failed proof attempts are retained. The final repair
uses upstream `mapLaw_decidableEq_irrel` to reconcile two equivalent
output equality tests before substituting the large physical state type;
it changes no sampling probability or theorem hypothesis.

## Evidence and replay

Ordinary Lean compilation passed in 111.16 seconds;
the compiled-environment audit passed in 203.92 seconds. The
[receipt](attempt-09/verification.json) binds the source, compiled object,
all module declarations and 4 complete headline dependency closures.
Only `propext`, `Classical.choice` and `Quot.sound` occur. The dependency
objects match the recorded accepted or newly compiled input hashes.

The pinned compiler and reused baseline objects remain trusted. This is
separate from the historical default-target Linux build and strict Comparator
task. [AI source review](AI-SOURCE-REVIEW.md) is not human review or independent
kernel verification. Failed compiler attempts are retained when present;
the [scope check](attempt-09/scope-check.json) and [proof diff](attempt-09/proof-only.diff)
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
