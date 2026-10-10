# Claims and evidence

[The claims ledger](../claims.json) binds each public headline to an English
claim, the quantity bounded, stated hypotheses, present limits, source files,
Lean declaration names, and a verification receipt with an explicit scope.
The English descriptions are interpretations that require mathematical review;
the exact Lean types remain the authority for hypotheses and conclusions.
The [compiled headline index](../formal/results/environment-aggregate-1236/headlines.json)
now records exact types, defining modules, axioms, and complete dependency-closure
bindings for all six Lean headlines. It also preserves the corresponding English
claims and hypotheses from the hash-qualified ledger snapshot. Historical named
receipts retain their narrower scope.

## Completed stage scope

The [current integrated receipt](../formal/results/completion-aggregate-1236/verification.json)
includes the encoded completion program, physical bridges, and both-branch
Boolean law and schedule. Its named audits are regenerated from saved receipts;
its normal build used authenticated dependency reuse and a fresh aggregate root.
The [status ledger](status.md) records current verification results and the
[contributor handoff](handoff.md) separates the checked core from frozen research.
The literal outer sampler, numerical complete runtime degree, and strict
Comparator replay remain open.

`python3 scripts/claims_ledger.py` validates the ledger and renders the README
claim cards and named-audit counts. `--write-readme` replaces only the marked
section, `--check-readme` detects stale generated content, and `--json` emits
receipt-derived scope counts. `--audit-driver focused` and
`--audit-driver all-components` emit Lean drivers from validated receipt module
lists and ledger headlines; they do not run Lean. No new compilation occurs
in this command.

The validator checks the pinned receipt bytes and published artifact digests,
replays each saved named audit with the strict axiom checker, compares names
and axiom lists, and requires each Lean headline to appear in a matching
receipt with its current source digest. Disjoint component counts are derived
from declaration names and checked for overlap. The current aggregate already includes the formerly separate encoded-program, physical-bridge, and Boolean-law/schedule names; their historical receipt counts must not be added again. The later Linux focused run
is a separate reproduction scope that overlaps the aggregate. A source list
or a large count cannot verify a headline absent from the named audit.

Some receipts bind an exact repository commit; others bind a checkout base
commit plus selected source hashes, or source hashes without a recorded base
commit. The ledger preserves these distinctions. A historical passing receipt
is evidence about its recorded bytes and scope, not a fresh build of the
current checkout. The Boolean schedule receipt preserves its original status
that selected compilation and named audits passed while publication review of
the private projection was still pending; a later publication does not rewrite
that historical receipt. Dependency-cache and reused-object trust boundaries
remain in the original receipts.

## ideal-inverse-gap

`Math115.IdealRepairRefinement.feasibleChain_poincare_d17_refined` bounds the
actual ideal auxiliary chain's variance by `80000 * d^17` times its energy,
where `d=10+(m+1)(n+1)`. Finite natural margins must have equal totals. State
existence and branch choice are part of the construction. This is an inverse
gap bound for transitions using ideal completions; it does not give the cost
of computing one transition or the complete machine runtime.

## finite-word-law

`Math115.PhysicalBooleanSampler.draw` returns a feasible table for every
reserved Boolean word. `draw_explicit_accuracy` bounds total variation from
the uniform feasible-table law by `2^-h` when that word is uniform and the
proved schedule is used. Equal-total natural margins may include zeros and
empty dimensions. The typed construction uses noncomputable ingredients;
identifying a complete literal encoded outer walker remains open.

## component-cost

`Math115.CompletionSamplerProgram.polynomial_draw` proves polynomial charged
cost for the completion draw with encoded margins, parameters, and supplied
random word. `Math115.CompletionSamplerSemantics.draw_semantics` identifies
its matrix code and accurate output law under `d≥14`, equal totals,
dimension/free-coordinate bounds, and the dense margin inequalities shown
in its Lean statement. `Math115.LatticeScheduleProgram.polynomial_schedule`
proves polynomial charged cost for the numeric schedule. These are component
contracts; they do not supply the full outer sampler's machine-cost exponent.

## executable-references

The Python exact finite backends and saved experiments exercise finite cases
under their stated laws and constraints. Enumeration and measured timings
support those instances. They do not establish general mixing or polynomial
runtime. In particular, ideal completion enumeration and proofs of a
probability law have different computational implications.

## Environment-derived audit

[EnvironmentAudit.lean](../formal/ResearchAudit/EnvironmentAudit.lean) implements a
separate environment audit using the pinned Lean 4.34.1 APIs. A driver imports
the target compiled modules and the helper, then runs:

```lean
#environment_audit prefixes [Math115] modules [] headlines
  [Math115.IdealRepairRefinement.feasibleChain_poincare_d17_refined]
```

The helper reads `Environment.constants`, selects declarations by namespace
or defining-module prefix, or by an explicitly selected imported module, and emits their exact pretty-printed
Lean types, declaration kinds, direct dependencies, and transitive axiom
reports. The theorem inventory is every `ConstantInfo.thmInfo` in that
selected environment, including declarations that were never placed in a
manual `#print axioms` roster. Defining-module selection also includes private
names; helper instrumentation is excluded from the project inventory.
Headline dependency closure traverses compiled types and values, including
opaque/theorem values and inductive constructors. Standard axioms are reported
separately from nonstandard axioms; any nonstandard axiom fails the command.
The proof-statement records contain all binders and hypotheses, while the
ledger supplies the separate English interpretation.

The [full compiled-environment audit](../formal/results/environment-aggregate-1236/README.md)
passed on the frozen native aggregate. The [publication record](../formal/results/environment-aggregate-1236/PUBLICATION.md)
links the subsequent independent AI-agent readback while preserving the frozen
receipt’s creation-time review status. Its complete report contains 22,710 selected
declarations, including 16,549 theorem constants, and six headline closures.
These totals include pinned upstream and generated/private declarations under
explicit filters; they are not new-theorem counts. The receipt binds the driver,
helper, executed runner, compiler and source pins, 11,849 imported modules,
resolved object hashes, and unchanged before/after input inventories.

The [exact headline index](../formal/results/environment-aggregate-1236/headlines.json)
contains every printed binder and hypothesis, while the compressed raw report
retains the complete dependency records. The following is a reading guide;
the exact types and definitions determine each contract.

| English claim | Lean declaration (all under `Math115`) | Main hypotheses or input contract |
| --- | --- | --- |
| Ideal-chain variance is at most `80,000d^17` times energy | `IdealRepairRefinement.feasibleChain_poincare_d17_refined` | Finite linearly ordered index sets; natural margins with equal totals; any real state observable. |
| Typed output is a feasible table for every word | `PhysicalBooleanSampler.draw` | Equal-total natural margins; natural walk/retry/precision parameters; a Boolean word of the reserved length. The return type is `Table r c`. |
| Scheduled typed output is within `2^-h` of uniform | `PhysicalBooleanSampler.draw_explicit_accuracy` | Equal-total natural margins and natural `h`; the defined physical schedule and uniform reserved word. Empty dimensions and zero margins are included. |
| Encoded completion has polynomial charged cost | `CompletionSamplerProgram.polynomial_draw` | The typed `drawRealizer` input, including its supplied Boolean list; cost is execution plus encoded output weight. Semantic margin conditions belong to the next statement. |
| Encoded completion equals the analyzed draw and has the stated accuracy | `CompletionSamplerSemantics.draw_semantics` | `d≥14`, equal totals, `m+1≤d`, `n+1≤d`, `mn≤d−1`, row margins at least `3d(n+1)`, column margins at least `3d(m+1)`, and the specified reserved word. |
| Numeric schedule has polynomial charged cost | `LatticeScheduleProgram.polynomial_schedule` | The typed `scheduleRealizer` input of encoded margins and natural precision. No full sampler cost is inferred. |

The report authenticates compiled types and dependencies, not the scientific
interpretation of a model. It does not identify the unfinished encoded outer
walker or perform strict Comparator replay. Files absent from the imports,
including the archived outer-sampler drafts, are outside the selected
environment. Named audit counts remain separate and must not be added to
these overlapping environment totals. No source regex supplies the theorem
inventory.
