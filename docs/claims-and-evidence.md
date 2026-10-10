# Claims and evidence

[The claims ledger](../claims.json) binds each public headline to an English
claim, the quantity bounded, stated hypotheses, present limits, source files,
Lean declaration names, and a verification receipt with an explicit scope.
The English descriptions are interpretations that require mathematical review;
the exact Lean types remain the authority for hypotheses and conclusions.
Headline defining-module/source attribution is explicit and reviewed using
the project’s module/namespace convention; historical selected receipts do not
independently attest defining-module origins. A compiled environment receipt
is needed to authenticate those origins.

## Completed stage scope

The [completed stage aggregate](../formal/results/completion-aggregate-1236/verification.json) passed **1,236 focused plus six standalone named declaration audits (1,242 total)**. Its 583-module normal closure contains 582 authenticated reused modules and one fresh aggregate root; four fresh named-audit checks passed. The formerly separate 46 encoded-program, 193 physical-bridge, and 134 Boolean-law/schedule declarations are now integrated into the default focused target. This is ordinary Lean compilation and selected axiom auditing with reused dependency objects, not a fresh rebuild of every dependency or strict kernel replay. All selected axioms remain within `propext`, `Classical.choice`, and `Quot.sound`, or subsets.

The environment-derived full audit is **pending final validation and import rehashing**; its Lean generation step finished, but no successful exhaustive-inventory result is claimed yet. Fresh Linux reproduction of this staged aggregate is also pending. The old aggregate and Linux `895b45c` receipts remain historical evidence for their exact earlier source scopes.

The final [outer-sampler attempt](../research/outer-sampler/status.json) failed: 673 modules were reused, three failed, nine were dependency-blocked, and no new source compiled successfully in that attempt. `LatticeProfileStep` had passed the preceding normal attempt and was reused; the current failures are `LatticeProfileWalk`, `LatticeSamplerPreparation`, and `LatticeUnitStep`. All 13 attempted outer-sampler sources and diagnostics are frozen under [research/outer-sampler](../research/outer-sampler/) outside the default formal target. No complete literal outer sampler or full machine runtime is verified.

The [runtime-degree archive](../research/runtime-degree/) retains passed TreeDegree diagnostics, a failed PolynomialCompilerDegree diagnostic, and uncompiled fresh-bit/finite-word proposals. The numerical complete runtime exponent is unknown. The [Comparator serial archive](../research/comparator-serial/) retains 33 offline orchestration tests and 16 planner tests, without a real Linux runtime result for that route. The [strict VM attempt](../formal/results/strict-comparator-vm-895b45c/README.md) passed ABI-11 sandbox preflight but exhausted memory before comparison; it produced no candidate export or kernel result.

Use the [contributor handoff](handoff.md) for reproduction and ordered next-round obligations. Reviewed application evidence includes the [mature worker-library benchmark](worker-library-benchmarks.md), [public commuting backtest](commuting-backtest.md), and [source-level composed complexity review](composed-complexity.md). These measure a classical law, describe a public job-table case frame, and retain a symbolic uncompiled cost proposal, respectively; none verifies a complete universal sampler.

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

This helper's successful local compilation and small fixture checks are
**diagnostics**, not a receipt for exhaustive project coverage. The full-environment Lean generation step has finished, but final validation and imported-object rehashing remain pending. No successful public full-environment audit receipt is supplied yet. Existing published counts
continue to describe selected named audits. To claim exhaustive coverage,
a successful compiler receipt must bind the audit JSON, exact imported
module list, source/object digests, compiler and dependency pins, and the
selected namespace/module filters. Its theorem set must then be compared
with the historical selected rosters; its headline types/hypotheses need
mathematical review against the ledger. Files absent from the imports are
outside that environment. No source regex is treated as a compiled theorem
inventory.
