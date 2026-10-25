# Separate AI source review: general ideal terminal correction

Date: 2026-10-24.

**No mathematical blocker found for the stated ideal one-trial correction.** The five prerequisite modules have successful compilation and assumption-audit receipts. `GeneralTerminalLaw` compiled cleanly in 48.28 seconds. Its assumption audit subsequently passed in 88.28 seconds; that completion is reconciled below. This reviewer checked the source and saved evidence and did not run Lean.

| Module | Reviewed SHA256 |
|---|---|
| `GeneralInverse.lean` | `eb5c24c8a90433ea15f8905baca5a04ddfca4d170d39ee320e888bc63f518242` |
| `GeneralInverseSupport.lean` | `0aae672bbe0989d9499140759289e23e6bc692f844f026a93b33809fdf3eb1c4` |
| `GeneralInverseLower.lean` | `9fd2ca995e5d33b6112a453be01bd3f978a3be702f29b2bb2eb500d27370b494` |
| `GeneralCount.lean` | `6d6aaa9c07ba1795ff2ea6415d4c53294cd857ee7dd4db77b6e9e17a7e766286` |
| `GeneralAcceptance.lean` | `8bcdd1b2ca716af5dbd74ac58e1d335682cf1ffb49cebda629f34766eb1045e0` |
| `GeneralTerminalLaw.lean` | `bede661953abd4cf1d7ac86021efd763e5ae59d54a92bbcbd75fe819f66f891d` |

## Inverse pairs and counts

The inverse retains both full physical views and the particular dense completion. It proves bounded small coordinates, original small-line inequalities, dense agreement and caps, and positive hard weight from an explicit completion witness before constructing an actual `DefectJoint`. Canonical labels are proved equal to the candidate labels. Full signed recovery makes the arithmetic-label characterization exhaustive.

The support test correctly distinguishes crossing classes. A small crossing needs a positive ordinary target entry, including label/crossing coincidences. A large crossing needs positive **ordinary** residual row and column slacks; padded positivity alone is insufficient. `L>=1` supplies dense subtraction after success. Inverse small entries may reach `U`, and the source proves the required non-strict cap. No inverse-count, completion-existence, or positive-hard-weight premise is assumed.

The exact count is a finite sum over ordered labels passing the support/slack test. Explicit equivalences connect it to the actual repaired-matrix fibre, successful ordinary-output fibre, and option-valued partial-repair fibre. Completion multiplicities are preserved throughout.

Positive ordinary margins supply a positive target cell in every small row. The row injection chooses one such cell per small row and varies labels over small rows and all columns, excluding exactly the coincident-label case. Its cardinality is `a*(n*a-1)`. The symmetric column injection has cardinality `b*(m*b-1)`. Both recover their parameters from the labels. Taking their maximum, rather than their sum, correctly avoids overlapping families. This derives the documented `c0` lower bound.

## Ideal law and success

The generic rule uses the total clipped probability `min(c0,ell)/ell`, including `ell=0`. It proves successful point mass `min(c0,ell)/Z` from an ideal uniform source on actual defect/completion pairs. The geometric lower count removes clipping and gives point mass `c0/Z` for every ordinary table. No acceptance lower bound remains as a caller premise in this specialization.

The terminal law proves total success probability and uniform successful-output proportions. At `U=11*d*(m+n-2), L=7`, the count module instantiates the existing reciprocal-growth theorem on the actual large mask and derives `Z<=2*p*(p-1)*N`. Success is therefore at least `c0/(2*p*(p-1))`; source nonemptiness and this bound justify positive denominators.

The final positivity theorem supplies the strict-positivity step: with `m,n>=2`, positive ordinary margins and a nonempty actual defect-joint space, the denominator bound forces `p>0`, so `c0>0`. Uniform proportions then have positive mass and justify conditional uniformity upon acceptance in this ideal branch. Nonempty `DefectJoint` is explicit; it is not a derived initialization theorem.

## Evidence, reconciliation and limits

For all five prerequisite modules, the saved source and compressed-audit hashes match their receipts, every headline closure has a record for each dependency, and no module or headline-closure record reports a nonstandard axiom. Terminal-law compilation reports unchanged source, empty diagnostics and output-object SHA256 `a7a5633b33098bb221a5ab720b740de2efe8c0559e5b9418dd82b692977ee6f5`. The subsequent final audit passed with seven complete headline closures and only standard axioms; the coordinator reconciled this receipt against the unchanged reviewed source. Failed attempts remain evidence and are not described as successful runs.

The final count source includes namespace qualification, abbreviation unfolding, and alpha-renaming the theorem-statement let binder `p` to `cellCount`. Its headers are not byte-identical to the earlier candidate; these changes preserve the mathematical claim. Terminal-law proof repairs use explicit positivity/casts and algebraic calculation. The positive-success theorem is an explicit additional result.

The exact support count remains a sum over label pairs. These modules do not simplify it to `D0+abuv`, derive `c0>=p/4` or the `1/(8p)` corollary, implement a bounded dyadic coin, compose approximate endpoint errors, or identify an encoded program. They supply no starts, branch assembly, retries, complete sampler, runtime bound, or exponent change. No `sorry`, `admit`, or new `axiom` appears in the reviewed sources.

Final receipt reconciliation: all six source hashes above match the compiled sources. The final module audit and compressed bytes are recorded in [verification.json](attempt-03/verification.json). No source changed after this review.
