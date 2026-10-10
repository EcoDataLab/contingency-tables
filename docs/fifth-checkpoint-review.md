# Independent review of the fourth publication checkpoint

Review provenance: “independent” here means a separate AI agent reviewing AI-produced research or code within this project. This is not outside human peer review. Compiler and execution receipts have the narrower scopes stated below.

Review date: 9 October 2026 UTC. This is the fifth review batch; the
publication checkpoint is number four. Separate Codex agents reviewed the
physical repair integration, exact finite backend, benchmark accounting, and
2×2 argument. Source review and successful compiler execution are distinct
evidence. The [formal ledger](formal-verification.md) and
[Python receipt](../reports/checkpoint-verification.json) record execution.

## Actual physical repair and chain constants

The [source review receipt](../formal/results/physical-repair-review.json)
identifies final frozen hashes for `PhysicalRepairRefinement`, its ideal and
dense-compatible wrappers, and the abstract repair lemma. It found no
substantive mathematical defect. The reviewer did not invoke Lean.

The refinement uses the literal source `repairWord`, its two-cell label
encoding, weight domination, and repair-energy bound. The label cardinality
is still `p²`; no improved repair congestion or omitted within-type variance
is assumed. The new coefficient is

```
C = C_T + (sqrt(p² C_T)+1)².
```

The polynomial estimate was checked independently: the transversal term is
at most `27dU⁴/32`, the Young multiplier is at most `9d²/8`, and the remainder
is at most `d³U⁴/128`. Together these give `245d³U⁴/256 ≤ d³U⁴` under
`d≥11,U≥2,p≤d`, including `p=0`.

The reference-chain energy retains its factor `β/(2Z)`, giving `2C/β`;
the empty-block unit identity has factor `β/Z`, giving `C/β`. The unchanged
proposal reciprocal is at most `64d²`. Thus `128d⁵U⁴` and `64d⁵U⁴` have the
correct normalization. The automatic selector uses the larger allowance.
The `80,000d¹⁷` and `128·47⁴d²⁵` wrappers use the same chain objects already
constructed at their respective scales. Equal-total wrappers discharge
physical-state nonemptiness without adding a reference-index assumption.

Review corrected the explanation of the eightfold conservative improvement:
it combines the new repair inequality with tighter polynomial arithmetic.
The exact repair coefficient alone approaches a factor-two improvement when
its defect term dominates.

The audit harness now checks every requested declaration by name, including
Lean reports with no axioms. It rejects missing, duplicated, reordered, or
unrequested reports, nonstandard axioms, and unrecognized output. A separate
reviewer checked the parser and all five regression tests. The pinned audit
files contain only imports and print commands; even a compiler warning now
requires inspection. Compiler exit status is checked separately.

## Finite ideal-chain implementation and budgets

The backend was independently checked against the pinned physical state and
completion definitions, including row-valid and column-valid views, unit
exchanges, designated repairs, translation rejection, stationary weights,
and all-small returns. Its tests enumerate feasible state pairs independently
of the production profile generator and verify accepted forward/reverse
completion sets. Exact stationary output checks apply to stationary draws;
short fixed-start trajectories are not asserted to be uniform.

The implementation is an exhaustive finite oracle. Limits cover candidate
profiles, retained states, completion work, graph construction, and exact
linear algebra. Rational size checks limit retained normalized results;
intermediate integer products before reduction are not preflight bounded.
That limitation is explicit in the implementation guide and benchmark.
No incorrect-law or silent partial-result defect remained after review.

## Same-law comparison and failure accounting

Independent review checked 23 diagnostic/benchmark tests, then the root
integration ran the full 230-test suite. All eight source hashes embedded in
the saved benchmark match the published inputs. The panel contains 18 cases;
uniform, activity-weighted, and ordinary inverse-factorial laws are separate.
The worker urn is compared only against methods targeting its own law.

Exact reversible-kernel diagnostics solve the Poisson equation by rational
arithmetic and verify the resulting equations. Periodic chains, distinct
communicating-class means, zero variance, and zero asymptotic variance have
explicit statuses. Stationary variance is not a cold-start convergence claim.

All operational preparation, initialization, warmup, and draw costs are
separate from target enumeration and diagnostics. Supplied tuned mixtures
include loading and input-validation costs; their original numerical search
cost is unmeasured and excluded. Algebraic censored-return draws bypass
physical excursions and are not reported as literal chain timings.

Five physical runs hit the excursion cap. Their partial outputs and elapsed
work are retained, without ESS or throughput claims; each affected method's
aggregate median is unavailable. Four larger fibers exceed the exact dense
diagnostic cap. These failures remain part of the result.

## Exact 2×2 family and lower bound

A separate reviewer reconstructed physical graphs from diagonal coordinates
for margins `t=1,...,6` and independently solved the base rational Dirichlet
problem. Complete states, edges, return kernels, return-time means, Poisson
variances, and the Rayleigh witness agree with the
[saved certificate](../reports/ideal-two-by-two.json).

The general block argument gives `13t+1` vertices and `28t` edges, with
censored neighbor probability `32β/15`. Its coordinate variance inflation is
`((t+1)²+1)/(5q)-1`. The full physical Rayleigh witness gives the inverse-gap
lower bound `5(13t²+3t−514/75)/(128β)`. Setting `t=U−1` yields an `Ω(U²)`
obstruction for this free-cutoff chain family at fixed dimensions.

The argument is mathematical and independently reviewed, but not formalized
in Lean. Six exhaustive examples check the implementation; they do not prove
the universal decomposition by enumeration. Return-index asymptotic variance
is not multiplied by the mean return time to claim a physical-clock variance
theorem. Root integration also corrected the comparison prose: the saved
benchmark uses a full-line heat bath with no added holding probability, so
on a single rectangle it gives iid uniform draws and variance inflation one.

## Boundaries at this checkpoint

The new ideal scales violate the retained sufficient dense-completion
interface. Stationary physical success and the outer output law at free
scales still need their own integration. No complete modified finite-bit
sampler, machine-runtime proof, general practical speed advantage, or
extension to arbitrary bounded/weighted models follows from this checkpoint.
Earlier Linux/native Windows checks and strict Comparator limitations retain the
separate scope recorded in the formal ledger.

Subsequent checkpoint 5 adds the
[stationary success and output proof](physical-stationary-success.md), with
its own [independent source review](../formal/results/stationary-output-review.json).
It closes the stationary-law part of the integration above; finite-walk
output approximation and finite-bit implementation remain open.
