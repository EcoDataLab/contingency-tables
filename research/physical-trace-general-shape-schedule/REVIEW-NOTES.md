# AI source-review addendum: exact-numerator retry schedule

Date: 2026-11-06. This implementation-worker addendum records the mathematical meaning and ordinary compile/audit evidence. A separate skeptical AI source review examined the ceiling arithmetic, product-cover interpretation, budget and fixtures. This is a standalone optional schedule; the existing installed sampler, correction, numerator, kernels and raw code interfaces are unchanged.

The immutable successful source is `formal/ResearchPhysicalTraceJoin/GeneralShapeSchedule.lean`, module `ResearchPhysicalTraceJoin.GeneralShapeSchedule`. Source SHA256: `4640b268fac4992cd865fef5f9bc76852c022c0f3fa428888f7c1bf43a2746c4`. Receipt: `attempt-04/verification.json`. Base HEAD: `0dc1aa752e48d8127fcb058e7311c6d1b5119d6b`.

Let `D=2p(p-1)`, retain the current numerator `c0`, and let the current linear schedule's block be `A=min(D,4p)`. The new total definition is `K=min(A,(D+c0-1)/c0)`. On computed reference inputs, `c0>0` and `D>0`. `shapeCeiling_le_iff` proves that `(D+c0-1)/c0 ≤ k` exactly when `D ≤ k*c0`. Thus this is the exact integer ceiling, including divisible cases; it is not the sometimes one-larger `D/c0+1` alternative.

The existing geometric inequality `p-1 ≤ 2c0` and the fact `c0≥1` imply `D≤A*c0`. Therefore the new minimum is redundant on valid reference inputs: `positiveTraceShapeBlock_eq_ceiling` proves `K=ceil(D/c0)`. `positiveTraceShapeBlock_le_iff` states its exact least-product-cover meaning. This does not mean optimal actual retry count or optimal runtime.

The quantity `s=c0/D` is the exact defined `positiveTraceCorrectionSuccess` allowance, a proved lower bound on the actual ideal trial success. In general it is not equality to that actual success, whose earlier exact expression is `|Table|*c0/|DefectJoint|`. The new proofs retain this distinction. They establish `K>0`, `K*s≥1`, and `1/K≤s`. An actual defect start supplies the existing upper bound `s≤1`; no new success premise is assumed by the shape schedule theorem.

The schedule sets `R=K*(t+1)` and `h=k=t+2+clog2(R)`. A factored generic rational budget proves failure at most `2^-(t+1)` and each of the two accumulated draw errors at most `2^-(t+2)`, giving total error at most `2^-t`. `positiveTraceShapeScheduled_accuracy` composes this arithmetic with the existing corrected-retry accuracy theorem rather than duplicating its probabilistic argument. The law retains the existing supplied actual start and feasible fallback interface; initialization is a separate available composition. Both retry count and precision are proved no larger than the current linear schedule. The precision is given by an exact formula; no unsupported word-width or runtime monotonicity claim is made.

`shapeRetryBlockCode` and `shapeScheduleCodeData` are ordinary computational list/natural arithmetic outside the noncomputable section. Exact code/type correspondence proves that every reported count, block, attempt count and precision has the stated typed meaning. The fixtures use identical positive margin lists on both axes, so equal totals hold, and the computed reference tag/cutoff are also checked.

| Input on each axis | Cutoff | p | c0 | D | Old A | New K | Old R at t=10 | New R | Old h=k | New h=k |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| Nine 1s, then 30000 | 25938 | 99 | 801 | 19404 | 396 | 25 | 4356 | 275 | 25 | 21 |
| Nineteen 1s, then 200000 | 188518 | 399 | 7201 | 317604 | 1596 | 45 | 17556 | 495 | 27 | 21 |

These are exact integer equalities checked by ordinary kernel reduction, not native evaluation or timing estimates. The retry-count ratios are `396/25` and `532/15`. They do not establish corresponding wall-clock speedups, a new encoded runtime exponent, or an integrated improved finite-word sampler.

Attempt-04 compiled with empty stdout/stderr in 33.67 seconds and passed the full environment/headline audit in 125.62 seconds. The audit checked 41 declarations, 32 theorems, 11 complete headline closures, and 11,956 imported objects. Only `propext`, `Classical.choice`, and `Quot.sound` occur; the concrete fixture closures use only `propext`. Pinned compiler and accepted imports remain trusted.

Attempts-01 through -03 are preserved unchanged. The core ceiling, positivity, success-product, comparison, budget and law-accuracy proofs checked in attempt-01. Repairs addressed only a dependent rewrite in the full reported-data tuple and concrete fixture proof presentation: raw-side conversion, local fixture recursion allowance, constructive branch/cutoff decisions, and direct kernel reflexivity of the nine-field numeric tuple. No theorem was weakened, no new premise was added, and no correction/kernel behavior changed.
