# Separate AI source review

Final checked source SHA-256: `b227dd48ab18b02a2be2d367c691a78cb8186407e167b93d9abf7003d334ed40`.

Reviewed frozen source: `revisions/attempt-01/formal/ResearchPhysicalTraceJoin/Schedule.lean`.

Source SHA-256: `b227dd48ab18b02a2be2d367c691a78cb8186407e167b93d9abf7003d334ed40`.

A separate AI reviewer checked the natural schedule, scalar error bounds, and final literal-program instantiation. No mathematical or hypothesis mismatch was found. Under `U >= 2`, the natural subtraction in `terminalAggregateCount` casts to the real subtraction in the existing aggregate correction constant. Consequently `terminalGapCount` casts exactly to the existing aggregate mixing allowance, rather than assuming a new gap estimate. Its positivity follows from the existing lower bound on that allowance under `p >= 2`.

The exponent `h + 2 + 2 * D * clog_2(base)` pays for the full physical mass allowance `base^(2D)`, including the factor `2D`. The walk length is the positive natural gap count times this exponent, so its ratio to the real mixing allowance is exactly the exponent. The existing exponential and mass-charge bounds therefore make the mixing contribution at most `dyadic(h+2)`. The precision `h + 2 + clog_2(T)` pays for the accumulated `T` step errors; terminal precision `h+2` pays for the final completion error. Their sum is at most three quarters of `dyadic h`, hence at most the claimed target. All arguments include `h = 0`.

The final definition supplies these same natural parameters to the already identified literal terminal program. Its accuracy theorem directly composes the existing terminal-joint bound with the proved scalar budget. There is no desired-error hypothesis, stationary-start premise, abstract replacement sampler, or new conditional-law estimate. The word width is the inherited exact reserved input width of the literal walk and fresh terminal completion; it is not a claim about inspected bits or running time.

The final theorem retains equal original totals, `U >= 2`, `L >= 7`, at least two small cells, both computed large-line lists nonempty, nonempty defect support, and a supplied starting defect. Original margins need not all be positive. Its target is the uniform law on defect-labelled physical completion pairs. The schedule neither supplies that starting defect nor handles empty defect support, and does not establish original-table uniformity, an output correction, whole-sampler restart, a complete table sampler, or a new runtime exponent.

Compilation and assumption auditing are separate evidence and were pending for this frozen source when this note was written. This is AI source review, not human expert review or an independent kernel check.

The final ordinary compilation and full assumption audit are recorded separately in this packet.
