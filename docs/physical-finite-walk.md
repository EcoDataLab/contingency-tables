# Finite walks and bounded output retries at ideal scales

The new modules connect the actual physical chain to a finite rational walk,
a fresh exact terminal completion, and a bounded first-success output law.
They use the source's physical graph, proposal, reference completion
acceptance, and unit branch at free `U,L`.

Both new modules compiled serially with pinned Lean 4.34.1. All 39 named
declarations passed the printed-axiom audit using only `propext`,
`Classical.choice`, and `Quot.sound`. The [module receipt](../formal/results/finite-walk/verification.json)
retains commands, logs, selected audit names, and source hashes. The
[integrated log](../formal/results/sixth-checkpoint.log) records a fresh
aggregate compilation and all 324 selected declaration audits. The
[independent review](../formal/results/finite-walk-review.json) records the
mathematical and interface checks at the stated source hashes.
The published fifth checkpoint at
`7ad5c81117bbaa869da751b1f92a9213ddefdd22` supplies their chain and
stationary-success inputs. These local checks do not extend that
checkpoint's Linux evidence or establish strict Comparator replay.

## The actual finite law

[PhysicalRationalKernel.lean](../formal/Math115/PhysicalRationalKernel.lean)
defines rational reference, unit, and selected transition laws. Its cast
theorems identify every transition probability, including holds, with the
existing actual `FiniteChain`. The selector uses the same branch predicate
and chosen references as the earlier selected chain. The independent finite
walk therefore has exactly the transition law of that chain.

[PhysicalFiniteWalk.lean](../formal/Math115/PhysicalFiniteWalk.lean)
defines a complete output law for equal-total ordinary margins and a supplied
feasible fallback table. The fallback's successful physical preimage supplies
a specific positive initial state. Every attempt restarts at that state,
runs `T` transitions with fresh randomness, and draws a fresh uniform
completion from its terminal state's actual fibre. It tests balance and
padding, and returns the unpadded table on success. After `R` failures it
returns the supplied fallback.

These are independent restarted attempts. Consecutive outputs of one
persistent chain have a different joint law and are not covered by this
retry theorem.

## The output-error bound

Let

\[
 d=10+(m+1)(n+1),\quad N=\sum_i r_i,\quad
 p=|\mathrm{Cells}(\mathrm{firstPaperSmall}(r,c,U))|.
\]

The actual capacity is at most `N+dL+U+2`. Every positive physical weight
is a positive integer completion count, so it is at least one. The existing
free-scale mass theorem bounds the normalizer by

\[
 B=(N+dL+U+3)^{2d}.
\]

Thus every stationary state probability is at least `1/B`. For any actual
Poincare coefficient `K≥1`, generic lazy-chain mixing gives a finite-walk
TV bound `B exp(−T/K)`. Appending the same exact conditional completion
kernel to the walk and stationary laws cannot increase their TV distance.

If the ordinary padded-table count is at most `A` times the original count,
the stationary joint success probability is at least
`1/[A(1+p²)]`. Independent retries accumulate the trial error before the
success test. The final law therefore satisfies

\[
 \operatorname{TV}(\text{output},\mathrm{Uniform}(\mathrm{Table}(r,c)))
 \le \exp\!\left(-\frac{R}{A(1+p^2)}\right)
       + R B\exp\!\left(-\frac{T}{K}\right).
\]

No approximate trial law is conditioned on success. The two terms account
for exhaustion of the retry budget and imperfect mixing of each finite walk.

At the ideal-only scales `U=5d³`, `L=3d`, the verified input theorems give

\[
 K=80{,}000d^{17},\qquad A=2,\qquad S=2(1+p^2).
\]

The new `idealOuterLaw_variation` specializes the bound to
`exp(−R/S)+RB exp(−T/K)` for all equal-total ordinary margins. It requires
a feasible fallback but no assumed stationary start or supplied large
reference row or column.

## Sufficient schedules

For a positive target `ε` and positive integer `R`, it suffices to choose

\[
 R\ge S\log(2/\varepsilon),\qquad
 T\ge K\log(2RB/\varepsilon).
\]

Then each error term is at most `ε/2`, and the output TV distance is at most
`ε`. `idealOuterLaw_variation_of_log_schedule` states these explicit
inequalities. For `0<ε≤1`, natural ceilings of the displayed expressions
provide suitable schedules; the theorem states `R>0` to exclude division
by zero.

The second logarithm includes

\[
 \log B=2d\log(N+dL+U+3).
\]

The factor `d` remains part of the transition allowance. A dimension-order
comparison must also retain the outer factor `R`, which can grow as `p²`.
The exact `R,T` expressions are preferable to hiding these factors inside
an unspecified logarithmic term.

## Scope and implementation work

The generic theorems handle zero margins, zero small-cell count, singleton
physical spaces, and empty index types under equal total margins. The unit
branch handles a missing large row or column. All divisions used for mixing
and the schedule have explicit positive denominators. If the target table
fibre is known to be a singleton, the fallback itself gives exact output.

The proof constructs noncomputable finite rational laws. It does not yet
identify those laws with an executable source proposal/draw/test routine,
prove efficient neighbor generation, or implement the exact completion
oracle. The finite walk uses at most `RT` kernel transitions. A realization
using one completion draw per reference transition and one terminal draw
would use at most `R(T+1)` completion-oracle invocations, after proving that
realization has the same law. The empty-completion branch can omit those
oracle calls.

Neither transition counts nor that prospective oracle-call ceiling charge
completion work, reference-fibre construction, neighbor enumeration,
integer arithmetic, random bits, or initialization. These costs and the
finite-bit approximation/correction proof remain separate. The ideal
scales still fail the retained dense finite-bit scale interface. No machine
runtime, practical competitiveness, exact uniform sampling, or weighted
and constrained-table extension is claimed.
