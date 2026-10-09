# Approximate completion oracles in the ideal-scale sampler

The new interface separates an oracle's certified output accuracy from
its implementation cost. It plugs normalized approximate completion laws
into the actual physical chain's dyadic proposal and signed translation
test, then bounds their effect on the finite-walk output law.

Both new modules compiled serially with pinned Lean 4.34.1. All 37 named
declarations passed the printed-axiom audit using only `propext`,
`Classical.choice`, and `Quot.sound`. Exact local commands, times, diagnostic
logs, audit names, and source hashes are in the
[verification receipt](../formal/results/approximate-oracle/verification.json),
with a separate [source review](../formal/results/approximate-oracle-review.json).
These checks build on the published sixth
checkpoint's actual rational kernels and finite-walk output bound; they do
not extend its Linux evidence or establish strict Comparator replay.
They do not construct an efficient completion oracle or a finite-bit
sampling program.

## Transition error and terminal error

[PhysicalApproximateOracle.lean](../formal/Math115/PhysicalApproximateOracle.lean)
first accepts two separate accuracy hypotheses. For every actual physical
state `x`:

- An approximate transition law `Q(x)` is within TV distance `δ` of the
  actual `selectedTransitionLaw(x)`.
- A terminal completion law `F(x)` on that state's actual fibre is within
  TV distance `η` of the uniform law on that fibre.

The bounds must hold for every state the approximate walk can visit.
Each transition and completion uses fresh conditional randomness. The
approximate chain need not be reversible or have the ideal stationary law.

After `T` transitions, the joint state/completion law differs from the exact
finite-walk trial law by at most

\[
 T\delta+\eta.
\]

The conditional-completion comparison is weighted by the approximate
walk's state law, so an average accuracy guarantee under the ideal
stationary distribution would not suffice. A uniform all-state guarantee
supplies the displayed bound.

For `R` independent attempts, each restarted at the same specified positive
state, the additional output error is at most `R(Tδ+η)`. The error is charged
before the balance/padding success test; no approximate trial law is
conditioned on success.

At `U=5d³`, `L=3d`, with a feasible fallback table and equal ordinary total
margins, the resulting bound is

\[
 \operatorname{TV}(\text{output},\mathrm{Uniform}(\mathrm{Table}(r,c)))
 \le e^{-R/S}+RB e^{-T/K}+R(T\delta+\eta),
\]

where `K=80,000d¹⁷`, `S=2(1+p²)`, `p` is the actual small-cell count,
`N=Σᵢrᵢ`, and `B=(N+dL+U+3)^(2d)`.
The [finite-walk schedules](physical-finite-walk.md) retain the explicit
factor `2d` in `log B`.

## The actual completion experiment gives a sharper row bound

[PhysicalCompletionOracle.lean](../formal/Math115/PhysicalCompletionOracle.lean)
identifies the actual finite proposal/draw/test experiment with the existing
rational transition law. Every physical neighbor receives mass

\[
 \beta=2^{-\lceil\log_2(32d^2)\rceil}.
\]

The remaining proposal mass holds at the current state. A non-hold proposal
draws an ordinary reference completion of the current state and tests the
source's literal signed translation. An exact uniform reference draw gives
exactly `referenceTransitionLaw`, including rejection and holding mass.
No assumed stationary law replaces this identity.

If the ordinary completion laws `μ(x),ν(x)` differ by TV distance `ζ(x)`,
the change in the transition law at `x` is at most

\[
 \beta\,\deg(x)\,\zeta(x).
\]

Holding proposals have constant output, so they contribute zero completion
error. This statement uses the same exact proposal and translation test;
proposal approximation or a changed test would need its own error bound.

The actual physical degree allowance is `D=5d²+1`. Define `γ=Dβ`, which the
source proposal bound gives at most `1/2`. A uniform completion error
`ζstep` therefore gives a uniform transition error `δ≤γ ζstep`. The local
degree bound can be smaller than this global allowance.

For the terminal draw, the source's free-scale reference-fibre equivalence
transports an ordinary reference table to the actual retained completion
fibre. This bijection preserves TV distance exactly. The oracle can use a
different terminal accuracy `ζterminal`.

The selected oracle interface consequently proves

\[
 \boxed{\operatorname{TV}(\text{output},\mathrm{Uniform})
 \le e^{-R/S}+RB e^{-T/K}
       +R\bigl(T\gamma\,\zeta_{\rm step}+\zeta_{\rm terminal}\bigr).}
\]

When both calls have accuracy `ζ`, the oracle contribution is
`R(Tγ+1)ζ`. The factor `γ` is an accuracy improvement from the proposal
structure. It is not an oracle-running-time improvement.

## Accuracy contract and remaining work

`OracleFamily` returns a normalized rational law on the actual ordinary
reference `Table` space for every reference choice and state. It cannot
silently return an invalid table or an unaccounted failure. An implementation
that can fail must include its fallback or failure handling in the law and
accuracy proof. Fresh calls must satisfy the conditional accuracy contract;
reusing correlated randomness is not covered by the independent-law model.

If a large reference row or column is missing, the selected construction
uses the exact unit transition law and the unique actual completion fibre.
The new module proves that fibre has cardinality one. That branch does not
invoke the ordinary-completion oracle. Zero margins, empty index types, and
singleton state spaces remain permitted under the stated nonemptiness or
equal-total hypotheses.

To allocate a positive TV target `ε`, one can first make the ideal
mixing/retry contribution at most `ε/2`, then require

\[
 R\bigl(T\gamma\zeta_{\rm step}+\zeta_{\rm terminal}\bigr)
 \le\varepsilon/2.
\]

The generic `approximateOuterLaw_variation_of_budget` formalizes that split.
It states sufficient real/rational inequalities and does not compute an
executable precision or walk schedule.

An adapter around an independently certified ordinary-table sampler could
supply these oracle laws and their accuracy bounds. In particular, using
the original full sampler as a separate subroutine would avoid assuming
that the new outer padding satisfies its internal dense discretization
conditions. The adapter must establish its own law and cost; substituting
an oracle name does not discharge those obligations.

The separate [dilated-margin completion route](completion-oracle-dilation.md)
uses a larger lattice, the existing dense sampler, and an integer decoder
with equal accepted-fiber counts. Its
[formalization](completion-oracle-formalization.md) now proves the complete
count comparison, quarter acceptance, and bounded-retry accuracy from an
accurate whole fine-table law. Connecting the canonical dense law and
assembling this completion law for every physical state remain open, as do
finite-bit realization and cost. These interface modules do not themselves
discharge those remaining obligations.

The new result identifies finite proposal/draw/test laws and accounts for
their accuracy. It does not bound completion cost, neighbor generation,
integer arithmetic, random bits, input conversion, or total machine
runtime. It does not remove the retained dense-scale obstruction or
establish practical competitiveness of a complete implementation.
