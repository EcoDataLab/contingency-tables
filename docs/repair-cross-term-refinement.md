# A sharper finite repair constant

Mathematical derivation, 8 October 2026. This refinement is not yet checked
in Lean. The separate draft
`RepairVarianceRefinement.lean` (a local draft deferred from this publication checkpoint)
contains the Young-parameter family, a finite weighted Cauchy–Schwarz argument,
and its proposed graph-energy corollary. That module has not been compiled or
axiom-audited. The current full-variance integration deliberately uses the
unchanged source repair inequality.

Work is saved for resumption at the user's requested pause. No compiler pass
has been started for this module. The next check is a direct Lean invocation
from `formal/`, with `-j1 -DautoImplicit=false`, followed by an axiom audit of
its seven exported lemmas and theorems. Coordinate a compiler slot first;
the working source cache currently uses direct builds without Lake traces.

Suppose base states have nonnegative weights `w`, defect states have
nonnegative weights `v`, and each defect `d` repairs to `R(d)`. Assume
`v(d) <= w(R(d))`, and the pair `(repair label, R(d))` identifies `d`, with
at most `D` labels. Let the observable be `H` on base states and `K` on
defects. These are the same hypotheses as upstream `variance_sum_repair`.

Write `mu` for the base weighted mean and define the unnormalized quantities

\[
 V=\sum_b w_b(H_b-\mu)^2,\qquad
 A=\sum_d v_d(H_{R(d)}-\mu)^2,\qquad
 R=\sum_d v_d(K_d-H_{R(d)})^2.
\]

The source's typewise injection gives `A <= D V`. Centering the full
variance at `mu` and expanding the defect terms gives

\[
 \operatorname{Var}_{\rm full}
 \le V+A+R+2\sum_d v_d(K_d-H_{R(d)})(H_{R(d)}-\mu).
\]

Weighted Cauchy–Schwarz bounds the last sum by `sqrt(A R)`. Consequently,

\[
 \operatorname{Var}_{\rm full}
 \le (1+D)V+R+2\sqrt{DVR}.
\]

If `C_T >= 0`, `V <= C_T E`, and `R <= E` for a nonnegative graph energy `E`, this yields

\[
 \boxed{C_{\rm full}\le (1+D)C_T+1+2\sqrt{D C_T}
       =C_T+(\sqrt{D C_T}+1)^2.}
\]

This improves the earlier manuscript coefficient
`(sqrt((1+D) C_T)+1)^2`. The useful distinction is that the repair
displacement is zero on base states. Only the defect-side lifted energy
`A` participates in the cross term; the base energy `V` stays outside it.

It also never exceeds the unchanged source coefficient `(1+2D) C_T+2`:
the difference between the source and refined coefficients is
`(sqrt(D C_T)-1)^2`. Both comparisons are included in the uncompiled draft.

Every zero case is harmless: the displayed argument uses nonnegative finite
sums and square roots, with no division by a state weight or a context mass.
When the base total mass is zero, domination forces all defect weights to
be zero as well.

An equivalent route for formalization is the parameterized square inequality

\[
 (x+y)^2\le (1+1/\eta)x^2+(1+\eta)y^2\quad(\eta>0).
\]

Applying this only to defects gives the fully algebraic family

\[
 C_{\rm full}\le [1+(1+\eta)D]C_T+1+1/\eta.
\]

For `D C_T > 0`, choose `eta=1/sqrt(D C_T)`; the zero case follows directly.
This refinement changes constants. The `O(p^3 U^4)` full-variance order and
the `O(d^5 U^4)` ideal-chain inverse-gap order are unchanged.
