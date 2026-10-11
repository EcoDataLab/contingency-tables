# What the current generic repair assumptions cannot improve

The remaining `p` factors cannot all be removed by rearranging the existing
generic repair inequalities. An abstract graph family satisfies their
transport, load and degree scales and still needs order `p⁴U²` in the
normalized defect trace. This is a limitation of that proof information,
**not a lower bound for contingency-table chains**.

Take `p=r²`, `r≥2`, and `q=rU+1` balanced centers in a path. Each center has
`k=p(p−1)` unit-weight defect leaves joined to it by unit repair edges.
Label the leaves by ordered distinct pairs. Within each fiber, join leaves
sharing their first label into cliques of size `p−1`; connect adjacent fibers
by one defect edge. There are no balanced-to-balanced edges, each defect
has one repair neighbor, and repair plus labels is injective. Full defect
degree is at most `p+1`.

For the observable equal to the fiber number on each fiber, all internal
and star-elimination energies vanish. Bridge energy is `q−1`, whereas
unnormalized defect variance is `kq(q²−1)/12`. At proposal `1/[2(p+1)]`, the
inverse gap is therefore at least

```
2(p+1) kq(q+1)/12 = Θ(p⁴U²).
```

The balanced transversal coefficient has order `q²=Θ(pU²)`: a linear
observable supplies the lower bound; three-edge repair/bridge/repair paths
and the ordinary path variance inequality give upper bound `3q(q−1)`.
Thus the example simultaneously permits the current transversal scale,
quadratic repair load and linear defect degree. All conductances are one,
so it also meets half acceptance. It is not an ordinary-table construction.

There is a useful exact alternative decomposition on the **actual** table
graph. Write `c_bx` for accepted conductance from balanced `b` to defect `x`,
`a_x=Σ_b c_bx`, `S_b=Σ_x c_bx`, and let `H_b` be the conductance-weighted
mean of a defect observable around `b`. Then

```
Var_a(g)=E_star(g)+Var_S(H),
Var_(w,D)(g)≤2Var_a(g).
```

The second inequality uses the designated accepted repair edge to get
`w_x≤2a_x`. Each incidence is counted once, including defects with two
balanced neighbors. A physical bound on `Var_S(H)` better than the generic
repair comparison could remove a power. However, `S_b` tilts the ordinary
completion-count law by accepted degree. Existing no-valley and signature
theorems for ordinary table counts do not automatically hold for this tilt.

The [exact supplementary checks](../reports/direct-defect-variance.json)
verify these identities and retain the abstract graph formulas. They also
exhibit actual one-small-column tables with repair load exactly `p(p−1)`,
so that pointwise load cannot simply be replaced by order `p`. That example
does not lower-bound the actual table chain's gap: its additional exchange
geometry could still support a better argument.

The [zero-range comparison](zero-range-subclass.md) now supplies such an
argument for a restricted unique-completion family. Its actual repair load
can remain quadratic while the defect trace has a reviewed `O(d⁴)` bound.
The proof identifies the accepted shared-defect graph with a classical
composition-transfer process and keeps the variance and energy normalizers
matched. Extending that identification to general completion weights and
the marked incidence law remains open.

The [thin mixed-family comparison](thin-parallel-comparison.md) provides a
second concrete improvement. It has a nontrivial dense completion block
and an explicit d⁶ allowance for selected `3×2b` margins. Each auxiliary
grid edge has `b²` parallel physical defect edges; averaging them cancels
the quadratic repair load. Shared defects connect the remaining slice
means. The proof still uses its particular margins and near-uniform dense
counts, so it does not yet close the general center-transport problem.

The [growing-row comparison](growing-row-comparison.md) extends that mechanism
to specified `(R+1)×2b` tables. A grid-center move has
`b((R+1)b−2)` distinct actual DD copies, with endpoint-pair charge at most
`b(R−1)`. Exact conditional composition couplings then give an explicit
bounded-aspect d⁵ allowance; a classical zero-range comparison improves
its asymptotic order to d⁴ with an unextracted constant. Both dimensions
may grow. The actual repair law is retained, but the proof still depends
on product dense counts comparable within a fixed factor. Establishing
center transport for arbitrary completion weights is the remaining general
obstacle; the restricted family does not supply that missing inequality.

The [higher-total extension](growing-row-extension.md) permits
`1≤h≤U/[2(R−1)]` without losing those exponent orders. Its supporting
[junction comparison](junction-star-comparison.md) is more general:
`E_J(F_g)≤12E_star(g)` holds for ordinary margins under the stated capacities
and actual half acceptance. Incoming junctions charge the full repair law;
the joint within-fiber noise and center-error identity avoids an artificial
factor growing with h. This closes that energy comparison, but the general
weighted center Poincare inequality remains unproved.
