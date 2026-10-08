# Localized exposure variance

Verified exposure integration, 8 October 2026. The new module
[`PhysicalExposureVariance.lean`](../formal/Math115/PhysicalExposureVariance.lean)
connects the actual upstream finite word-prefix decomposition to the completed
physical leaf-energy comparison. The targeted module build has completed
successfully, including the separate verified `PathVariance` dependency.
A temporary `#print axioms` audit of its seven principal statements completed
successfully; every statement uses only `propext`, `Classical.choice`, and
`Quot.sound`. Parent-managed integrated receipts remain the publication record.

The principal statement `physical_transversal_variance_localized` is

\[
 \operatorname{variance}(w,H)
 \le C_T\operatorname{physicalEnergy}(\mathrm{hardMarginal},H),
 \qquad
 C_T=\frac{U(U+1)}2
      \left(2+\frac{(p-1)(U+1)^2}{2}\right).
\]

Here `w` is the unchanged physical completion-weighted word distribution,
`p` counts small cells, and the variance is unnormalized as in the source.
The assumptions are explicit: `U>=2`, uniform small-cell capacity `U`,
large-cell capacities at least two, and the same residual-table capacity
bound required by the completion-retaining repair injection. All zero-mass
contexts and children are included.

The proof checks four connections:

1. Exact finite exposure telescoping retains the sum of every prefix
   contribution, rather than replacing each depth by a common budget.
2. The canonical suffix enumeration used for physical ownership gives the
   same zeroth and first moments as the source's actual word fibres. This
   follows from the existing enumeration-independent physical choice-fibre
   identity, not from an assumed equality of enumeration conventions.
3. The sharper path theorem gives each prefix variance at most
   `U(U+1)/2` times its sum of weighted adjacent contrasts. The hard child
   masses satisfy the source's proved no-valley property, which includes
   interval support and permits hard zeros.
4. Reindexing depth and prefix choices into canonical owners counts each
   owner once. The previously verified physical owner-sum bound then supplies
   the displayed coefficient, without an extra exposure-depth factor.

The first completed theorem concerns the balanced transversal. The verified
[`PhysicalFullVariance.lean`](../formal/Math115/PhysicalFullVariance.lean)
uses the source's existing finite repair inequality, actual repair injection,
repair-edge energy bound, and positive-support encoding to prove

\[
 C_{\rm full}=(1+2p^2)C_T+2.
\]

`physical_full_variance_localized` proves this bound on the exact disjoint
union of balanced words and positive defect profiles, using the actual
completion-retaining repair injection. `physical_variance_localized` then
removes the zero-weight profiles and proves the bound for every observable
on the source's actual positive-weight physical state space. Both retain
the explicit width and residual-capacity hypotheses above.

The full-variance module compiled successfully with direct Lean using
`-j1 -DautoImplicit=false`. A separate `#print axioms` audit of both principal
statements also exited successfully and reported only `propext`,
`Classical.choice`, and `Quot.sound`. This checkpoint retains the source's
factor-two repair estimate; the smaller cross-term coefficient is a
separate refinement.

Comparing the full bound to the sampler's actual Dirichlet form is a
separate step. No full mixing exponent is certified by these variance
theorems alone, and the algorithm's runtime and dense-sampler comparisons
require their own integration.
