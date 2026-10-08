# Integrating literal leaf energies with the physical graph

Verified integration step, 8 October 2026. The new module is
[`PhysicalLeafEnergy.lean`](../formal/Math115/PhysicalLeafEnergy.lean), over the
unchanged `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` definitions.
Compilation status is reported at the end of this note.

The preceding formal ownership result recovered the special slot, adjacent
level and prefix from an abstract pair of removed-unit endpoints. This module
connects that argument to the sampling paper's actual row-major coordinate
map and proves the associated global energy accounting statement.

## Exact object being localized

For a fixed physical context, the module maps upstream `leafEdges` through
`ExcessContextProfiles.assemble` and calls the resulting finite edge set
`physicalLeafEdges`. Its energy is the sum of `edgeTerm` over those oriented
edges, divided by two. This matches the upstream unordered-energy convention.

This is the image of the literal leaf-clique edges. It is **not** the induced
exchange graph on the union `leafVertices`: such an induced graph can contain
extra edges between different leaves. The latter is insufficient for a claim
that every edge recovers one transport leaf.

`leafEnergySum_eq_physicalLeafEnergy` proves exact equality between the
upstream recursive leaf sum, with the weight and observable composed with
`assemble`, and that image energy. It uses the existing literal edge-sum
identity and the injectivity of the physical assembly map.

`leafEnergySum_truncate_eq` supplies an additional exact bridge: if the root
display is in its declared box and has total `R+1`, every valid leaf vertex
is in the corresponding extended box with total `R+sum(Ms)`. Truncating the
weight outside that slice therefore leaves the literal leaf energy unchanged.
This permits the auxiliary kernel to retain the truncation required by repair
without changing the energy that will be charged globally.

`physicalLeafEnergy_tendsto` also proves continuity of the fixed finite
physical leaf energy under pointwise convergence of weights, including
hard-zero limits. This statement requires neither positive limiting vertex
weights nor convergence of currents.

## Physical support and global owners

The physical membership theorem assumes `1 <= ell <= U`, `U >= 1`, a bounded
prefix and uniform small-cell capacity `U`. Every root display then lies in
its box. Balanced branch embeddings stay in the box, and removing a unit
cannot increase a coordinate. The existing upstream `leaf_pattern` and
`context_vertex_mem` therefore put each mapped endpoint in the actual
physical vertex set. Existing `assemble_removeOne` ensures that the two
holes remain outside the fixed prefix.

`physicalLeafEdges_owner_unique` proves that a shared literal physical edge
forces equality of the two exposed cells, equality of their adjacent levels,
and agreement of their assignments on all earlier small cells. It uses the
actual upstream `base_pair_total` and `assemble_removeOne` lemmas, then the
previously verified global display-ownership bridge. The result allows
different suffix enumerations on the two sides. It does not infer equality
of unused suffix values in arbitrary ambient prefix encodings.

To sum contexts without duplicates, `Owner` is the finite dependent type

```
exposed small cell
× positive adjacent level in 1,...,U
× choices in 0,...,U on exactly the earlier small cells.
```

An owner's ambient prefix is formed with upstream `prefixExtension`; its
suffix enumeration is fixed canonically. No ignored future assignments or
alternative enumeration are included in the key. Consequently `owner_unique`
gives genuinely disjoint physical edge sets.

The resulting theorem is

\[
 \sum_{o\text{ a canonical physical owner}}E_o(f,H)
 \;\le\;\operatorname{physicalEnergy}(f,H).
\]

It has no multiplicative charge for the number of exposure depths or adjacent
levels. It assumes only nonnegative weights and an arbitrary real observable,
so zero-weight endpoints are permitted and contribute zero exactly. The
small-cell boxes and physical state patterns are the original upstream ones.

## Hard limits and actual adjacent means

The subsequent extension closes the local hard-limit bridge.
`leafEnergySum_tendsto` proves continuity of the recursive finite leaf sum
itself. `integer_root_leaf_transport_quarter_limit` then takes the limit of
the previously verified quarter-coefficient transport inequality. Its only
strict positivity assumptions are the two limiting endpoint marginal masses;
their positivity eventually holds along the approximating family. There is
no limit of recursively defined currents.

`integer_box_root_leaf_transport_quarter_limit` applies this argument to
the source's **boxed, fixed-total zero extension**. The original endpoint
sums and leaf energy are restored by exact identities, while the auxiliary
kernel retains its truncation. `context_box_leaf_transport_quarter` applies
the result to the literal physical `contextSoft` and `contextHard` families,
using the upstream proof of the soft signature hypotheses.

Finally, `adjacent_physical_leaf_transport_quarter` uses the existing
completion-retaining conditional repair theorem on precisely this truncated
auxiliary kernel. For an exposed cell with `n` later small cells, adjacent
hard child masses `a,b>0`, and their conditional means, it proves

\[
 \min(a,b)(\mu_{\ell-1}-\mu_\ell)^2
 \le \left(2+\frac{n(U+1)^2}{2}\right)E_{s,\sigma,\ell}.
\]

Here the energy is the literal physical leaf energy defined above. The old
adjacent coefficient was `2+2n(U+1)^2`. The verified refinement uses the
continuous quarter bound; it does not claim the additional floor-function
rounding refinement discussed in the manuscript.

`ownerContrast` defines the left side for every canonical owner. If a child
has zero mass, its contrast is zero because the minimum mass is zero. This
does not assign a probabilistic conditional mean to an empty child.
`ownerContrast_le_ownerEnergy` handles these zero cases explicitly.
Combining that comparison with unique physical ownership gives
`sum_ownerContrast_le_physicalEnergy`:

\[
 \sum_o \operatorname{ownerContrast}(o)
 \le \left(2+\frac{(p-1)(U+1)^2}{2}\right)
       \operatorname{physicalEnergy}(\mathrm{hardMarginal},H),
\]

where `p` is the number of small cells (and `p-1` is natural-number
subtraction, so the empty case is also covered). This statement includes all
prefixes and adjacent levels. Its assumptions include `U>=2`, uniform
small-cell capacity, large-cell capacities at least two, and the same
residual-table capacity bound used by the upstream repair injection.

## Remaining integration work

This module establishes the localized hard transport and global adjacent
contrast sum. It does not by itself establish the improved full Poincare or
spectral-gap theorem. The remaining steps are the sharper path variance,
exact exposure-variance summation, full-profile repair comparison, and
Dirichlet-form comparison for the actual sampler. Further exposure work is
kept in a separate module so this completed step remains independently
reviewable.

The energy module uses a fixed finite graph and nonnegative weights directly;
it does not take a limit of flows or assume that zero-mass children have
defined conditional means. Original transport signature hypotheses,
including ordinary-slot widths at least two, remain necessary when connecting
its energy conclusion to the transport theorem.

## Verification status

The targeted `lake build Math115.PhysicalLeafEnergy` completed successfully
against the pinned upstream source and Lean 4.34.1, including the hard-limit,
physical adjacent-mean, and global contrast-sum extensions. A separate
temporary `#print axioms` audit of sixteen principal energy, ownership,
hard-limit, and actual physical transport statements completed successfully.
Every audited statement uses only `propext`, `Classical.choice`, and
`Quot.sound`. The parent verification workflow owns the final audit imports
and receipts. The module's two compiler warnings concern unused section
variables, not missing proofs.
