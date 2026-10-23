# Retained correction and quadratic-width transport

11 October 2026. The complete abstract path theorem proves
`Var_z(h) ≤ [N(N+1)+2K] Σ E_l`, including zero stencil values and nonzero
exterior corrections. The [physical derivation](../../docs/retained-root-spectrum.md)
uses it to obtain `32p⁴U²` rational and `64p⁴U²` dyadic inverse-gap allowances.
With the [new padding cutoff](../../docs/reciprocal-padding-growth.md), these
become **431d⁸ / 862d⁸** for arbitrary aspect ratios and order **d⁷** for
bounded-aspect rectangles. The physical derivation is reviewed mathematics;
its changed defect trace still needs Lean assembly. The subsequent
[physical packet](../physical-spectral/) closes the actual context, exposure
and full graph variance, and proves d⁹ for the original normalized chain.

| English claim | Lean statement | Hypotheses and scope |
|---|---|---|
| Adjacent physical means satisfy the retained correction/leaf-energy inequality. | `Math115.RetainedRootPhysical.adjacent_physical_box_leaf_transport_retained` | Actual boxed soft-to-hard context, uniform width at least two, valid prefix/display, positive adjacent child masses. Truncation stays inside the correction kernel. |
| One fixed kernel supplies every stencil entry, and its limiting coefficient is nonnegative. | `Math115.RetainedRootPhysical.retainedRootCoefficient_shift`; `OAI.ContingencyTables.IntegerWeightedTransport.retainedRootCoefficient_nonnegative_limit` | Valid physical display; explicit coordinate boundaries, soft-signature inequalities and positive hard child masses. Interior support boundaries need not vanish. |
| The actual boxed correction is at most `r Q_U` times the larger adjacent mass. | `Math115.RetainedPhysicalCap.physical_correction_le_adjacent` | Same boxed moment expansion and actual auxiliary repair; `hB`, `hcap`, prefix validity and `U≥2`. This does not assume the desired correction cap. |
| Positive child support has the stated physical diameter. | `Math115.RetainedPhysicalSupport.positive_physical_support_diameter` | A positive child supplies an actual residual table; original small-line constraints bound its cell by the incident margins. At the original small-cell cutoff, diameter is at most `U−1`. |
| Restricting to positive support preserves actual variance and supplies a mode. | `Research.PositiveSupport.positive_support_restriction` | Nonnegative finite no-valley weights with nonempty positive support; exact mass/mean/variance reindexing and an owned-energy subset bound. Singleton variance is separately zero; all-zero contexts require their own trivial branch. |
| A positive-resistance path has an attained positive Rayleigh minimum and exact prefix flux. | `Research.SpectralPath.exists_path_rayleigh_minimizer` | `N≥1`, positive vertex masses and positive edge resistances. Compactness, first variation and the all-observable variational bound are proved, not assumed. |
| Retaining all three correction terms gives the quadratic-width path bound. | `Research.SpectralRetained.retained_spectral_variance_bound` | Positive unimodal masses, nonnegative corrections, interior cap `c_l≤K max(z_(l−1),z_l)`, nonnegative stencil `Xi_l`, and local contrast bound `(Δh_l)²≤Xi_l E_l`. Gives `N(N+1)+2K`, including `Xi_l=0`; no spectral or Poincare premise. |
| The tight scalar repair expression is at most `2p³V²`. | `Math115.RetainedRootSquare.tight_fullCoefficient_bound` | Natural `p,V≥2`; context expression `(V−1)V+2(p−1)floor((V+1)²/4)`. This is a scalar implication, not the full physical gap theorem. |
| The improved growth budget gives padded count at most twice original count. | `Research.GrowthRefinement.doubled_growth_twice` | A supplied product-count inequality, `H>0` and `47qs≤32H`. The actual ordinary-table bridge is compiled separately in `Research.ReciprocalCount`. |
| New scales give `3872d⁶s²`, bounded-aspect d⁷ and rounded general d⁸. | `Research.GrowthRefinement.shape_gap_width_square`; `bounded_aspect_gap_width_square`; `arbitrary_aspect_width_square_integer` | Scalar hypotheses `p≤d`, `V≤11ds`, the `32p⁴V²` allowance, and respectively `s²≤Ad` or `3s+13≤d`. The complete physical scale/gap assembly is separate. |
| All actual L=7 residual totals fit the completion cap. | `Math115.LegacyResidualCap.all_state_l7_cap` | Actual balanced/defect state; residual total at most original total plus `7RC`. The legacy completion law and remaining adapter are described [separately](../../docs/legacy-completion-backend.md). |

The [fresh expanded receipt](spectral-results/verification.json) records exact
statements, compiler/source hashes, imported-object hashes, and full dependency
closures for the current headlines in the [environment audit](spectral-results/audit.stdout.json.gz).
The inventory enumerates every declaration defined in the selected compiled
modules, including earlier mode-anchor and scalar results. The older
[receipt](results/verification.json) retains its original d¹⁰ component scope;
its overlapping counts are not added to the new scope or the default target.

Only standard Lean axioms occur. Compiler and reused baseline imports remain
trusted; these are ordinary compiler checks, not strict Comparator replay or
a fresh default-target rebuild. Separate AI agents reviewed the sources and
mathematical interfaces; no outside human review is claimed.

The general dimension bound works at the actual original capacity `U`, where
small-cell classification directly gives the `U−1` support bound. The sharper
instance helper reconstructs the whole context at effective width `V`; that
graph/energy equivalence remains a reviewed mathematical argument. Conditional
variance telescoping, physical edge ownership and repair are now assembled in
the [physical packet](../physical-spectral/), which also discharges `hB` and
`hcap` using genuine paper capacity. The new defect trace and its normalization
remain separate.

```sh
python3 research/repair-accept/verify.py --scope retained-root \
  --output .local/retained-root-fresh
python3 experiments/retained_spectrum.py \
  --output .local/reports/retained-spectrum.json
PYTHONPATH=src python3 experiments/reciprocal_padding_growth.py \
  --output .local/reports/reciprocal-padding-growth.json
```

Use the pinned Lean compiler and already-built baseline dependencies, with a
new output directory. The [spectral experiment](../../reports/retained-spectrum.json)
uses exact rational PSD certificates on 150 finite stencils. The
[earlier experiment](../../reports/retained-root.json) also checks actual mixed
completion contexts. Finite checks support boundary cases; the general proof
is separate from those observations.
