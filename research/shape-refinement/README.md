# Shape, block-floor and cutoff certificates

11 October 2026. This additive packet compiles the scalar proposal/scale
bounds and an actual physical half-acceptance improvement for smaller blocks.
It supports the [shape derivation](../../docs/shape-aware-defect.md) and
[constant-padding refinement](../../docs/constant-padding.md).

| English claim | Lean statement | Hypotheses and scope |
|---|---|---|
| The available-pair degree envelope is at most `4p-3`. | `Math115.ShapeDegreeBound.degreeEnvelope_le` | Natural layout counts, dimensions at least two and nonempty small mask; the physical move catalog interpretation is reviewed separately. |
| Rational/dyadic normalization obeys the sharper scalar allowances. | `Math115.ShapeScalarScales.proposal_rational_coefficient_le`, `proposal_dyadic_coefficient_le` | The explicit variance coefficient and global proposal envelope, including dyadic rounding. |
| The guarded cutoff permits at most factor-two padding growth. | `Math115.ShapeScalarScales.guarded_padded_count_le_twice` | Actual marked ordinary-table cells have both margins above the computed cutoff; uses the full table's donor count. |
| Local dimension floors meet the existing completion interface. | `Math115.ShapeScalarScales.localDimension_conditions` | Explicit block counts/local dimension, retaining the generic completion program's required floors. |
| Block floors imply half acceptance for every actual reference edge. | `Research.AcceptancePadding.reference_edge_acceptance_block_floor` | `min(R,C)L≥3(R-1)(C-1)`, actual adjacency, ordinary cap identification and reference indices. |
| The explicit rounded padding meets that condition. | `Research.AcceptancePadding.reference_edge_acceptance_floorPadding` | Same physical hypotheses, with `floorPadding` derived from the block dimensions. |
| The associated cutoff/count and bounded-aspect envelopes hold. | `Research.AcceptancePadding.outerCutoff_budget`, `bounded_aspect_gap` | Explicit dimension/shape inequalities. These scalar bounds do not assemble a new global physical gap. |

The [fresh receipt](results/verification.json) gives exact types, source and
compiler hashes, reused import hashes, and every headline's full dependency
closure in the [environment audit](results/audit.stdout.json.gz). It freshly
compiles shared earlier modules; counts overlap and are not new theorem totals.
Only standard Lean axioms occur. The retained unused-simp warning changes no
statement. AI source review is separate from compiler execution.

```sh
python3 research/repair-accept/verify.py --scope shape-refinement \
  --output .local/shape-refinement-fresh
```

Use the pinned compiler, built baseline imports and a new output path. This
is ordinary compilation with trusted reused dependencies, not strict Comparator
replay or a fresh default-target rebuild. The later retained-root and constant
padding combination improves the general reviewed envelope further to d¹⁰.
