# Constant completion padding

11 October 2026. The ordinary-table zero-entry bound and actual physical
reference acceptance theorem are compiled. They prove that **padding L≥7
suffices for half acceptance independently of completion-block dimensions**.
The [mathematical proof](../../docs/constant-padding.md) explains the weighted
switching and finite convolution argument.

For a marked cell with row/column margins a,b in an R×C ordinary table,
R,C≥2, set `alpha=(C-1)/(a+C-1)`, `beta=(R-1)/(b+R-1)`. The proved uniform
probability bound is `P(X=0)≤alpha+beta-alpha*beta`.

| English claim | Lean statement | Hypotheses and scope |
|---|---|---|
| Weighted unit switches compare adjacent actual table counts. | `Research.WeightedIncidence.weighted_level_recurrence` | Ordinary unrestricted natural tables; exact labeled incidence injection, with safe natural subtraction. |
| Normalized composition tails have decreasing residual ratios and the stated mean. | `Research.CompositionSurvival.tail_nbu`, `tail_sum` | All natural margins and shape parameters, including zero parameters/support endpoints. |
| Two such tails give the reciprocal convolution bound. | `Research.CompositionSurvival.composition_reciprocal_bound` | Common finite cutoff beyond both supports; NBU and exact means are derived. |
| Actual counts dominate zero-level count times the tail convolution. | `Research.ReciprocalZero.zero_count_times_convolution` | Both dimensions at least two; the actual weighted recurrence supplies the induction. |
| The uniform zero-cell probability obeys the sharp bound. | `Research.ReciprocalZero.zero_entry_probability_reciprocal` | Both dimensions at least two, equal totals; ordinary table nonemptiness supplies the positive denominator. |
| A signed translation accepts at least half the tables at L≥7. | `Research.ReciprocalZeroPhysical.accepted_half_seven` | Full residual row/column floors, equal totals and the explicit directional adjustment bounds. |
| Every actual directed physical reference move accepts at least half. | `Research.ConstantPaddingAcceptance.reference_edge_acceptance_seven` | `L≥7`, actual physical adjacency, `hB`, `hcap` and reference indices; full floors and totals are derived. Singleton blocks use the existing zero-donor argument. |

The [fresh receipt](results/verification.json) and [compiled environment](results/audit.stdout.json.gz)
retain exact statements, dependency closures, and source/compiler/imported-object
hashes. The scope freshly compiles the shared earlier acceptance sources too;
its declaration count overlaps those packets. Only standard Lean axioms occur.
Separate AI source reviews checked the recurrence, tail induction, probability
divisions and actual physical wrapper. No outside human review is claimed.

The [first integration failure](failed-integration-attempt/) is retained: the
runner omitted a shared import, then the final scope compiled it explicitly.
The successful receipt uses trusted baseline dependencies and compiler. It
is ordinary Lean compilation, not a default-target rebuild or strict Comparator
check. Caps/structural zeros are outside the ordinary switching theorem;
`hcap` is needed when identifying a physical completion fiber with that model.
Empty completion rectangles use the separate existing branch.

This result does not provide a general accurate completion sampler at L=7.
The existing generic completion program needs larger floors. The full d¹⁰
global gap and encoded sampler remain separate obligations.

```sh
python3 research/repair-accept/verify.py --scope constant-padding \
  --output .local/constant-padding-fresh
PYTHONPATH=src python3 experiments/reciprocal_zero_bound.py \
  --output .local/reports/reciprocal-zero-bound.json
```

The formal runner requires the pinned compiler and built baseline imports.
Use a new output path. The [exact finite report](../../reports/reciprocal-zero-bound.json)
supplements the arbitrary-parameter proof with independent table enumeration
and directed physical-edge checks.
