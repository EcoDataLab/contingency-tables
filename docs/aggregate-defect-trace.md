# A stronger bound for the same defect chain

The completed-table incidence argument now has a concrete Lean assembly for
the **same actual rational defect trace** as the earlier
[physical trace theorem](physical-defect-trace.md). Write
`d=10+(m+1)(n+1)` and `s=m+n−2`. At `U=11ds, L=7`, it proves

```text
Var(g) ≤ 34848 d⁵ s³ E(g).
```

For dimensions satisfying `s²≤Ad`, this gives the inverse-gap allowance
**`34848 A^(3/2)d^(13/2)`**. Keeping `A` bounded allows nonsquare rectangles;
if one dimension stays fixed while the other grows, this is still a `d⁸`
bound. The preceding compiled shape bound was `3872d⁶s²`, hence `d⁷` at
bounded aspect. This refinement saves a half power there. It bounds the
ideal chain's variance relative to its energy; the complete sampler and
its machine-time degree are separate work.

## What changes in the proof

A small cell lies in an original row or column whose margin is below `U`.
Let `p` be the number of small cells, `a,b` the counts of small rows and
columns, and `k=a+b`. Instead of bounding every repair donor independently,
the proof groups donors in each **full completion table**. Selected row and
column totals constrain their combined contribution:

```text
K₀ = kU²+pU
actual correction c_l ≤ 2K₀ max(z_(l−1),z_l)
C_T = U(U−1)+4K₀.
```

The map into the repaired residual child is injective on full completed
defects, including the large-large crossing. This retains the multiplicity
that a count of selected profiles alone would lose. The actual boxed kernel,
row-major exposure owners, and designated repair then give full-state
variance at most `2p²C_T` times physical graph energy.

The accepted-conductance comparison loses a factor of two. Eliminating the
balanced stars and normalizing on positive defects gives coefficient
`4Q·(2p²C_T)≤32p³C_T`, with the existing proposal allowance `Q=4p−3`.
There is no full-mass/defect-mass factor. Since `p≤d`, `k≤s+2`, and this cutoff
ensures `4p≤U+1`, we have `C_T≤9sU²`; substitution gives `34848d⁵s³`.

Both the reference-completion and missing-reference unit branches use the
same canonical kernel and proposal normalization in this theorem. The
[sharper reviewed coefficient `15488`](aggregate-incidence.md) uses additional
asymmetric/transposed moment estimates and a separate faster unit proposal.
That coefficient remains reviewed mathematics, not the coefficient of this
compiled theorem.

## Compare the actual coefficients

Both compiled inequalities apply to the same kernel under the same physical
hypotheses, so one may use their minimum. Compare the earlier **shape bound**,
not only its coarser `431d⁸` corollary:

```text
old coefficient / new coefficient = d/(9s).
```

| Dimensions | Earlier/new coefficient | Smaller certified allowance |
|---|---:|---|
| 2 × 20 | 0.406 | Earlier shape bound |
| 5 × 20 | 0.657 | Earlier shape bound |
| 20 × 20 | 1.319 | New aggregate bound |
| 10 × 100 | 1.153 | New aggregate bound |
| 100 × 100 | 5.730 | New aggregate bound |

These are ratios of upper bounds, not measured relaxation times or sampler
speedups. The new proof need not improve the constant for every finite shape.

## Statements and evidence

All the headline statements below derive their actual correction and
variance bounds internally. Dimensions are finite and ordered; margins are
natural numbers. The trace statements retain `m,n≥2`, `p≥2`, and nonempty
positive defect support at the stated cutoff. They use exact completion
weights. An automatic wrapper handling all degenerate branches remains
separate.

| Claim | Lean statement in `Math115.AggregateDefectTrace` | Additional hypotheses |
|---|---|---|
| Full-state variance coefficient `2p²C_T` | `state_variance_aggregate` | `U≥2`, `p≥2` |
| Same normalized trace coefficient `32p³C_T` | `actualRationalTrace_poincare_aggregate` | `U≥2`, `L≥7`, `p≥2`, nonempty positive defects |
| Shape coefficient `34848d⁵s³` | `actualRationalTrace_poincare_aggregate_shape` | `m,n≥2`, `U=11ds`, `L=7`, trace hypotheses |
| Squared aspect certificate `Var(g)²≤34848²A³d¹³E(g)²` | `actualRationalTrace_poincare_aggregate_aspect_sq` | Shape hypotheses, `A≥0`, `s²≤Ad` |

The last statement is polynomial and uses the displayed squared form in
Lean. Nonnegative variance and energy give its fractional-power
interpretation. It does not prove a lower bound on the true relaxation time.

The [formal packet](../research/aggregate-defect-trace/) supplies exact
sources and reproduction instructions. Its [combined public-source receipt](../research/aggregate-defect-trace/results/verification.json)
records fresh compilation of all 49 research modules, the pinned helper and
the auditor. The audit passed with 1,264 selected declarations, including
1,118 theorems, and eight complete headline dependency closures. Only
standard Lean axioms occur. The [separate source review](aggregate-defect-trace-review.md)
checked the mathematical linkage and comparison above.
This is ordinary Lean verification with trusted pinned compiler and baseline
imports. It does not enlarge the historical default Linux audit or constitute
Comparator acceptance. The mathematical/source review uses separate AI agents;
no outside human review is claimed.

The remaining algorithmic work is to realize the trace transitions and
completion calls with bounded bits, compose the output correction and schedule,
and prove the resulting encoded program's charged cost. A smaller inverse-gap
allowance alone does not complete those steps.
