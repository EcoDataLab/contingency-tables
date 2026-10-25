# Zero-margin preprocessing and reduced trace preparation

24 October 2026. Stable list filtering, literal matrix restoration, and the
connection to the reduced trace's computed scale and reference guard now have
compiled Lean proofs and full headline assumption audits. The reference draw
still returns a defect-labelled physical completion pair, from a supplied
actual starting defect. The [general repair map](../research/physical-trace-general-repair/)
now returns a feasible ordinary table on padding success. Its inverse-fibre
count and uniform acceptance law remain open.

The checked route is:

```mermaid
flowchart LR
  A[Original margin lists] --> B[Stable positive-margin lists]
  B --> C[Recompute cutoff and branch guards]
  C --> D[Reference schedule with supplied defect start]
  D --> E[Reduced defect and physical completion]
  E --> R[Completion-retaining repair and padding test]
  R -. Inverse-fibre acceptance law still open .-> F[Ordinary reduced table with corrected law]
  F --> G[Literal zero-row and zero-column reinsertion]
  G --> H[Original table]
```

The repair map already produces feasible ordinary reduced tables on success.
The dotted step is the probability correction needed before claiming a uniform
output law. The restoration theorem concerns laws on ordinary tables.

## Ordered lists and executable output

`positiveMargins xs` is the stable filter `xs.filter (fun v => decide (0 < v))`.
The retained position list is the existing `largeIndices (1, xs)`. A checked
strictly increasing equivalence identifies each filtered position with its
original positive position. Repeated margin values therefore remain distinct
rows or columns. Both total sums are unchanged, including empty and all-zero
inputs.

`restoreZeroMarginMatrix xs ys A` is a total ordinary list function. It uses
each retained position's `idxOf` rank to read the reduced matrix and inserts
zero elsewhere. For every valid reduced-table code, the returned code is
exactly the checked table restoration. Its dimensions always match the
original lists; malformed input defaults carry no feasibility guarantee.

For any rational law on reduced ordinary tables, restoration preserves
total variation exactly. Equal totals make the uniform targets nonempty and
give exact preservation of error relative to uniform original tables.

## Recompute the scale before choosing a branch

The wrapper computes `d=10+(m+1)(n+1)`, `U=11d(m+n-2)` and `L=7` on the
**filtered** dimensions. Its small-cell catalog and large-line lists reuse
the existing programs at that cutoff. At a fixed cutoff, retained-cell mask
tests agree literally. Dimension-based retuning can change the cutoff,
mask, physical capacities, budgets and branch.

For example, `[0,600,600]` by `[600,600]` has cutoff 726 and a unit tag;
after filtering it has cutoff 418 and a no-small tag. This fixture is checked
by ordinary Lean reduction. It prevents assuming the physical chains before
and after preprocessing are equal.

The unit row follows the literal classifier definition; the other rows also
have named specification or law lemmas.

| Computed preparation tag | Checked meaning | Remaining implementation |
|---|---|---|
| Deterministic | Either dimension is at most one; every feasible reduced table has the same value and restores to exact original uniform | Construct and dispatch its output in the revised outer program |
| No-small | Both dimensions are at least two and the actual small-cell count is zero | Supply this table branch |
| Unit | Both dimensions are at least two, at least two cells are small, and at least one computed large-line list is empty | Compose the corresponding revised branch |
| Reference | Both dimensions are at least two, at least two cells are small, and both computed large-line lists are nonempty | Supply an actual reduced defect start and the inverse-fibre acceptance law |

The mask is a union of entire rows and columns. With both dimensions at
least two its cell count is zero or at least two; a one-cell case cannot occur.

`positiveTraceReferenceWord_accuracy` connects the reference tag to the
existing literal finite-word schedule. From equal original totals, that tag
and an actual reduced defect start, it derives the necessary cutoff, count
and large-list conditions and proves TV at most `2^-h` to uniform on reduced
defect/completion pairs. Every budget and word width uses the same reduced
data. No completion-accuracy premise or desired-error premise is substituted
for the verified backend.

## Evidence and next interface

| Packet | Checked interface |
|---|---|
| [Ordered lists](../research/physical-trace-zero-margin-lists/) | Stable filtering, ordered indices, total preservation and exact table-law transport |
| [Scale and branch preparation](../research/physical-trace-preparation/) | Actual cutoff/catalog/large-list identities, branch specifications and deterministic law |
| [Reduced reference schedule](../research/physical-trace-zero-margin-preparation/) | Filter-to-preparation composition and the existing finite-word reference accuracy theorem |
| [Matrix restoration](../research/physical-trace-zero-margin-matrix/) | Literal output function and exact valid-table code correspondence |
| [General repair](../research/physical-trace-general-repair/) | Completion-retaining repair, fixed-label recovery and padding-tested ordinary-table output |

Each packet records its exact source, ordinary Lean 4.34.1 compilation,
environment audit and complete headline dependency closures. Only `propext`,
`Classical.choice` and `Quot.sound` occur. Separate AI source review checked
the statements and hypotheses. Compiler and reused dependencies remain
trusted; these packets are not a fresh default-target Linux build or strict
Comparator acceptance. Earlier failed attempts are retained.

Next are the exact inverse-fibre count and acceptance law for the checked
repair map, including a success bound at the recomputed scales. Defect
initialization, empty-support and other branches, fresh bounded
outer retries, encoded realization and charged costs still need assembly.
No complete sampler exponent or practical speedup changed here.
