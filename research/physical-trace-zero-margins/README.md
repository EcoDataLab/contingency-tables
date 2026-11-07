# Zero-margin removal and restoration of table laws

23 October 2026. The [Lean module](formal/ResearchPhysicalTraceJoin/ZeroMargins.lean), `ResearchPhysicalTraceJoin.ZeroMargins`,
passes ordinary compilation and its full assumption audit. Separate
AI source review found no semantic objection.

For arbitrary finite row and column types and natural margins, set

```
Iplus = {i | 0 < r_i},   Jplus = {j | 0 < c_j}.
```

The construction supplies an explicit equivalence

```
Table(r,c) ≃ Table(r restricted to Iplus, c restricted to Jplus).
```

Restriction keeps the entries at positive-margin row/column pairs.
Restoration inserts zero at every removed row or column:

```
restore(X)_(i,j) = X_(i,j)  if r_i>0 and c_j>0,
                   0       otherwise.
```

Every feasible nonnegative table has zero entries in a zero-margin row or
column. Attaching that support proof changes no table. The construction
then reuses the existing rectangle restriction/extension equivalence,
whose margin proofs use finite subtype sums. Neither direction selects an
arbitrary feasible table or enumerates tables.

The equivalence itself needs no equal-total, nonempty-support, or positive
original-margin premise. It includes total zero and empty original or
positive-index types. Uniform-law statements use equal original totals
to derive nonempty original and restricted table spaces. Existing
equivalence transport identities then prove

```
restoreLaw(uniform restricted tables) = uniform original tables,
TV(restoreLaw(q), restoreLaw(q')) = TV(q,q'),
TV(restoreLaw(q), uniform original tables)
  = TV(q, uniform restricted tables).
```

| English claim | Lean statement | Explicit hypotheses |
|---|---|---|
| Entries in zero-margin rows or columns vanish. | `table_entry_zero_of_row_zero`, `table_entry_zero_of_column_zero` | Supplied feasible ordinary table; corresponding original margin zero. |
| Restriction and explicit zero extension are inverse. | `zeroMarginEquiv`, `zeroMarginEquiv_restore_restrict`, `zeroMarginEquiv_restrict_restore` | Arbitrary finite row/column types and natural margins. |
| The equivalence uses literal restriction and nested-if zero insertion. | `zeroMarginEquiv_restrict_entry`, `zeroMarginEquiv_extend_entry` | Supplied original or restricted table. |
| Restoring two laws preserves their TV distance exactly. | `restoreZeroMarginsLaw_variation` | Any rational laws on restricted tables. |
| Restoring a uniform restricted law gives a uniform original law. | `restoreZeroMarginsLaw_uniform` | Equal original totals; nonemptiness is derived. |
| Restoration preserves error against the appropriate uniform target. | `restoreZeroMarginsLaw_uniform_variation` | Equal original totals and any rational restricted-table law. |

This is an ordinary-table probability-law interface. It does not implement
list preprocessing, choose an ordering of retained indices, transport a
cutoff or physical small mask, prove nonempty defect support, initialize a
defect walk, repair a physical joint, or complete the original-table sampler.
No finite-word implementation or runtime claim is supplied.

## Evidence and replay

Ordinary Lean compilation passed in 101.64 seconds;
the compiled-environment audit passed in 157.24 seconds. The
[receipt](attempt-06/verification.json) binds the source, compiled object,
all module declarations and 4 complete headline dependency closures.
Only `propext`, `Classical.choice` and `Quot.sound` occur. The dependency
objects match the recorded accepted or newly compiled input hashes.

The pinned compiler and reused baseline objects remain trusted. This is
separate from the historical default-target Linux build and strict Comparator
task. [AI source review](AI-SOURCE-REVIEW.md) is not human review or independent
kernel verification. All five failed compiler attempts are retained unchanged;
the [scope check](attempt-06/scope-check.json) and [proof diff](attempt-06/proof-only.diff)
record proof repairs. Source and compressed audit bytes are unchanged;
public diagnostic paths and trailing whitespace are projected.

Prepare the pinned Lean compiler and the dependency objects named by this
module's imports, including `ResearchAudit.EnvironmentAudit`, then run:

```sh
LEAN_PATH=<prepared-object-roots> bash REPRODUCE.sh /absolute/path/to/new-output-directory
```

The script compiles this additive module and audits its loaded environment.
It downloads or rebuilds no dependencies. The script is syntax-checked; the
saved run used the same source and compiler options. The claims-ledger
validator checks the saved source, statements, closures and object inventory.
