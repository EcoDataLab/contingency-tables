# Zero-margin removal and restoration of table laws

**Compilation failed; no verified theorem is claimed.** This candidate is
`ResearchPhysicalTraceJoin.ZeroMargins`, namespace `Math115.PhysicalTraceJoin`.
The final [source](formal/ResearchPhysicalTraceJoin/ZeroMargins.lean) and all
five failed compilation attempts are retained. It is excluded from the
verified claims ledger and standard build target. No assumption audit ran.

The remaining compiler error is confined to `zeroMarginEquiv_extend_entry`:
after case analysis, Lean leaves the inverse of the composed equivalence
unreduced. The generic subtype-instance mismatch from earlier attempts was
resolved. The rest of the file reports no elaboration errors in attempt 05,
but that does not constitute successful module compilation or an axiom audit.
The [final diagnostic](attempt-05/compile.stdout.txt) and
[attempt inventory](attempts.json) give the exact evidence. A next repair can
try controlled reduction of `Equiv.trans` and the inverse projections before
simplifying the nested conditionals; this suggestion has not been tested.

The descriptions below specify the candidate's intended theorem. The
separate [AI source review](AI-SOURCE-REVIEW.md) supports its mathematical
interpretation; it does not override the failed compiler result.

For arbitrary finite row and column types and natural margins, set

```
Iplus = {i | 0 < r_i},   Jplus = {j | 0 < c_j}.
```

The draft constructs an explicit equivalence

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

| English claim | Candidate Lean statement | Explicit hypotheses |
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

## Rechecking the candidate

Use the pinned Lean 4.34.1 toolchain and prepared dependency objects for
`OAI.Combinatorics.ContingencyTables.Transport.RectangleCompletions` and
`OAI.Combinatorics.ContingencyTables.Machines.FiniteFairBits`. Run the command from this packet directory. The recorded
runs used two compiler threads, an 8 GiB memory limit and `autoImplicit=false`:

```sh
LEAN_PATH=<prepared-object-roots> lean -j2 -M8192 -DautoImplicit=false \
  formal/ResearchPhysicalTraceJoin/ZeroMargins.lean
```

This command is expected to fail on the retained candidate. After a proof
repair, require successful full compilation and a fresh environment audit
before adding any theorem to the verified claims. The source hash and
compiler hash are recorded in each attempt's compilation receipt.
