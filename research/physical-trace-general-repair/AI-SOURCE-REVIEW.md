# Separate AI source review

Final checked source SHA-256: `6c453e98e87b4635fce4fe1075208f3adc1ee388676aa77ab33ef15f2c2d3cd0`.

Date: 2026-10-24.

**Source review passed for the stated map scope. Ordinary Lean compilation and the assumption/declaration audit passed.**

The reviewed `ResearchPhysicalTraceJoin/GeneralRepair.lean` has SHA256 `6c453e98e87b4635fce4fe1075208f3adc1ee388676aa77ab33ef15f2c2d3cd0` (246 lines). The coordinator's attempt-02 compilation receipt records exit code 0, 73.56 seconds, unchanged source, and output object SHA256 `46c02867d4718546cb7a25f78973f798c0f5b2258c7c0645c3cffb8727f6f557`. Diagnostics contain two unused-simp-argument warnings. This reviewer inspected the source and saved receipts but did not compile it.

The immutable `attempt-02/verification.json` records a successful 197.93-second environment audit: 50 module declarations, including 31 theorems, and five complete headline dependency closures. The saved closure sizes are 8,352; 8,343; 9,814; 9,855; and 9,887 declarations. This reviewer verified that every listed closure declaration has a record and no record reports a nonstandard axiom. The only headline axioms are `propext`, `Classical.choice`, and `Quot.sound`. The compressed audit, import manifest, diagnostics, and frozen source hashes match the immutable receipt; the import manifest contains 11,928 objects. Accepted imported objects were reused, as recorded by the coordinator; this is not an independent rebuild of those imports.

## What the checked map establishes

The input is the actual `DefectJoint`: a defect vertex together with its particular sampled physical completion. The source derives `PositiveDefects` and canonical defect labels from that same vertex, then passes the same completion to upstream `completionJointDefect` and `jointRepair`. This is the literal completion-retaining repair, rather than the different reference-star transition translation.

The repaired full table has the padded row and column margins and preserves the original small-row and small-column inequalities. Signed recovery formulas reconstruct both original full views from the repaired matrix and ordered labels. Consequently `(labels,repaired full table)` determines the entire input pair. The source does not claim injectivity of the unlabelled repair.

Every dense entry is unchanged except at a genuine large crossing, where it gains one. Every repaired small entry is strictly below `U`. The balanced-joint packaging retains precisely this same matrix. Its capacity obligation is discharged by `paper_residual_capacity` and `dimension_le_allowance`; it introduces no caller-supplied capacity, count, normalizer, or probability premise.

`TerminalRepairSuccess` tests every repaired large entry against `L`. Only inputs carrying that success proof are unpadded. The output is an ordinary `Table r c`, subtracts exactly the large-cell padding, and repads to the literal repaired matrix. The existing free-scale `successfulJointEquiv` identifies the returned table with exactly that repaired successful joint.

| Claim | Checked declaration | Essential hypotheses |
|---|---|---|
| Labels and repaired matrix determine the actual input | `terminalRepair_labels_table_injective` | Actual defect/completion pair |
| Dense entries are retained, with the designated increment | `terminalRepairedTable_large_entry` | Actual pair; inspected entry is large |
| Balanced-joint packaging retains the actual matrix | `terminalRepairedJoint_table` | Actual pair |
| Output subtracts padding only on large cells | `terminalRepairOutput_entry` | Actual repair passes every large-entry padding test |
| Returned table identifies the same repaired successful joint | `terminalRepairOutput_successfulJoint` | The same actual success test |

These map statements appropriately allow arbitrary natural `U,L` whenever an actual input exists. They do not require positive margins, `U>=2`, `L>=1`, a defect-existence theorem, or a new probability premise. Positivity and nontrivial geometry become necessary for the separate acceptance lower bound. Definitions remain noncomputable mathematical maps; this file supplies no executable list program or encoded runtime theorem.

## Mathematical assessment of the remaining inverse count

This section reviews the proposed argument in `docs/general-defect-output.md`; it is **not** a claim that the inverse-count or acceptance theorem is compiled in this packet.

For a successful balanced pair with full padded table `Y`, write `A` for its selected small entries. Every `A_z<U`, since at least one incident original margin is below `U`. Thus inverse increments remain at most `U` in both small views and their complementary profile encoding.

For a small crossing `z=(row(t),col(s))`, inverse full views are `X=Y+e_t-e_z` and `Q=Y+e_s-e_z`. For distinct labels they are nonnegative exactly when `A_z>0`, including `s=z` or `t=z`. The small row sums of `X` and small column sums of `Q` equal those of `A`. There are exactly `h_row(z)*k_col(z)-1` ordered choices: coincident labels occur only for `s=t=z` and must be excluded.

For a large crossing, these same full formulas give small views `x=A+e_t`, `q=A+e_s`, and dense completion `T-e_z`. The labels force `t` into the crossing's large row/small column and `s` into its small row/large column, giving `ab` choices. Feasibility is exactly positive ordinary row and column slack at that crossing. Success supplies `T_z>=L>=1`; dense subtraction preserves the upper cap. Positive padded entries alone do not imply ordinary slack.

The full signed difference uniquely recovers distinct ordered labels. Conversely any actual preimage obeys these inverse full formulas. The two crossing classes therefore partition the intended successful inverse fibre, supporting `ell_D=D0+abuv`. Formal arbitrary-target inverse construction, feasibility, exhaustiveness, and cardinality remain to be implemented.

For positive reduced margins, every small row has a positive selected entry because the entire row is small and has no large padding. Distinct rows give distinct support cells, each contributing at least `na-1`; hence `D0>=a(na-1)`. The symmetric argument gives `D0>=b(mb-1)`. Thus `c0=max(a(na-1),b(mb-1))` is positive when `m,n>=2` and `p>0`, and `c0>=max(an,bm)/2 >=(an+bm)/4 >=p/4`. Unique distinct ordered labels give `ell_D<=p(p-1)`.

No local mathematical obstruction was found at `U=11*d*(m+n-2), L=7`: the inverse argument only needs `U>=2`, `L>=1` and the stated positive-margin geometry. The matching actual padded-count theorem already exists as `Research.ReciprocalCount.shape_padding_count_le_twice` in `research/physical-spectral/formal/Research/ReciprocalCount.lean`. Its remaining interface is instantiation with the actual large set and alignment of padding notations, followed by denominator/success composition. The old `PhysicalStationaryLaw.ideal_padded_count` at `5d^3,3d` should not be reused at the new scales.

## Boundaries and remaining interfaces

- Image recovery is not arbitrary-target inverse feasibility or an inverse-fibre cardinality theorem.
- The closed `ell_D` formula applies after the padding test. Before success, large inverse crossings also require `T_z>0`.
- Positive-margin preprocessing is essential to the proposed `c0`. Zero restoration is a separate map. The no-small and one-dimensional branches remain separate, and branch classification does not itself construct a defect start.
- Uniform stationary defect/completion pairs do not become uniform ordinary tables merely by repair. The proposed corrected mass is `c0/|DefectJoint|` per table and requires the exact inverse count and correction law.
- An ideal rational acceptance rule with probability `c0/ell_D` must be distinguished from a bounded dyadic coin and its rounding-error law. Arbitrary rational probabilities are not generally realized exactly by bounded fair words.
- Initialization, branch assembly, outer retries, finite-word law composition, and encoded cost identification remain separate. This packet changes no complete-sampler, exponent, runtime, or default-build claim.

Attempt 01 failed on proof-expression normalization and ambiguous/unqualified names. Attempt 02 fixes those expressions and names. The sole theorem-header change explicitly qualifies `terminalRepairOutput_repad`'s `paddedTable` as `Math115.PhysicalStateNonempty.paddedTable`; it names the intended existing padding function and does not strengthen or weaken the mathematical claim. The source is not byte-identical to attempt 01. The remaining changes are proof normalization, name qualification, and unused-binder cleanup. The reviewed final README claim/hypothesis table matches the source, and its acceptance wording correctly distinguishes ideal rational acceptance from bounded dyadic approximation.

No `sorry`, `admit`, or new `axiom` appears in the reviewed source. The saved audit confirms complete headline closure records and no nonstandard axioms. This is ordinary Lean compilation and the existing environment audit, with a separate AI source review; it is not Linux rebuild or Comparator acceptance.

The final ordinary compilation and full assumption audit are recorded separately in this packet.
