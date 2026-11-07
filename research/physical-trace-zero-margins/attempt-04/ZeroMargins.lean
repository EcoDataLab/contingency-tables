/-
SPDX-License-Identifier: Apache-2.0
Restriction to positive-margin rows/columns and explicit zero restoration
are inverse on ordinary tables. Uniform laws and total variation transport
through that equivalence. This is not a list preprocessing implementation,
cutoff/physical-state transport, defect initialization, or a cost theorem.
-/
import OAI.Combinatorics.ContingencyTables.Transport.RectangleCompletions
import OAI.Combinatorics.ContingencyTables.Machines.FiniteFairBits

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables
open CompletionCounts PaddedCompletions FirstSuccess ResidualMixture FairBits
open scoped BigOperators Classical

noncomputable section
variable {I J : Type*} [Fintype I] [Fintype J]
variable (r : I → ℕ) (c : J → ℕ)

abbrev PositiveRows := {i : I // 0 < r i}
abbrev PositiveColumns := {j : J // 0 < c j}
/-- Elaborate subtype finite instances with generic predicates, exactly as
in the pinned rectangle equivalence. No table is selected by this alias. -/
abbrev RestrictedTable (p : I → Prop) (q : J → Prop) :=
  Table (fun i : {i // p i} => r i.val) (fun j : {j // q j} => c j.val)

abbrev PositiveTable := RestrictedTable r c (fun i => 0 < r i) (fun j => 0 < c j)

def zeroMarginMask (i : I) (j : J) : Bool := decide (r i = 0 ∨ c j = 0)

lemma zeroMarginMask_rectangle (i : I) (j : J) :
    zeroMarginMask r c i j = false ↔ 0 < r i ∧ 0 < c j := by
  simp [zeroMarginMask, Nat.pos_iff_ne_zero]

lemma table_entry_zero_of_row_zero (X : Table r c) (i : I) (j : J) (hi : r i = 0) :
    X.val i j = 0 := by
  have h := entry_le_row X.property i j
  omega

lemma table_entry_zero_of_column_zero (X : Table r c) (i : I) (j : J) (hj : c j = 0) :
    X.val i j = 0 := by
  have h : X.val i j ≤ c j := by
    rw [← X.property.2 j]
    exact Finset.single_le_sum (f := fun k => X.val k j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- Adding the supported-on-positive-rectangle proof changes no table. -/
def zeroMarginSupportedEquiv : Table r c ≃ LargeCompletion (zeroMarginMask r c) r c where
  toFun X := ⟨X, by
    intro i j hs
    have h : r i = 0 ∨ c j = 0 := by
      simpa only [zeroMarginMask, decide_eq_true_eq] using hs
    rcases h with hi | hj
    · exact table_entry_zero_of_row_zero r c X i j hi
    · exact table_entry_zero_of_column_zero r c X i j hj⟩
  invFun X := X.val
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

/-- The existing rectangle equivalence gives literal restriction and
zero extension, including empty positive-index types and zero totals. -/
def zeroMarginEquiv : Table r c ≃ PositiveTable r c :=
  (zeroMarginSupportedEquiv r c).trans
    (rectangleCompletionEquiv (zeroMarginMask r c) (fun i => 0 < r i) (fun j => 0 < c j)
      (zeroMarginMask_rectangle r c) r c
      (by intro i hi; omega) (by intro j hj; omega))

theorem zeroMarginEquiv_restrict_entry (X : Table r c)
    (i : PositiveRows r) (j : PositiveColumns c) :
    (zeroMarginEquiv r c X).val i j = X.val i.val j.val := rfl

theorem zeroMarginEquiv_extend_entry (X : PositiveTable r c) (i : I) (j : J) :
    ((zeroMarginEquiv r c).symm X).val i j =
      if hi : 0 < r i then if hj : 0 < c j then X.val ⟨i, hi⟩ ⟨j, hj⟩ else 0 else 0 := by
  by_cases hi : 0 < r i <;> by_cases hj : 0 < c j <;>
    simp [zeroMarginEquiv, zeroMarginSupportedEquiv, rectangleCompletionEquiv, Equiv.symm,
      rectangleExtend, hi, hj]

theorem zeroMarginEquiv_restore_restrict (X : Table r c) :
    (zeroMarginEquiv r c).symm (zeroMarginEquiv r c X) = X :=
  (zeroMarginEquiv r c).symm_apply_apply X

theorem zeroMarginEquiv_restrict_restore (X : PositiveTable r c) :
    zeroMarginEquiv r c ((zeroMarginEquiv r c).symm X) = X :=
  (zeroMarginEquiv r c).apply_symm_apply X

def restoreZeroMarginsLaw (q : RationalLaw (PositiveTable r c)) : RationalLaw (Table r c) :=
  equivLaw (zeroMarginEquiv r c).symm q

/-- No table enumeration or conditioning is needed: TV is unchanged by
the explicit restoration bijection. Feasibility is not a new premise. -/
theorem restoreZeroMarginsLaw_variation (q q' : RationalLaw (PositiveTable r c)) :
    variation (restoreZeroMarginsLaw r c q) (restoreZeroMarginsLaw r c q') =
      variation q q' :=
  variation_equiv (zeroMarginEquiv r c).symm q q'

/-- Equal original totals supply both nonempty table spaces, even when
all margins vanish or either original index type is empty. -/
theorem restoreZeroMarginsLaw_uniform (htotal : (∑ i, r i) = ∑ j, c j) :
    letI := table_nonempty r c htotal
    letI : Nonempty (PositiveTable r c) :=
      Nonempty.map (zeroMarginEquiv r c) (table_nonempty r c htotal)
    restoreZeroMarginsLaw r c (uniformLaw (α := PositiveTable r c)) =
      uniformLaw (α := Table r c) := by
  letI := table_nonempty r c htotal
  letI : Nonempty (PositiveTable r c) :=
    Nonempty.map (zeroMarginEquiv r c) (table_nonempty r c htotal)
  exact uniform_equiv (zeroMarginEquiv r c).symm

/-- Any reduced-table approximation keeps exactly its TV error after
zero rows/columns are restored. This is only an ordinary-table law. -/
theorem restoreZeroMarginsLaw_uniform_variation (htotal : (∑ i, r i) = ∑ j, c j)
    (q : RationalLaw (PositiveTable r c)) :
    letI := table_nonempty r c htotal
    letI : Nonempty (PositiveTable r c) :=
      Nonempty.map (zeroMarginEquiv r c) (table_nonempty r c htotal)
    variation (restoreZeroMarginsLaw r c q) (uniformLaw (α := Table r c)) =
      variation q (uniformLaw (α := PositiveTable r c)) := by
  letI := table_nonempty r c htotal
  letI : Nonempty (PositiveTable r c) :=
    Nonempty.map (zeroMarginEquiv r c) (table_nonempty r c htotal)
  rw [← restoreZeroMarginsLaw_uniform r c htotal]
  exact restoreZeroMarginsLaw_variation r c q _

end
end Math115.PhysicalTraceJoin
