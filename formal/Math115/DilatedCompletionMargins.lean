/-
SPDX-License-Identifier: Apache-2.0
Actual physical residual margins and the adjacent-lattice fine-input margins.
This file does not prove the rounding codec, a volume/count comparison, or an
oracle accuracy or machine-cost theorem.
-/
import Math115.PhysicalCompletionOracle
import OAI.Combinatorics.ContingencyTables.Transport.ReferenceCompletionBounds

namespace Math115.DilatedCompletionMargins

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open ReducedSmallChain PhysicalCompletionOracle
open SmallGraphProfiles CompletionCounts PaddedCompletions
open PhysicalCompletionFibres FirstPaperPhysicalMarginal
open scoped BigOperators Classical

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

private lemma subtype_card_indicator {A : Type*} [Fintype A] (p : A → Prop)
    [DecidablePred p] : (∑ x : A, if p x then 1 else 0) = Fintype.card {x // p x} := by
  simp only [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

omit [Fintype I] [LinearOrder I] [LinearOrder J] in
lemma rowLargeCount_rectangle (r : I → ℕ) (c : J → ℕ) (U : ℕ) (i : I) :
    rowLargeCount (firstPaperSmall r c U) i =
      if U ≤ r i then Fintype.card (LargeColumns c U) else 0 := by
  by_cases hi : U ≤ r i
  · rw [ite_eq_left hi]
    calc
      _ = ∑ j : J, if U ≤ c j then 1 else 0 := by
        unfold rowLargeCount
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : U ≤ c j
        · simp [firstPaperSmall, Nat.not_lt.mpr hi, Nat.not_lt.mpr hj, hj]
        · have hj' : c j < U := Nat.lt_of_not_ge hj
          simp [firstPaperSmall, hj', hj]
      _ = _ := subtype_card_indicator (fun j : J => U ≤ c j)
  · rw [ite_eq_right hi]
    have hi' : r i < U := Nat.lt_of_not_ge hi
    simp [rowLargeCount, firstPaperSmall, hi']

omit [Fintype J] [LinearOrder I] [LinearOrder J] in
lemma columnLargeCount_rectangle (r : I → ℕ) (c : J → ℕ) (U : ℕ) (j : J) :
    columnLargeCount (firstPaperSmall r c U) j =
      if U ≤ c j then Fintype.card (LargeRows r U) else 0 := by
  by_cases hj : U ≤ c j
  · rw [ite_eq_left hj]
    calc
      _ = ∑ i : I, if U ≤ r i then 1 else 0 := by
        unfold columnLargeCount
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : U ≤ r i
        · simp [firstPaperSmall, Nat.not_lt.mpr hi, Nat.not_lt.mpr hj, hi]
        · have hi' : r i < U := Nat.lt_of_not_ge hi
          simp [firstPaperSmall, hi', hi]
      _ = _ := subtype_card_indicator (fun i : I => U ≤ r i)
  · rw [ite_eq_right hj]
    have hj' : c j < U := Nat.lt_of_not_ge hj
    simp [columnLargeCount, firstPaperSmall, hj']

omit [LinearOrder I] [LinearOrder J] in
lemma total_large_cell_count (r : I → ℕ) (c : J → ℕ) (U : ℕ) :
    (∑ i, rowLargeCount (firstPaperSmall r c U) i) =
      Fintype.card (LargeRows r U) * Fintype.card (LargeColumns c U) := by
  calc
    _ = ∑ i : I, (if U ≤ r i then 1 else 0) * Fintype.card (LargeColumns c U) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [rowLargeCount_rectangle]
      split_ifs <;> simp
    _ = (∑ i : I, if U ≤ r i then 1 else 0) * Fintype.card (LargeColumns c U) :=
      (Finset.sum_mul _ _ _).symm
    _ = _ := by rw [subtype_card_indicator]

/-- Every large row retains one padding contribution for every large column.
The physical residual's truncated subtraction is nonnegative even before using
positive completion mass. This strengthens the source's single-L lower bound. -/
lemma physical_residual_row_lower (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (z : States r c U L) (i : LargeRows r U) :
    Fintype.card (LargeColumns c U) * L ≤
      residualRows (firstPaperSmall r c U) (capacity r c U L) r c L z i.val := by
  unfold residualRows
  rw [rowLargeCount_rectangle, ite_eq_left i.property]
  omega

lemma physical_residual_column_lower (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (z : States r c U L) (j : LargeColumns c U) :
    Fintype.card (LargeRows r U) * L ≤
      residualColumns (firstPaperSmall r c U) (capacity r c U L) r c L z j.val := by
  unfold residualColumns
  rw [columnLargeCount_rectangle, ite_eq_left j.property]
  omega

/-- The actual referenceTable row index includes its reference row as none;
all rows therefore satisfy the same full-block lower bound. -/
lemma reference_row_lower (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (z : States r c U L)
    (i : Option {i : LargeRows r U // i ≠ i₀}) :
    Fintype.card (LargeColumns c U) * L ≤
      referenceRows r c U L (capacity r c U L) i₀ z i :=
  physical_residual_row_lower r c U L z ((Equiv.optionSubtypeNe i₀) i)

lemma reference_column_lower (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (j₀ : LargeColumns c U) (z : States r c U L)
    (j : Option {j : LargeColumns c U // j ≠ j₀}) :
    Fintype.card (LargeRows r U) * L ≤
      referenceColumns r c U L (capacity r c U L) j₀ z j :=
  physical_residual_column_lower r c U L z ((Equiv.optionSubtypeNe j₀) j)

lemma reference_row_total_eq_residual (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (z : States r c U L) :
    (∑ i, referenceRows r c U L (capacity r c U L) i₀ z i) =
      ∑ i, residualRows (firstPaperSmall r c U) (capacity r c U L) r c L z i := by
  unfold referenceRows
  rw [(Equiv.optionSubtypeNe i₀).sum_comp
    (fun i : LargeRows r U => residualRows (firstPaperSmall r c U)
      (capacity r c U L) r c L z i.val)]
  convert sum_subtype_eq_of_zero (fun i => U ≤ r i)
    (residualRows (firstPaperSmall r c U) (capacity r c U L) r c L z)
    (physical_residual_row_zero r c U L (capacity r c U L) z
      (physical_paper_capacity _ r c _ L U dimension_le_allowance z)) using 1
  congr 2
  exact Subsingleton.elim _ _

/-- Actual paperCapacity and positive physical mass force zero residuals
outside the large block, so the sharper abL total also bounds ReferenceTable. -/
theorem reference_total_upper (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (z : States r c U L) :
    (∑ i, referenceRows r c U L (capacity r c U L) i₀ z i) ≤
      (∑ i, r i) + Fintype.card (LargeRows r U) * Fintype.card (LargeColumns c U) * L := by
  rw [reference_row_total_eq_residual]
  have h := padded_total_le (firstPaperSmall r c U)
    (FirstPaperProfiles.smallView (firstPaperSmall r c U)
      (physicalProfile _ (capacity r c U L) r c L z) false) r L
  rw [total_large_cell_count] at h
  exact h

/-- Fine row margins on exactly the row index of PhysicalCompletionOracle.ReferenceTable. -/
def fineRows (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (i₀ : LargeRows r U)
    (z : States r c U L) (i : Option {i : LargeRows r U // i ≠ i₀}) : ℕ :=
  (dimensionAllowance (I := I) (J := J))^12 *
    (referenceRows r c U L (capacity r c U L) i₀ z i + 2 * Fintype.card (LargeColumns c U))

def fineColumns (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (j₀ : LargeColumns c U)
    (z : States r c U L) (j : Option {j : LargeColumns c U // j ≠ j₀}) : ℕ :=
  (dimensionAllowance (I := I) (J := J))^12 *
    (referenceColumns r c U L (capacity r c U L) j₀ z j + 2 * Fintype.card (LargeRows r U))

abbrev FineReferenceTable (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L) :=
  Table (fineRows r c U L i₀ z) (fineColumns r c U L j₀ z)

lemma fine_row_total (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (z : States r c U L) :
    (∑ i, fineRows r c U L i₀ z i) =
      (dimensionAllowance (I := I) (J := J))^12 *
        ((∑ i, referenceRows r c U L (capacity r c U L) i₀ z i) +
          2 * Fintype.card (LargeRows r U) * Fintype.card (LargeColumns c U)) := by
  simp only [fineRows, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul]
  rw [Fintype.card_congr (Equiv.optionSubtypeNe i₀)]
  ring

lemma fine_column_total (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (j₀ : LargeColumns c U) (z : States r c U L) :
    (∑ j, fineColumns r c U L j₀ z j) =
      (dimensionAllowance (I := I) (J := J))^12 *
        ((∑ j, referenceColumns r c U L (capacity r c U L) j₀ z j) +
          2 * Fintype.card (LargeRows r U) * Fintype.card (LargeColumns c U)) := by
  simp only [fineColumns, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    smul_eq_mul]
  rw [Fintype.card_congr (Equiv.optionSubtypeNe j₀)]
  ring

/-- Equal totals are derived from the actual feasible physical state and its
paperCapacity; they are not an extra hypothesis on an abstract margin pair. -/
theorem fine_totals (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L) :
    (∑ i, fineRows r c U L i₀ z i) = ∑ j, fineColumns r c U L j₀ z j := by
  rw [fine_row_total, fine_column_total,
    reference_totals r c U L (capacity r c U L) i₀ j₀ z
      (physical_paper_capacity _ r c _ L U dimension_le_allowance z)]

instance fineReferenceTableNonempty (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L) :
    Nonempty (FineReferenceTable r c U L i₀ j₀ z) :=
  table_nonempty _ _ (fine_totals r c U L i₀ j₀ z)

theorem fine_total_upper (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (z : States r c U L) :
    (∑ i, fineRows r c U L i₀ z i) ≤
      (dimensionAllowance (I := I) (J := J))^12 *
        ((∑ i, r i) + Fintype.card (LargeRows r U) * Fintype.card (LargeColumns c U) * L +
          2 * Fintype.card (LargeRows r U) * Fintype.card (LargeColumns c U)) := by
  rw [fine_row_total]
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_right (reference_total_upper r c U L i₀ z) _)

/-- Nonempty large blocks make the fine margins meet the pinned dense oracle's
d^12 lower threshold. This remains true for every U,L, independently of any
reviewed geometric acceptance estimate. -/
theorem fine_row_dense_minimum (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L)
    (i : Option {i : LargeRows r U // i ≠ i₀}) :
    (dimensionAllowance (I := I) (J := J))^12 ≤ fineRows r c U L i₀ z i := by
  have hb : 0 < Fintype.card (LargeColumns c U) := Fintype.card_pos_iff.mpr ⟨j₀⟩
  have h : 1 ≤ referenceRows r c U L (capacity r c U L) i₀ z i +
      2 * Fintype.card (LargeColumns c U) := by omega
  simpa only [fineRows, Nat.mul_one] using
    Nat.mul_le_mul_left ((dimensionAllowance (I := I) (J := J))^12) h

theorem fine_column_dense_minimum (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L)
    (j : Option {j : LargeColumns c U // j ≠ j₀}) :
    (dimensionAllowance (I := I) (J := J))^12 ≤ fineColumns r c U L j₀ z j := by
  have ha : 0 < Fintype.card (LargeRows r U) := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have h : 1 ≤ referenceColumns r c U L (capacity r c U L) j₀ z j +
      2 * Fintype.card (LargeRows r U) := by omega
  simpa only [fineColumns, Nat.mul_one] using
    Nat.mul_le_mul_left ((dimensionAllowance (I := I) (J := J))^12) h

theorem ideal_reference_row_geometric_minimum (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (i₀ : LargeRows r U)
    (z : States r c U (3 * dimensionAllowance (I := I) (J := J)))
    (i : Option {i : LargeRows r U // i ≠ i₀}) :
    3 * Fintype.card (LargeColumns c U) * dimensionAllowance (I := I) (J := J) ≤
      referenceRows r c U (3 * dimensionAllowance (I := I) (J := J))
        (capacity r c U (3 * dimensionAllowance (I := I) (J := J))) i₀ z i := by
  simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    reference_row_lower r c U (3 * dimensionAllowance (I := I) (J := J)) i₀ z i

theorem ideal_reference_column_geometric_minimum (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (j₀ : LargeColumns c U)
    (z : States r c U (3 * dimensionAllowance (I := I) (J := J)))
    (j : Option {j : LargeColumns c U // j ≠ j₀}) :
    3 * Fintype.card (LargeRows r U) * dimensionAllowance (I := I) (J := J) ≤
      referenceColumns r c U (3 * dimensionAllowance (I := I) (J := J))
        (capacity r c U (3 * dimensionAllowance (I := I) (J := J))) j₀ z j := by
  simpa only [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
    reference_column_lower r c U (3 * dimensionAllowance (I := I) (J := J)) j₀ z j

end
end Math115.DilatedCompletionMargins
