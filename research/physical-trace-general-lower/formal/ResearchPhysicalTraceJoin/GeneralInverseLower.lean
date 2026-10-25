/-
SPDX-License-Identifier: Apache-2.0
A concrete shape-dependent lower bound on the exact ordinary inverse-label
count, constructed from positive entries in every small row and column.
-/
import ResearchPhysicalTraceJoin.GeneralInverseSupport

set_option maxHeartbeats 1200000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open SmallContextFibres PaddedCompletions
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalStationarySuccess
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U : ℕ)

local notation "small" => firstPaperSmall r c U

abbrev RepairSmallRows := {i : Fin m // r i < U}
abbrev RepairSmallColumns := {j : Fin n // c j < U}

lemma table_positive_row (X : Table r c) (i : Fin m) (hr : 0 < r i) :
    ∃ j, 0 < X.val i j := by
  by_contra hn
  have hz (j : Fin n) : X.val i j = 0 := by
    have hnot : ¬0 < X.val i j := fun h => hn ⟨j,h⟩
    omega
  have hm := X.property.1 i
  simp only [hz, Finset.sum_const_zero] at hm
  omega

lemma table_positive_column (X : Table r c) (j : Fin n) (hc : 0 < c j) :
    ∃ i, 0 < X.val i j := by
  by_contra hn
  have hz (i : Fin m) : X.val i j = 0 := by
    have hnot : ¬0 < X.val i j := fun h => hn ⟨i,h⟩
    omega
  have hm := X.property.2 j
  simp only [hz, Finset.sum_const_zero] at hm
  omega

def rowPositiveColumn (X : Table r c) (hr : ∀ i, 0 < r i) (i : RepairSmallRows r U) : Fin n :=
  Classical.choose (table_positive_row r c X i.val (hr i.val))

lemma rowPositiveColumn_spec (X : Table r c) (hr : ∀ i, 0 < r i) (i : RepairSmallRows r U) :
    0 < X.val i.val (rowPositiveColumn r c U X hr i) :=
  Classical.choose_spec (table_positive_row r c X i.val (hr i.val))

def columnPositiveRow (X : Table r c) (hc : ∀ j, 0 < c j) (j : RepairSmallColumns c U) : Fin m :=
  Classical.choose (table_positive_column r c X j.val (hc j.val))

lemma columnPositiveRow_spec (X : Table r c) (hc : ∀ j, 0 < c j) (j : RepairSmallColumns c U) :
    0 < X.val (columnPositiveRow r c U X hc j) j.val :=
  Classical.choose_spec (table_positive_column r c X j.val (hc j.val))

abbrev RowInverseParameters (X : Table r c) (hr : ∀ i, 0 < r i) :=
  (i : RepairSmallRows r U) ×
    {w : RepairSmallRows r U × Fin n // w ≠ (i, rowPositiveColumn r c U X hr i)}

abbrev ColumnInverseParameters (X : Table r c) (hc : ∀ j, 0 < c j) :=
  (j : RepairSmallColumns c U) ×
    {w : Fin m × RepairSmallColumns c U // w ≠ (columnPositiveRow r c U X hc j, j)}

def rowInverseLabels (X : Table r c) (hr : ∀ i, 0 < r i)
    (a : RowInverseParameters r c U X hr) : InverseSupportLabels r c U X := by
  let s : Cells small := ⟨(a.2.val.1.val, rowPositiveColumn r c U X hr a.1), by
    simp [firstPaperSmall, a.2.val.1.property]⟩
  let t : Cells small := ⟨(a.1.val, a.2.val.2), by
    simp [firstPaperSmall, a.1.property]⟩
  refine ⟨(s,t),?_,?_⟩
  · intro he
    have hi : a.2.val.1 = a.1 := Subtype.ext (congrArg (fun z : Cells small => z.val.1) he)
    have hj : rowPositiveColumn r c U X hr a.1 = a.2.val.2 :=
      congrArg (fun z : Cells small => z.val.2) he
    exact a.2.property (Prod.ext hi hj.symm)
  · change if small a.1.val (rowPositiveColumn r c U X hr a.1) then
      0 < X.val a.1.val (rowPositiveColumn r c U X hr a.1) else _
    have hs : small a.1.val (rowPositiveColumn r c U X hr a.1) = true := by
      simp [firstPaperSmall, a.1.property]
    rw [hs]
    exact rowPositiveColumn_spec r c U X hr a.1

def columnInverseLabels (X : Table r c) (hc : ∀ j, 0 < c j)
    (a : ColumnInverseParameters r c U X hc) : InverseSupportLabels r c U X := by
  let s : Cells small := ⟨(a.2.val.1, a.1.val), by
    simp [firstPaperSmall, a.1.property]⟩
  let t : Cells small := ⟨(columnPositiveRow r c U X hc a.1, a.2.val.2.val), by
    simp [firstPaperSmall, a.2.val.2.property]⟩
  refine ⟨(s,t),?_,?_⟩
  · intro he
    have hi : a.2.val.1 = columnPositiveRow r c U X hc a.1 :=
      congrArg (fun z : Cells small => z.val.1) he
    have hj : a.2.val.2 = a.1 :=
      Subtype.ext (congrArg (fun z : Cells small => z.val.2) he).symm
    exact a.2.property (Prod.ext hi hj)
  · change if small (columnPositiveRow r c U X hc a.1) a.1.val then
      0 < X.val (columnPositiveRow r c U X hc a.1) a.1.val else _
    have hs : small (columnPositiveRow r c U X hc a.1) a.1.val = true := by
      simp [firstPaperSmall, a.1.property]
    rw [hs]
    exact columnPositiveRow_spec r c U X hc a.1

lemma rowInverseLabels_injective (X : Table r c) (hr : ∀ i, 0 < r i) :
    Function.Injective (rowInverseLabels r c U X hr) := by
  rintro ⟨i,w⟩ ⟨i',w'⟩ he
  have hi : i.val = i'.val := congrArg
    (fun z : InverseSupportLabels r c U X => z.val.2.val.1) he
  have hh : w.val.1.val = w'.val.1.val := congrArg
    (fun z : InverseSupportLabels r c U X => z.val.1.val.1) he
  have hk : w.val.2 = w'.val.2 := congrArg
    (fun z : InverseSupportLabels r c U X => z.val.2.val.2) he
  have hii : i = i' := Subtype.ext hi
  subst i'
  congr 1
  exact Subtype.ext (Prod.ext (Subtype.ext hh) hk)

lemma columnInverseLabels_injective (X : Table r c) (hc : ∀ j, 0 < c j) :
    Function.Injective (columnInverseLabels r c U X hc) := by
  rintro ⟨j,w⟩ ⟨j',w'⟩ he
  have hj : j.val = j'.val := congrArg
    (fun z : InverseSupportLabels r c U X => z.val.1.val.2) he
  have hh : w.val.1 = w'.val.1 := congrArg
    (fun z : InverseSupportLabels r c U X => z.val.1.val.1) he
  have hk : w.val.2.val = w'.val.2.val := congrArg
    (fun z : InverseSupportLabels r c U X => z.val.2.val.2) he
  have hjj : j = j' := Subtype.ext hj
  subst j'
  congr 1
  exact Subtype.ext (Prod.ext hh (Subtype.ext hk))

lemma rowInverseParameters_card (X : Table r c) (hr : ∀ i, 0 < r i) :
    Fintype.card (RowInverseParameters r c U X hr) =
      Fintype.card (RepairSmallRows r U) * (n * Fintype.card (RepairSmallRows r U) - 1) := by
  change Fintype.card ((i : RepairSmallRows r U) ×
    {w : RepairSmallRows r U × Fin n // w ≠ (i,rowPositiveColumn r c U X hr i)}) = _
  rw [Fintype.card_sigma]
  have hc (i : RepairSmallRows r U) :
      Fintype.card {w : RepairSmallRows r U × Fin n // w ≠ (i,rowPositiveColumn r c U X hr i)} =
        n * Fintype.card (RepairSmallRows r U) - 1 := by
    simp [Fintype.card_subtype_compl, Fintype.card_prod, Nat.mul_comm]
  simp only [hc, Finset.sum_const, Finset.card_univ, smul_eq_mul]

lemma columnInverseParameters_card (X : Table r c) (hc : ∀ j, 0 < c j) :
    Fintype.card (ColumnInverseParameters r c U X hc) =
      Fintype.card (RepairSmallColumns c U) * (m * Fintype.card (RepairSmallColumns c U) - 1) := by
  change Fintype.card ((j : RepairSmallColumns c U) ×
    {w : Fin m × RepairSmallColumns c U // w ≠ (columnPositiveRow r c U X hc j,j)}) = _
  rw [Fintype.card_sigma]
  have hh (j : RepairSmallColumns c U) :
      Fintype.card {w : Fin m × RepairSmallColumns c U // w ≠ (columnPositiveRow r c U X hc j,j)} =
        m * Fintype.card (RepairSmallColumns c U) - 1 := by
    simp [Fintype.card_subtype_compl, Fintype.card_prod]
  simp only [hh, Finset.sum_const, Finset.card_univ, smul_eq_mul]

lemma inverseSupportCount_rows_lower (X : Table r c) (hr : ∀ i, 0 < r i) :
    Fintype.card (RepairSmallRows r U) * (n * Fintype.card (RepairSmallRows r U) - 1) ≤
      inverseSupportCount r c U X := by
  have h := Fintype.card_le_of_injective (rowInverseLabels r c U X hr)
    (rowInverseLabels_injective r c U X hr)
  rw [rowInverseParameters_card] at h
  simpa only [InverseSupportLabels, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter, inverseSupportCount] using h

lemma inverseSupportCount_columns_lower (X : Table r c) (hc : ∀ j, 0 < c j) :
    Fintype.card (RepairSmallColumns c U) * (m * Fintype.card (RepairSmallColumns c U) - 1) ≤
      inverseSupportCount r c U X := by
  have h := Fintype.card_le_of_injective (columnInverseLabels r c U X hc)
    (columnInverseLabels_injective r c U X hc)
  rw [columnInverseParameters_card] at h
  simpa only [InverseSupportLabels, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter, inverseSupportCount] using h

/-- The documented c0, from literal small-row and small-column counts. -/
def inverseSupportAllowance : ℕ :=
  max (Fintype.card (RepairSmallRows r U) * (n * Fintype.card (RepairSmallRows r U) - 1))
    (Fintype.card (RepairSmallColumns c U) * (m * Fintype.card (RepairSmallColumns c U) - 1))

theorem inverseSupportAllowance_le_count (X : Table r c)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) :
    inverseSupportAllowance r c U ≤ inverseSupportCount r c U X :=
  max_le (inverseSupportCount_rows_lower r c U X hr) (inverseSupportCount_columns_lower r c U X hc)

theorem inverseSupportAllowance_positive (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hp : 0 < Fintype.card (Cells small)) : 0 < inverseSupportAllowance r c U := by
  obtain ⟨z⟩ := Fintype.card_pos_iff.mp hp
  have hsmall : r z.val.1 < U ∨ c z.val.2 < U := by
    simpa only [firstPaperSmall, decide_eq_true_eq] using z.property
  rcases hsmall with hr | hc
  · have ha : 0 < Fintype.card (RepairSmallRows r U) :=
      Fintype.card_pos_iff.mpr ⟨⟨z.val.1,hr⟩⟩
    have hna : 2 ≤ n * Fintype.card (RepairSmallRows r U) := by nlinarith
    have hpos : 0 < Fintype.card (RepairSmallRows r U) *
        (n * Fintype.card (RepairSmallRows r U) - 1) := Nat.mul_pos ha (by omega)
    exact hpos.trans_le (le_max_left _ _)
  · have hb : 0 < Fintype.card (RepairSmallColumns c U) :=
      Fintype.card_pos_iff.mpr ⟨⟨z.val.2,hc⟩⟩
    have hmb : 2 ≤ m * Fintype.card (RepairSmallColumns c U) := by nlinarith
    have hpos : 0 < Fintype.card (RepairSmallColumns c U) *
        (m * Fintype.card (RepairSmallColumns c U) - 1) := Nat.mul_pos hb (by omega)
    exact hpos.trans_le (le_max_right _ _)

end
end Math115.PhysicalTraceJoin
