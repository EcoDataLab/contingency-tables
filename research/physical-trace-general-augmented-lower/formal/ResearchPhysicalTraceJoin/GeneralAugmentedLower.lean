/-
SPDX-License-Identifier: Apache-2.0
A spanning family of ordinary inverse labels gives the stronger universal
lower bound p-1. No strict LARGE-donor slack is assumed or counted.+-/
import ResearchPhysicalTraceJoin.GeneralLinearSuccess

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

abbrev RepairLargeRows := {i : Fin m // ¬r i < U}

abbrev RowSpanningParameters (X : Table r c) (hr : ∀ i, 0 < r i)
    (root : RepairSmallRows r U) :=
  {w : RepairSmallRows r U × Fin n // w ≠ (root, rowPositiveColumn r c U X hr root)}

/-- Every small-row cell except one indexes a distinct positive-donor label.
At the chosen donor column, the label links to a fixed small root row. -/
def rowSpanningLabels (X : Table r c) (hr : ∀ i, 0 < r i)
    (root : RepairSmallRows r U) (w : RowSpanningParameters r c U X hr root) :
    InverseSupportLabels r c U X := by
  let i := w.val.1
  let j := w.val.2
  let donor := rowPositiveColumn r c U X hr i
  let source : RepairSmallRows r U := if j = donor then root else i
  let s : Cells small := ⟨(source.val, donor), by
    simp [firstPaperSmall, source.property]⟩
  let t : Cells small := ⟨(i.val,j), by simp [firstPaperSmall, i.property]⟩
  refine ⟨(s,t),?_,?_⟩
  · intro he
    have hi : source = i := Subtype.ext (congrArg (fun z : Cells small => z.val.1) he)
    have hj : donor = j := congrArg (fun z : Cells small => z.val.2) he
    have hs : source = root := by simp [source, hj]
    have hir : i = root := hi.symm.trans hs
    apply w.property
    apply Prod.ext hir
    change j = rowPositiveColumn r c U X hr root
    simpa only [← hir] using hj.symm
  · change if small i.val donor then 0 < X.val i.val donor else _
    have hs : small i.val donor = true := by simp [firstPaperSmall, i.property]
    rw [hs]
    exact rowPositiveColumn_spec r c U X hr i

lemma rowSpanningLabels_injective (X : Table r c) (hr : ∀ i, 0 < r i)
    (root : RepairSmallRows r U) :
    Function.Injective (rowSpanningLabels r c U X hr root) := by
  intro v w he
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg (fun z : InverseSupportLabels r c U X => z.val.2.val.1) he
  · exact congrArg (fun z : InverseSupportLabels r c U X => z.val.2.val.2) he

abbrev ColumnAttachmentParameters := RepairLargeRows r U × RepairSmallColumns c U

/-- Attach the remaining cells, all in small columns and large rows. If a
cell is its column's chosen donor, connect it to the fixed small root row. -/
def columnAttachmentLabels (X : Table r c) (hc : ∀ j, 0 < c j)
    (root : RepairSmallRows r U) (w : ColumnAttachmentParameters r c U) :
    InverseSupportLabels r c U X := by
  let i := w.1
  let j := w.2
  let donor := columnPositiveRow r c U X hc j
  let source : Fin m := if i.val = donor then root.val else i.val
  let s : Cells small := ⟨(source,j.val), by simp [firstPaperSmall, j.property]⟩
  let t : Cells small := ⟨(donor,j.val), by simp [firstPaperSmall, j.property]⟩
  refine ⟨(s,t),?_,?_⟩
  · intro he
    have h : source = donor := congrArg (fun z : Cells small => z.val.1) he
    by_cases hi : i.val = donor
    · have hroot : root.val = i.val := by
        have h' : root.val = donor := by simpa only [source, hi, ite_true] using h
        exact h'.trans hi.symm
      exact i.property (hroot ▸ root.property)
    · exact hi (by simpa [source, hi] using h)
  · change if small donor j.val then 0 < X.val donor j.val else _
    have hs : small donor j.val = true := by simp [firstPaperSmall, j.property]
    rw [hs]
    exact columnPositiveRow_spec r c U X hc j

lemma columnAttachmentLabels_injective (X : Table r c) (hc : ∀ j, 0 < c j)
    (root : RepairSmallRows r U) :
    Function.Injective (columnAttachmentLabels r c U X hc root) := by
  rintro ⟨i,j⟩ ⟨i',j'⟩ he
  have hj : j = j' := Subtype.ext
    (congrArg (fun z : InverseSupportLabels r c U X => z.val.1.val.2) he)
  subst j'
  have hs : (if i.val = columnPositiveRow r c U X hc j then root.val else i.val) =
      (if i'.val = columnPositiveRow r c U X hc j then root.val else i'.val) :=
    congrArg (fun z : InverseSupportLabels r c U X => z.val.1.val.1) he
  have hir : i.val ≠ root.val := fun h => i.property (h ▸ root.property)
  have hir' : i'.val ≠ root.val := fun h => i'.property (h ▸ root.property)
  have hi : i = i' := by
    apply Subtype.ext
    split_ifs at hs with h h' h' <;> simp_all
  exact Prod.ext hi rfl

lemma spanningLabels_disjoint (X : Table r c) (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j) (root : RepairSmallRows r U)
    (v : RowSpanningParameters r c U X hr root)
    (w : ColumnAttachmentParameters r c U) :
    rowSpanningLabels r c U X hr root v ≠ columnAttachmentLabels r c U X hc root w := by
  intro he
  have ht : v.val.1.val = columnPositiveRow r c U X hc w.2 :=
    congrArg (fun z : InverseSupportLabels r c U X => z.val.2.val.1) he
  have hs : (if v.val.2 = rowPositiveColumn r c U X hr v.val.1
      then root.val else v.val.1.val) =
      (if w.1.val = columnPositiveRow r c U X hc w.2 then root.val else w.1.val) := by
    have h := congrArg (fun z : InverseSupportLabels r c U X => z.val.1.val.1) he
    simpa only [rowSpanningLabels, columnAttachmentLabels, apply_ite] using h
  have hd : ¬w.1.val = columnPositiveRow r c U X hc w.2 := by
    intro h
    exact w.1.property ((h.trans ht.symm) ▸ v.val.1.property)
  simp only [hd, ite_false] at hs
  split_ifs at hs with h
  · exact w.1.property (hs ▸ root.property)
  · exact w.1.property (hs ▸ v.val.1.property)

def spanningInverseLabels (X : Table r c) (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j) (root : RepairSmallRows r U) :
    RowSpanningParameters r c U X hr root ⊕ ColumnAttachmentParameters r c U →
      InverseSupportLabels r c U X :=
  Sum.elim (rowSpanningLabels r c U X hr root) (columnAttachmentLabels r c U X hc root)

lemma spanningInverseLabels_injective (X : Table r c) (hr : ∀ i, 0 < r i)
    (hc : ∀ j, 0 < c j) (root : RepairSmallRows r U) :
    Function.Injective (spanningInverseLabels r c U X hr hc root) := by
  intro v w he
  cases v with
  | inl v => cases w with
    | inl w => exact congrArg Sum.inl (rowSpanningLabels_injective r c U X hr root he)
    | inr w => exact False.elim (spanningLabels_disjoint r c U X hr hc root v w he)
  | inr v => cases w with
    | inl w => exact False.elim (spanningLabels_disjoint r c U X hr hc root w v he.symm)
    | inr w => exact congrArg Sum.inr (columnAttachmentLabels_injective r c U X hc root he)

lemma repairLargeRows_card :
    Fintype.card (RepairLargeRows r U) + Fintype.card (RepairSmallRows r U) = m := by
  have h := Fintype.card_subtype_compl (fun i : Fin m => r i < U)
  have hle := Fintype.card_subtype_le (fun i : Fin m => r i < U)
  simp only [Fintype.card_fin] at h hle
  change Fintype.card (RepairLargeRows r U) = m - Fintype.card (RepairSmallRows r U) at h
  change Fintype.card (RepairSmallRows r U) ≤ m at hle
  omega

theorem inverseSupportCount_spanning_lower (X : Table r c)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) :
    Fintype.card (Cells small) - 1 ≤ inverseSupportCount r c U X := by
  let a := Fintype.card (RepairSmallRows r U)
  let b := Fintype.card (RepairSmallColumns c U)
  let p := Fintype.card (Cells small)
  change p - 1 ≤ inverseSupportCount r c U X
  have hinc := smallCell_card_incidence r c U
  change p + a * b = n * a + m * b at hinc
  by_cases ha : a = 0
  · have hl := inverseSupportCount_columns_lower r c U X hc
    change b * (m * b - 1) ≤ _ at hl
    have hp : p = m * b := by
      simpa only [ha, Nat.mul_zero, zero_mul, Nat.add_zero, Nat.zero_add] using hinc
    rw [hp]
    by_cases hb : b = 0
    · simp [hb]
    · have h := Nat.mul_le_mul_right (m * b - 1) (show 1 ≤ b by omega)
      simp only [one_mul] at h
      exact h.trans hl
  · obtain ⟨root⟩ := Fintype.card_pos_iff.mp (show 0 < Fintype.card (RepairSmallRows r U) by omega)
    have hl := Fintype.card_le_of_injective (spanningInverseLabels r c U X hr hc root)
      (spanningInverseLabels_injective r c U X hr hc root)
    have hcard : Fintype.card (RowSpanningParameters r c U X hr root) = n * a - 1 := by
      simp [RowSpanningParameters, Fintype.card_subtype_compl, Fintype.card_prod,
        a, Nat.mul_comm]
    rw [Fintype.card_sum, hcard, Fintype.card_prod] at hl
    have hlarge := repairLargeRows_card r U
    change Fintype.card (RepairLargeRows r U) + a = m at hlarge
    have he : n * a - 1 + Fintype.card (RepairLargeRows r U) * b = p - 1 := by
      have hn : 0 < n := by
        obtain ⟨j,_⟩ := table_positive_row r c X root.val (hr root.val)
        have := j.isLt
        omega
      have hna : 1 ≤ n * a := Nat.mul_pos hn (by omega)
      have hm := congrArg (fun k : ℕ => k * b) hlarge
      rw [Nat.add_mul] at hm
      omega
    rw [he] at hl
    simpa only [InverseSupportLabels, Fintype.card_subtype, Finset.card_eq_sum_ones,
      Finset.sum_filter, inverseSupportCount] using hl

/-- A valid stronger numerator. Existing samplers still use the old allowance. -/
def augmentedInverseSupportAllowance : ℕ :=
  max (inverseSupportAllowance r c U) (Fintype.card (Cells small) - 1)

theorem augmentedInverseSupportAllowance_le_count (X : Table r c)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) :
    augmentedInverseSupportAllowance r c U ≤ inverseSupportCount r c U X :=
  max_le (inverseSupportAllowance_le_count r c U X hr hc)
    (inverseSupportCount_spanning_lower r c U X hr hc)

end
end Math115.PhysicalTraceJoin
