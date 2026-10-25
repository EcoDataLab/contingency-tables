/-
SPDX-License-Identifier: Apache-2.0
Actual repair-fibre and total-joint upper bounds at the sharper scales.
No inverse existence, acceptance lower bound, or output law is assumed.
-/
import ResearchPhysicalTraceJoin.GeneralRepair
import Research.ReciprocalCount

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open SmallGraphProfiles FirstPaperProfiles CompletionCounts PaddedCompletions
open SmallContextCoordinates
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalStationarySuccess
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)

local notation "small" => firstPaperSmall r c U
local notation "p" => Fintype.card (Cells small)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "rbar" => (fun i => r i + rowLargeCount small i * L)
local notation "cbar" => (fun j => c j + columnLargeCount small j * L)

abbrev DistinctRepairLabels :=
  {st : Cells small × Cells small // st.1 ≠ st.2}

def terminalDistinctLabels (a : DefectJoint r c U L) : DistinctRepairLabels r c U :=
  ⟨terminalRepairLabels r c U L a.1, by
    intro h
    exact (terminalRepairLabels_spec r c U L a.1).1 (congrArg Subtype.val h)⟩

theorem distinctRepairLabels_card :
    Fintype.card (DistinctRepairLabels r c U) = p * (p - 1) := by
  change Fintype.card {st : Cells small × Cells small // st.1 ≠ st.2} = _
  rw [Fintype.card_subtype]
  have he : (Finset.univ.filter (fun st : Cells small × Cells small => st.1 ≠ st.2)) =
      (Finset.univ : Finset (Cells small)).offDiag := by
    ext st
    simp
  rw [he, Finset.offDiag_card, Finset.card_univ]
  rw [Nat.mul_sub_left_distrib, Nat.mul_one]

/-- Completion multiplicities are retained in this literal encoding. -/
def terminalRepairEncoding (a : DefectJoint r c U L) :
    DistinctRepairLabels r c U × Table rbar cbar :=
  (terminalDistinctLabels r c U L a, (terminalRepairedTable r c U L a).val)

theorem terminalRepairEncoding_injective :
    Function.Injective (terminalRepairEncoding r c U L) := by
  intro a b h
  apply terminalRepair_labels_table_injective r c U L
  exact Prod.ext (congrArg Subtype.val (congrArg Prod.fst h))
    (Subtype.ext (congrArg Prod.snd h))

/-- All actual defect/completion pairs, including padding failures. -/
theorem defectJoint_card_le_padded :
    Fintype.card (DefectJoint r c U L) ≤
      p * (p - 1) * Fintype.card (Table rbar cbar) := by
  have h := Fintype.card_le_of_injective (terminalRepairEncoding r c U L)
    (terminalRepairEncoding_injective r c U L)
  simpa only [Fintype.card_prod, distinctRepairLabels_card] using h

abbrev TerminalOutputFibre (X : Table r c) :=
  {a : SuccessfulTerminalRepair r c U L // terminalRepairOutput r c U L a = X}

def terminalOutputFibreLabels (X : Table r c) (a : TerminalOutputFibre r c U L X) :
    DistinctRepairLabels r c U := terminalDistinctLabels r c U L a.val.val

theorem terminalOutputFibreLabels_injective (X : Table r c) :
    Function.Injective (terminalOutputFibreLabels r c U L X) := by
  intro a b h
  apply Subtype.ext
  apply Subtype.ext
  apply terminalRepair_labels_table_injective r c U L
  apply Prod.ext
  · exact congrArg Subtype.val h
  · apply Subtype.ext
    rw [← terminalRepairOutput_repad r c U L a.val,
      ← terminalRepairOutput_repad r c U L b.val, a.property, b.property]

/-- An actual successful fibre has at most one inverse per distinct ordered label pair. -/
theorem terminalOutputFibre_card_le (X : Table r c) :
    Fintype.card (TerminalOutputFibre r c U L X) ≤ p * (p - 1) := by
  have h := Fintype.card_le_of_injective (terminalOutputFibreLabels r c U L X)
    (terminalOutputFibreLabels_injective r c U L X)
  simpa only [distinctRepairLabels_card] using h

/-- Instantiate the existing reciprocal-growth count theorem with the actual mask. -/
theorem actualShape_padded_count_le_twice :
    let U := 11 * d * (m + n - 2)
    Fintype.card (Table
      (fun i => r i + rowLargeCount (firstPaperSmall r c U) i * 7)
      (fun j => c j + columnLargeCount (firstPaperSmall r c U) j * 7)) ≤
        2 * Fintype.card (Table r c) := by
  dsimp only
  let K : Finset (Fin m × Fin n) :=
    Finset.univ.filter (fun z => firstPaperSmall r c (11 * d * (m + n - 2)) z.1 z.2 = false)
  have hrow : ∀ z ∈ K, 11 * d * (Fintype.card (Fin m) + Fintype.card (Fin n) - 2) ≤ r z.1 := by
    intro z hz
    have hs := (Finset.mem_filter.mp hz).2
    simp only [firstPaperSmall, decide_eq_false_iff_not, not_or, not_lt] at hs
    simpa only [Fintype.card_fin] using hs.1
  have hcol : ∀ z ∈ K, 11 * d * (Fintype.card (Fin m) + Fintype.card (Fin n) - 2) ≤ c z.2 := by
    intro z hz
    have hs := (Finset.mem_filter.mp hz).2
    simp only [firstPaperSmall, decide_eq_false_iff_not, not_or, not_lt] at hs
    simpa only [Fintype.card_fin] using hs.2
  have h := Research.ReciprocalCount.shape_padding_count_le_twice r c K d
    dimension_le_allowance hrow hcol
  simpa only [K, PhysicalStationarySuccess.large_padding_rows, PhysicalStationarySuccess.large_padding_columns] using h

/-- New-scale denominator bound for the actual labelled joint, with no count premise. -/
theorem actualShape_defectJoint_card_le :
    let U := 11 * d * (m + n - 2)
    let cellCount := Fintype.card (Cells (firstPaperSmall r c U))
    Fintype.card (DefectJoint r c U 7) ≤
      2 * (cellCount * (cellCount - 1)) * Fintype.card (Table r c) := by
  dsimp only
  have h := defectJoint_card_le_padded r c (11 * d * (m + n - 2)) 7
  have hc := actualShape_padded_count_le_twice r c
  dsimp only at hc
  apply h.trans
  calc
    _ ≤ _ := Nat.mul_le_mul_left _ hc
    _ = _ := by ring

end
end Math115.PhysicalTraceJoin
