/-
SPDX-License-Identifier: Apache-2.0
An actual empty-defect obstruction when all small cells belong to zero
original-margin rows. A concrete equal-total fixture still has both large
lists and at least two small cells. Thus these hypotheses do not supply
the starting defect required by the defect-walk interface.
-/
import Research.PhysicalTraceGeometry
import Math115.PhysicalComputedProposal

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open PaddedCompletions
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace Math115.PhysicalComputedProposal
open scoped BigOperators Classical

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ) (U L : ℕ)

/-- The actual positive-weight state's original residual row test forces
every small entry in a zero-margin row to vanish. -/
lemma actual_small_entry_zero_of_row_zero (x : States r c U L) (i : I) (j : J)
    (hs : firstPaperSmall r c U i j = true) (hr0 : r i = 0) :
    smallView (firstPaperSmall r c U)
      (physicalProfile _ (capacity r c U L) r c L x) false i j = 0 := by
  let small := firstPaperSmall r c U
  let X := smallView small (physicalProfile _ (capacity r c U L) r c L x) false
  have hrow : smallRow small X i ≤ r i :=
    (physicalProfile_feasible r c U L x).residuals.1 i
  have hentry : X i j ≤ smallRow small X i := by
    calc
      X i j = if small i j then X i j else 0 := by simp only [small, hs, ite_true]
      _ ≤ ∑ k, if small i k then X i k else 0 :=
        Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [hr0] at hrow
  change X i j = 0
  omega

/-- This premise concerns the actual first-paper small mask. It needs no
padding/cutoff lower bound, equal-total assumption, or large-list premise. -/
theorem defects_isEmpty_of_zero_small_rows
    (hzero : ∀ i j, firstPaperSmall r c U i j = true → r i = 0) :
    IsEmpty (DefectVertices r c U L) := by
  refine ⟨fun d => ?_⟩
  obtain ⟨s, t, hs, ht, hd⟩ := defect_isSingleDefect r c U L d
  have hz := actual_small_entry_zero_of_row_zero r c U L d.val t.1 t.2 ht
    (hzero t.1 t.2 ht)
  have hp := hd.positive_entry
  omega

section Fixture

def obstructionRows : Fin 3 → ℕ := ![0, 4, 4]
def obstructionColumns : Fin 2 → ℕ := ![4, 4]

theorem obstruction_equal_totals :
    (∑ i, obstructionRows i) = ∑ j, obstructionColumns j := by
  decide

theorem obstruction_large_rows :
    largeIndices (2, List.ofFn obstructionRows) = [1, 2] := by
  decide

theorem obstruction_large_columns :
    largeIndices (2, List.ofFn obstructionColumns) = [0, 1] := by
  decide

theorem obstruction_both_large :
    0 < (largeIndices (2, List.ofFn obstructionRows)).length ∧
      0 < (largeIndices (2, List.ofFn obstructionColumns)).length := by
  rw [obstruction_large_rows, obstruction_large_columns]
  decide

theorem obstruction_small_rows_zero :
    ∀ i j, firstPaperSmall obstructionRows obstructionColumns 2 i j = true →
      obstructionRows i = 0 := by
  intro i j hs
  fin_cases i <;> fin_cases j <;>
    norm_num [firstPaperSmall, obstructionRows, obstructionColumns] at hs ⊢

/-- Two distinct small cells exist in row zero; no large state enumeration
is used to establish the small-cell-count hypothesis. -/
theorem obstruction_two_small_cells :
    2 ≤ Fintype.card (Cells (firstPaperSmall obstructionRows obstructionColumns 2)) := by
  let f : Fin 2 → Cells (firstPaperSmall obstructionRows obstructionColumns 2) :=
    fun j => ⟨(0, j), by simp [firstPaperSmall, obstructionRows]⟩
  have hf : Function.Injective f := by
    intro j k h
    exact congrArg
      (fun a : Cells (firstPaperSmall obstructionRows obstructionColumns 2) => a.val.2) h
  have hc := Fintype.card_le_of_injective f hf
  simpa using hc

theorem obstruction_defects_isEmpty :
    IsEmpty (DefectVertices obstructionRows obstructionColumns 2 7) :=
  defects_isEmpty_of_zero_small_rows obstructionRows obstructionColumns 2 7
    obstruction_small_rows_zero

/-- All displayed trace-scale conditions hold, but there is no defect
available to supply as the initial state of a defect-only walk. -/
theorem obstruction_no_defect_start :
    ¬Nonempty (DefectVertices obstructionRows obstructionColumns 2 7) := by
  rintro ⟨d⟩
  exact obstruction_defects_isEmpty.false d

end Fixture
end
end Math115.PhysicalTraceJoin
