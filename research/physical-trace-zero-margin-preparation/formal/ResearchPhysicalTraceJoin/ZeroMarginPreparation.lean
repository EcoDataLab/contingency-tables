/-
SPDX-License-Identifier: Apache-2.0
Compose stable zero-margin list preprocessing with the actual reduced
scale/catalog/branch preparation and the checked finite-word reference walk.
The reference walk still takes an actual defect start and returns a labelled
physical completion pair. Ordinary-table restoration is a separate exact law
interface, usable after the unresolved general repair/acceptance step.
-/
import ResearchPhysicalTraceJoin.ZeroMarginLists
import ResearchPhysicalTraceJoin.TracePreparation
import ResearchPhysicalTraceJoin.Schedule

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles CompletionCounts SmallContextCoordinates
open FirstSuccess ResidualMixture FairBits
open Math115.RetainedChainSquare Math115.PhysicalDefectTrace
open Math115.CompletionRetryBudget
open scoped BigOperators Classical

def positiveTraceInput (xs ys : List ℕ) : List ℕ × List ℕ :=
  (positiveMargins xs, positiveMargins ys)

def positiveTraceCutoff (xs ys : List ℕ) : ℕ := traceCutoff (positiveTraceInput xs ys)

def positiveTraceBranch (xs ys : List ℕ) : TraceInputBranch :=
  traceInputBranch (positiveTraceInput xs ys)

noncomputable section
variable (xs ys : List ℕ)

theorem positiveTraceInput_code :
    positiveTraceInput xs ys = (List.ofFn (filteredMargin xs), List.ofFn (filteredMargin ys)) := by
  simp only [positiveTraceInput, ofFn_filteredMargin]

theorem positiveTraceCutoff_code :
    positiveTraceCutoff xs ys =
      squareCutoff (I := Fin (positiveMargins xs).length) (J := Fin (positiveMargins ys).length) := by
  rw [positiveTraceCutoff, positiveTraceInput_code, traceCutoff_ofFn]

/-- At a fixed supplied cutoff the retained-cell test is literal. This
does not assert mask equality when the cutoff itself is changed. -/
theorem filteredSmallMask_entry (U : ℕ)
    (i : Fin (positiveMargins xs).length) (j : Fin (positiveMargins ys).length) :
    firstPaperSmall (filteredMargin xs) (filteredMargin ys) U i j =
      firstPaperSmall (listMargin xs) (listMargin ys) U
        (positiveIndexEquiv xs i).val (positiveIndexEquiv ys j).val := by
  simp only [firstPaperSmall, filteredMargin_at_retained]

/-- Computed reduced list positions select exactly the corresponding
original retained margins at any cutoff, including U=0. -/
theorem filteredLargeIndices_membership (U : ℕ) (i : Fin (positiveMargins xs).length) :
    i.val ∈ largeIndices (U, positiveMargins xs) ↔
      U ≤ listMargin xs (positiveIndexEquiv xs i).val := by
  have hi := largeIndices_ofFn_mem (filteredMargin xs) U i
  simpa only [ofFn_filteredMargin, filteredMargin_at_retained] using hi

theorem positiveTraceReference_conditions
    (hb : positiveTraceBranch xs ys = .reference) :
    2 ≤ (positiveMargins xs).length ∧ 2 ≤ (positiveMargins ys).length ∧
    2 ≤ Fintype.card (Cells (firstPaperSmall (filteredMargin xs) (filteredMargin ys)
      (positiveTraceCutoff xs ys))) ∧
    0 < (largeIndices (positiveTraceCutoff xs ys, List.ofFn (filteredMargin xs))).length ∧
    0 < (largeIndices (positiveTraceCutoff xs ys, List.ofFn (filteredMargin ys))).length := by
  change traceInputBranch (positiveTraceInput xs ys) = .reference at hb
  rw [positiveTraceInput_code] at hb
  rw [positiveTraceCutoff_code]
  exact (traceInputBranch_reference_iff (filteredMargin xs) (filteredMargin ys)).mp hb

theorem positiveTraceReference_cutoff
    (hb : positiveTraceBranch xs ys = .reference) : 2 ≤ positiveTraceCutoff xs ys := by
  have h := positiveTraceReference_conditions xs ys hb
  rw [positiveTraceCutoff_code]
  exact squareCutoff_at_least_two (by simpa using h.1) (by simpa using h.2.1)

def positiveTraceWordWidth (h : ℕ) : ℕ :=
  terminalScheduleWordWidth (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) 7 h

/-- The branch certificate discharges computed-list and scale conditions;
the actual start is intentionally still an explicit input. -/
def positiveTraceReferenceWord (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) 7)
    (h : ℕ) (word : Fin (positiveTraceWordWidth xs ys h) → Bool) :
    DefectJoint (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) 7 :=
  terminalScheduleWord (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) 7
    (positiveTraceReference_conditions xs ys hb).2.2.2.1
    (positiveTraceReference_conditions xs ys hb).2.2.2.2 start h word

/-- No remaining scale, p-count or completion-accuracy premise: they come
from the actual preparation tag and the existing checked backend. The
target remains the reduced defect-labelled joint, not original tables. -/
theorem positiveTraceReferenceWord_accuracy
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) 7)
    (h : ℕ) :
    letI : Nonempty (DefectVertices (filteredMargin xs) (filteredMargin ys)
      (positiveTraceCutoff xs ys) 7) := ⟨start⟩
    (variation
      (mapLaw (uniformLaw (α := Fin (positiveTraceWordWidth xs ys h) → Bool))
        (positiveTraceReferenceWord xs ys hb start h))
      (uniformLaw (α := DefectJoint (filteredMargin xs) (filteredMargin ys)
        (positiveTraceCutoff xs ys) 7)) : ℝ) ≤ (dyadic h : ℝ) := by
  letI : Nonempty (DefectVertices (filteredMargin xs) (filteredMargin ys)
    (positiveTraceCutoff xs ys) 7) := ⟨start⟩
  exact terminalScheduleWord_accuracy (filteredMargin xs) (filteredMargin ys)
    (positiveTraceCutoff xs ys) 7
    (positiveTraceReference_conditions xs ys hb).2.2.2.1
    (positiveTraceReference_conditions xs ys hb).2.2.2.2
    (filtered_totals_equal xs ys htotal) (positiveTraceReference_cutoff xs ys hb)
    (by decide) (positiveTraceReference_conditions xs ys hb).2.2.1 start h

/-- For the deterministic reduced branch, any feasible reduced table
restores to the exact original uniform law. This does not choose that table. -/
theorem positiveTraceDeterministic_restored_uniform
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .deterministic)
    (X : Table (filteredMargin xs) (filteredMargin ys)) :
    letI := table_nonempty (listMargin xs) (listMargin ys) htotal
    restoreZeroMarginListsLaw xs ys (pointLaw X) =
      uniformLaw (α := Table (listMargin xs) (listMargin ys)) := by
  letI := table_nonempty (listMargin xs) (listMargin ys) htotal
  letI := table_nonempty (filteredMargin xs) (filteredMargin ys) (filtered_totals_equal xs ys htotal)
  change traceInputBranch (positiveTraceInput xs ys) = .deterministic at hb
  rw [positiveTraceInput_code] at hb
  rw [deterministicBranch_pointLaw_uniform (filteredMargin xs) (filteredMargin ys)
    (filtered_totals_equal xs ys htotal) hb X]
  exact restoreZeroMarginListsLaw_uniform xs ys htotal

/-- The concrete ordered preprocessing agrees with the retuning fixture. -/
theorem positiveTraceBranch_retuning_fixture :
    positiveTraceInput [0, 600, 600] [600, 600] = ([600, 600], [600, 600]) ∧
    positiveTraceCutoff [0, 600, 600] [600, 600] = 418 ∧
    positiveTraceBranch [0, 600, 600] [600, 600] = .noSmall := by
  decide

end
end Math115.PhysicalTraceJoin
