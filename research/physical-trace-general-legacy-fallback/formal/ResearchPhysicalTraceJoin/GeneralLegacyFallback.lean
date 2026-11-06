/-
SPDX-License-Identifier: Apache-2.0
An explicit legacy finite-word fallback on the ordered positive margins.
The backend rebuilds its own U=5*d^3, L=3*d preparation; no equality with
the sharper classifier's U=11*d*(m+n-2), L=7 is asserted. This supplies
typed finite-word semantics, not a new encoded hybrid or runtime theorem.
-/
import ResearchPhysicalTraceJoin.ZeroMarginPreparation
import Math115.PhysicalBooleanSampler

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open FirstSuccess ResidualMixture FairBits CompletionCounts PhysicalCompletionOracle
open Math115.CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section
variable (xs ys : List ℕ)

/-- Scheduled legacy fair-bit width on the reduced ordered lists. -/
def positiveLegacyWordWidth (h : ℕ) : ℕ :=
  let r := filteredMargin xs
  let c := filteredMargin ys
  let d := dimensionAllowance (I := Fin (positiveMargins xs).length)
    (J := Fin (positiveMargins ys).length)
  let p := CompletionOuterSchedule.physicalSmallCount r c
  let base := CompletionOuterSchedule.physicalMassBase (J := Fin (positiveMargins ys).length) r
  PhysicalReferenceBoolean.outerBits (n := (positiveMargins ys).length) r
    (CompletionOuterSchedule.walkCount p d base h)
    (CompletionOuterSchedule.restartCount p h)
    (CompletionOuterSchedule.stepPrecision p d base h)
    (CompletionOuterSchedule.terminalPrecision p h)

/-- Complete existing backend, initialized and scheduled from reduced data. -/
def positiveLegacyReducedWord
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) (h : ℕ)
    (word : Fin (positiveLegacyWordWidth xs ys h) → Bool) :
    Table (filteredMargin xs) (filteredMargin ys) :=
  let r := filteredMargin xs
  let c := filteredMargin ys
  let d := dimensionAllowance (I := Fin (positiveMargins xs).length)
    (J := Fin (positiveMargins ys).length)
  let p := CompletionOuterSchedule.physicalSmallCount r c
  let base := CompletionOuterSchedule.physicalMassBase (J := Fin (positiveMargins ys).length) r
  PhysicalBooleanSampler.draw r c (filtered_totals_equal xs ys htotal)
    (CompletionOuterSchedule.walkCount p d base h)
    (CompletionOuterSchedule.restartCount p h)
    (CompletionOuterSchedule.stepPrecision p d base h)
    (CompletionOuterSchedule.terminalPrecision p h) word

def positiveLegacyWord
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) (h : ℕ)
    (word : Fin (positiveLegacyWordWidth xs ys h) → Bool) :
    Table (listMargin xs) (listMargin ys) :=
  (zeroMarginListEquiv xs ys).symm (positiveLegacyReducedWord xs ys htotal h word)

def positiveLegacyWordLaw
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) (h : ℕ) :
    RationalLaw (Table (listMargin xs) (listMargin ys)) :=
  mapLaw (uniformLaw (α := Fin (positiveLegacyWordWidth xs ys h) → Bool))
    (positiveLegacyWord xs ys htotal h)

theorem positiveLegacyWord_law
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) (h : ℕ) :
    positiveLegacyWordLaw xs ys htotal h =
      restoreZeroMarginListsLaw xs ys
        (mapLaw (uniformLaw (α := Fin (positiveLegacyWordWidth xs ys h) → Bool))
          (positiveLegacyReducedWord xs ys htotal h)) := by
  exact mapLaw_equiv_output (zeroMarginListEquiv xs ys).symm _ _

/-- No branch-preservation, supplied start, or desired-accuracy premise.
The fallback is valid for every equal-total pair, at its own legacy scales. -/
theorem positiveLegacyWord_accuracy
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) (h : ℕ) :
    letI := table_nonempty (listMargin xs) (listMargin ys) htotal
    (variation (positiveLegacyWordLaw xs ys htotal h)
      (uniformLaw (α := Table (listMargin xs) (listMargin ys))) : ℝ) ≤
        (dyadic h : ℝ) := by
  letI := table_nonempty (listMargin xs) (listMargin ys) htotal
  letI := table_nonempty (filteredMargin xs) (filteredMargin ys)
    (filtered_totals_equal xs ys htotal)
  rw [positiveLegacyWord_law,
    restoreZeroMarginListsLaw_uniform_variation xs ys htotal]
  exact PhysicalBooleanSampler.draw_explicit_accuracy
    (filteredMargin xs) (filteredMargin ys) (filtered_totals_equal xs ys htotal) h

/-- The deterministic dimension branch consumes the unique zero-width word. -/
def positiveDeterministicWord
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (_word : Fin 0 → Bool) : Table (listMargin xs) (listMargin ys) :=
  (zeroMarginListEquiv xs ys).symm
    (GreedyFeasibleTable.table (filteredMargin xs) (filteredMargin ys)
      (filtered_totals_equal xs ys htotal))

theorem positiveDeterministicWord_law
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .deterministic) :
    letI := table_nonempty (listMargin xs) (listMargin ys) htotal
    mapLaw (uniformLaw (α := Fin 0 → Bool)) (positiveDeterministicWord xs ys htotal) =
      uniformLaw (α := Table (listMargin xs) (listMargin ys)) := by
  letI := table_nonempty (listMargin xs) (listMargin ys) htotal
  let X := GreedyFeasibleTable.table (filteredMargin xs) (filteredMargin ys)
    (filtered_totals_equal xs ys htotal)
  calc
    _ = restoreZeroMarginListsLaw xs ys
        (mapLaw (uniformLaw (α := Fin 0 → Bool)) (fun _ => X)) :=
      mapLaw_equiv_output (zeroMarginListEquiv xs ys).symm _ _
    _ = restoreZeroMarginListsLaw xs ys (pointLaw X) := by rw [mapLaw_constant]
    _ = _ := positiveTraceDeterministic_restored_uniform xs ys htotal hb X

end
end Math115.PhysicalTraceJoin
