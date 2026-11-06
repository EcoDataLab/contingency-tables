/-
SPDX-License-Identifier: Apache-2.0
Initialized, automatically scheduled flat-word reference sampler on original
ordered margins. This identifies a typed finite-word map, not an encoded
machine or a running-time bound.
-/
import ResearchPhysicalTraceJoin.GeneralInitialization
import ResearchPhysicalTraceJoin.GeneralLinearSchedule
import ResearchPhysicalTraceJoin.GeneralRetryWord

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open FirstSuccess ResidualMixture CompletionCounts
open Math115.CompletionRetryBudget
open scoped BigOperators Classical
noncomputable section
variable (xs ys : List ℕ)

def positiveReferenceWordWidth (t : ℕ) : ℕ :=
  terminalCorrectedRetryWordWidth (filteredMargin xs) (filteredMargin ys)
    (positiveTraceCutoff xs ys) 7
    (positiveTraceLinearPrecision xs ys t) (positiveTraceLinearPrecision xs ys t)
    (positiveTraceLinearAttempts xs ys t)

/-- Every word produces an ordinary table on the original ordered lists.
The start, fallback, repeat count and both precisions are derived internally. -/
def positiveReferenceWord
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) (t : ℕ)
    (word : Fin (positiveReferenceWordWidth xs ys t) → Bool) :
    Table (listMargin xs) (listMargin ys) :=
  (zeroMarginListEquiv xs ys).symm
    (terminalCorrectedRetryWord (filteredMargin xs) (filteredMargin ys)
      (positiveTraceCutoff xs ys) 7
      (positiveTraceReference_conditions xs ys hb).2.2.2.1
      (positiveTraceReference_conditions xs ys hb).2.2.2.2
      (positiveTraceInitialStart xs ys htotal hb)
      (positiveTraceLinearPrecision xs ys t) (positiveTraceLinearPrecision xs ys t)
      (positiveTraceFallback xs ys htotal) (positiveTraceLinearAttempts xs ys t) word)

def positiveReferenceWordLaw
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) (t : ℕ) :
    RationalLaw (Table (listMargin xs) (listMargin ys)) :=
  mapLaw (uniformLaw (α := Fin (positiveReferenceWordWidth xs ys t) → Bool))
    (positiveReferenceWord xs ys htotal hb t)

/-- Exact identification with the proved initialized and budgeted retry law. -/
theorem positiveReferenceWord_law
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) (t : ℕ) :
    positiveReferenceWordLaw xs ys htotal hb t =
      positiveTraceLinearScheduledLaw xs ys hb
        (positiveTraceInitialStart xs ys htotal hb) (positiveTraceFallback xs ys htotal) t := by
  calc
    _ = restoreZeroMarginListsLaw xs ys
        (terminalCorrectedRetryWordLaw (filteredMargin xs) (filteredMargin ys)
          (positiveTraceCutoff xs ys) 7
          (positiveTraceReference_conditions xs ys hb).2.2.2.1
          (positiveTraceReference_conditions xs ys hb).2.2.2.2
          (positiveTraceInitialStart xs ys htotal hb)
          (positiveTraceLinearPrecision xs ys t) (positiveTraceLinearPrecision xs ys t)
          (positiveTraceFallback xs ys htotal) (positiveTraceLinearAttempts xs ys t)) :=
      mapLaw_equiv_output (zeroMarginListEquiv xs ys).symm _ _
    _ = _ := by rw [terminalCorrectedRetryWordLaw_eq]; rfl

/-- Equal totals and the computed reference tag suffice: no supplied start,
fallback, completion accuracy, success bound or outer-budget premise. -/
theorem positiveReferenceWord_accuracy
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) (t : ℕ) :
    letI := table_nonempty (listMargin xs) (listMargin ys) htotal
    variation (positiveReferenceWordLaw xs ys htotal hb t)
      (uniformLaw (α := Table (listMargin xs) (listMargin ys))) ≤ dyadic t := by
  letI := table_nonempty (listMargin xs) (listMargin ys) htotal
  rw [positiveReferenceWord_law]
  exact positiveTraceLinearScheduled_accuracy xs ys htotal hb
    (positiveTraceInitialStart xs ys htotal hb) (positiveTraceFallback xs ys htotal) t

end
end Math115.PhysicalTraceJoin
