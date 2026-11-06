/-
SPDX-License-Identifier: Apache-2.0
Ordinary matrix-code wrappers for the already proved legacy and deterministic
positive-margin branches, with exact zero restoration. No sampler or
probability analysis is duplicated, and no new runtime bound is asserted.
-/
import ResearchPhysicalTraceJoin.GeneralLegacyFallback
import ResearchPhysicalTraceJoin.GeneralInitializationCode
import ResearchPhysicalTraceJoin.ZeroMarginMatrix

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms CompletionCounts PhysicalCompletionOracle
open Math115.CompletionRetryBudget
open scoped BigOperators

/-- The frozen program computes its own legacy schedule on positive lists. -/
def rawPositiveLegacyWordWidth (xs ys : List ℕ) (h : ℕ) : ℕ :=
  Math115.LatticeScheduleProgram.totalBits ((positiveMargins xs,positiveMargins ys),h)

def rawPositiveLegacyReducedWordCode (xs ys : List ℕ) (h : ℕ) (word : List Bool) : MatrixCode :=
  Math115.LatticeSampler.draw (((positiveMargins xs,positiveMargins ys),h),word)

/-- Original ordering and zero lines are restored by the existing ordinary
matrix program after the unchanged frozen backend returns its reduced code. -/
def rawPositiveLegacyWordCode (xs ys : List ℕ) (h : ℕ) (word : List Bool) : MatrixCode :=
  restoreZeroMarginMatrix xs ys (rawPositiveLegacyReducedWordCode xs ys h word)

def rawPositiveDeterministicWordCode (xs ys : List ℕ) (_word : List Bool) : MatrixCode :=
  restoreZeroMarginMatrix xs ys (positiveTraceFallbackCode xs ys)

open scoped Classical
noncomputable section

/-- Exact request width, at all natural precisions including zero. -/
theorem rawPositiveLegacyWordWidth_eq (xs ys : List ℕ) (h : ℕ) :
    rawPositiveLegacyWordWidth xs ys h = positiveLegacyWordWidth xs ys h := by
  have he := Math115.LatticeScheduleProgram.totalBits_ofFn
    (filteredMargin xs) (filteredMargin ys) h
  simpa only [rawPositiveLegacyWordWidth, positiveLegacyWordWidth, filteredMargin,
    ofFn_listMargin] using he

theorem rawPositiveLegacyReducedWordCode_eq (xs ys : List ℕ)
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) (h : ℕ)
    (word : Fin (positiveLegacyWordWidth xs ys h) → Bool) :
    rawPositiveLegacyReducedWordCode xs ys h (List.ofFn word) =
      matrixCode (positiveLegacyReducedWord xs ys htotal h word).val := by
  have he := Math115.LatticeSampler.draw_code (filteredMargin xs) (filteredMargin ys)
    (filtered_totals_equal xs ys htotal) h word
  simpa only [rawPositiveLegacyReducedWordCode, positiveLegacyReducedWord, filteredMargin,
    ofFn_listMargin] using he

/-- Every reserved word agrees pointwise, without any branch, probability,
or accuracy premise. The same statement applies at h=0. -/
theorem rawPositiveLegacyWordCode_eq (xs ys : List ℕ)
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) (h : ℕ)
    (word : Fin (positiveLegacyWordWidth xs ys h) → Bool) :
    rawPositiveLegacyWordCode xs ys h (List.ofFn word) =
      matrixCode (positiveLegacyWord xs ys htotal h word).val := by
  unfold rawPositiveLegacyWordCode
  rw [rawPositiveLegacyReducedWordCode_eq xs ys htotal h word]
  exact restoreZeroMarginMatrix_code xs ys _

/-- Deterministic restoration agrees on its unique zero-width typed word;
the ordinary function takes no semantic table or equal-total proof input. -/
theorem rawPositiveDeterministicWordCode_eq (xs ys : List ℕ)
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) (word : Fin 0 → Bool) :
    rawPositiveDeterministicWordCode xs ys (List.ofFn word) =
      matrixCode (positiveDeterministicWord xs ys htotal word).val := by
  unfold rawPositiveDeterministicWordCode
  rw [positiveTraceFallbackCode_code xs ys htotal]
  exact restoreZeroMarginMatrix_code xs ys _

end
end Math115.PhysicalTraceJoin
