/-
SPDX-License-Identifier: Apache-2.0
Explicit natural outer retry and precision settings for requested dyadic
accuracy, on ordered positive-margin reference inputs. Start and fallback
remain parameters. This is a law-level schedule, without a running-time bound.
-/
import ResearchPhysicalTraceJoin.GeneralOuterSchedule
import ResearchPhysicalTraceJoin.GeneralLinearSuccess

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open FirstSuccess ResidualMixture
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.RetainedChainSquare Math115.CompletionRetryBudget
open scoped BigOperators Classical
noncomputable section

/-- Use the smaller of the original count block and the linear incidence block. -/
def positiveTraceLinearBlock (xs ys : List ℕ) : ℕ :=
  let p := Fintype.card (Cells (firstPaperSmall (filteredMargin xs)
    (filteredMargin ys) (positiveTraceCutoff xs ys)))
  min (positiveTraceOuterBlock xs ys) (4 * p)

def positiveTraceLinearAttempts (xs ys : List ℕ) (t : ℕ) : ℕ :=
  positiveTraceLinearBlock xs ys * (t + 1)

def positiveTraceLinearPrecision (xs ys : List ℕ) (t : ℕ) : ℕ :=
  t + 2 + Nat.clog 2 (positiveTraceLinearAttempts xs ys t)

theorem positiveTraceLinearBlock_positive (xs ys : List ℕ)
    (hb : positiveTraceBranch xs ys = .reference) :
    0 < positiveTraceLinearBlock xs ys := by
  have hp := (positiveTraceReference_conditions xs ys hb).2.2.1
  exact lt_min (positiveTraceOuterBlock_positive xs ys hb)
    (Nat.mul_pos (by decide) (by omega))

theorem positiveTraceLinearBlock_le_linear (xs ys : List ℕ) :
    let p := Fintype.card (Cells (firstPaperSmall (filteredMargin xs)
      (filteredMargin ys) (positiveTraceCutoff xs ys)))
    positiveTraceLinearBlock xs ys ≤ 4 * p := by
  exact Nat.min_le_right _ _

theorem positiveTraceLinearAttempts_le_old (xs ys : List ℕ) (t : ℕ) :
    positiveTraceLinearAttempts xs ys t ≤ positiveTraceOuterAttempts xs ys t := by
  have hblock : positiveTraceLinearBlock xs ys ≤ positiveTraceOuterBlock xs ys :=
    Nat.min_le_left _ _
  exact Nat.mul_le_mul hblock (show t + 1 ≤ t + 2 by omega)

/-- Reuse the finite geometric reciprocal-block lemma for the outer failures. -/
theorem positiveTraceLinear_failure_budget (xs ys : List ℕ)
    (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys)
      (positiveTraceCutoff xs ys) 7) (t : ℕ) :
    (1 - positiveTraceCorrectionSuccess xs ys)^(positiveTraceLinearAttempts xs ys t) ≤
      dyadic (t + 1) := by
  have hs := positiveTraceCorrectionSuccess_bounds xs ys hb start
  have hlin : 1 / (positiveTraceLinearBlock xs ys : ℚ) ≤
      positiveTraceCorrectionSuccess xs ys := by
    unfold positiveTraceLinearBlock
    rw [Nat.min_def]
    split_ifs
    · exact hs.1
    · simpa only [Nat.cast_mul, Nat.cast_ofNat] using
        positiveTraceCorrectionSuccess_linear xs ys hb
  have hA := positiveTraceLinearBlock_positive xs ys hb
  have hq : 0 ≤ 1 - positiveTraceCorrectionSuccess xs ys := sub_nonneg.mpr hs.2
  have hrecip : 1 - positiveTraceCorrectionSuccess xs ys ≤
      1 - 1 / (positiveTraceLinearBlock xs ys : ℚ) := by linarith [hlin]
  unfold positiveTraceLinearAttempts
  rw [pow_mul]
  calc
    _ ≤ (1 / 2 : ℚ)^(t + 1) := by
      apply pow_le_pow_left₀ (pow_nonneg hq _)
      exact (pow_le_pow_left₀ hq hrecip _).trans
        (Math115.PhysicalStarBudget.reciprocal_block _ hA)
    _ = dyadic (t + 1) := by simp [dyadic]

/-- Each of the two corrected-word accuracy settings is computed from the
outer retry count, so their accumulated contribution fits a quarter-budget. -/
theorem positiveTraceLinear_draw_budget (xs ys : List ℕ) (t : ℕ) :
    (positiveTraceLinearAttempts xs ys t : ℚ) *
      dyadic (positiveTraceLinearPrecision xs ys t) ≤ dyadic (t + 2) := by
  have hclog : (positiveTraceLinearAttempts xs ys t : ℚ) ≤
      (2 : ℚ)^Nat.clog 2 (positiveTraceLinearAttempts xs ys t) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (positiveTraceLinearAttempts xs ys t)
  calc
    _ ≤ (2 : ℚ)^Nat.clog 2 (positiveTraceLinearAttempts xs ys t) *
        dyadic (positiveTraceLinearPrecision xs ys t) :=
      mul_le_mul_of_nonneg_right hclog (dyadic_positive _).le
    _ = dyadic (t + 2) := by
      unfold dyadic positiveTraceLinearPrecision
      rw [pow_add]
      field_simp

theorem positiveTraceLinear_budget (xs ys : List ℕ)
    (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys)
      (positiveTraceCutoff xs ys) 7) (t : ℕ) :
    (1 - positiveTraceCorrectionSuccess xs ys)^(positiveTraceLinearAttempts xs ys t) +
      (positiveTraceLinearAttempts xs ys t : ℚ) *
        (dyadic (positiveTraceLinearPrecision xs ys t) +
          dyadic (positiveTraceLinearPrecision xs ys t)) ≤ dyadic t := by
  have hf := positiveTraceLinear_failure_budget xs ys hb start t
  have hd := positiveTraceLinear_draw_budget xs ys t
  have hhalf := dyadic_succ t
  have hquarter := dyadic_succ (t + 1)
  nlinarith

def positiveTraceLinearScheduledLaw (xs ys : List ℕ)
    (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) 7)
    (fallback : Table (filteredMargin xs) (filteredMargin ys)) (t : ℕ) :
    RationalLaw (Table (listMargin xs) (listMargin ys)) :=
  positiveTraceCorrectedRetryLaw xs ys hb start
    (positiveTraceLinearPrecision xs ys t) (positiveTraceLinearPrecision xs ys t)
    fallback (positiveTraceLinearAttempts xs ys t)

/-- The requested dyadic accuracy is now the only supplied accuracy setting.
This law still has independent retries and supplied start/fallback values. -/
theorem positiveTraceLinearScheduled_accuracy (xs ys : List ℕ)
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) 7)
    (fallback : Table (filteredMargin xs) (filteredMargin ys)) (t : ℕ) :
    letI := table_nonempty (listMargin xs) (listMargin ys) htotal
    variation (positiveTraceLinearScheduledLaw xs ys hb start fallback t)
      (uniformLaw (α := Table (listMargin xs) (listMargin ys))) ≤ dyadic t := by
  exact (positiveTraceCorrectedRetry_accuracy xs ys htotal hb start
    (positiveTraceLinearPrecision xs ys t) (positiveTraceLinearPrecision xs ys t)
    fallback (positiveTraceLinearAttempts xs ys t)).trans
      (positiveTraceLinear_budget xs ys hb start t)

end
end Math115.PhysicalTraceJoin
