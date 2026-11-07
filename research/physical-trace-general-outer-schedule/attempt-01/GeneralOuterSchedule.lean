/-
SPDX-License-Identifier: Apache-2.0
Explicit natural outer retry and precision settings for requested dyadic
accuracy, on ordered positive-margin reference inputs. Start and fallback
remain parameters. This is a law-level schedule, without a running-time bound.
-/
import ResearchPhysicalTraceJoin.ZeroMarginCorrected
import ResearchPhysicalStarBudget.Schedule

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

/-- A deliberately loose count-polynomial retry block; no logarithm of a
rational success probability is needed. -/
def positiveTraceOuterBlock (xs ys : List ℕ) : ℕ :=
  let p := Fintype.card (Cells (firstPaperSmall (filteredMargin xs)
    (filteredMargin ys) (positiveTraceCutoff xs ys)))
  2 * (p * (p - 1))

def positiveTraceOuterAttempts (xs ys : List ℕ) (t : ℕ) : ℕ :=
  positiveTraceOuterBlock xs ys * (t + 2)

def positiveTraceOuterPrecision (xs ys : List ℕ) (t : ℕ) : ℕ :=
  t + 3 + Nat.clog 2 (positiveTraceOuterAttempts xs ys t)

theorem positiveTraceOuterBlock_positive (xs ys : List ℕ)
    (hb : positiveTraceBranch xs ys = .reference) :
    0 < positiveTraceOuterBlock xs ys := by
  have hp := (positiveTraceReference_conditions xs ys hb).2.2.1
  exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (by omega))

/-- Positivity of the actual integer numerator supplies the reciprocal
block bound. The upper bound comes from the actual ideal law's failure mass. -/
theorem positiveTraceCorrectionSuccess_bounds (xs ys : List ℕ)
    (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys)
      (positiveTraceCutoff xs ys) 7) :
    1 / (positiveTraceOuterBlock xs ys : ℚ) ≤ positiveTraceCorrectionSuccess xs ys ∧
      positiveTraceCorrectionSuccess xs ys ≤ 1 := by
  let r := filteredMargin xs
  let c := filteredMargin ys
  let U := positiveTraceCutoff xs ys
  letI : Nonempty (DefectVertices r c U 7) := ⟨start⟩
  have hb' := positiveTraceReference_conditions xs ys hb
  have hc0 := inverseSupportAllowance_positive r c U hb'.1 hb'.2.1 (by omega)
  have hA : (0 : ℚ) < positiveTraceOuterBlock xs ys :=
    Nat.cast_pos.mpr (positiveTraceOuterBlock_positive xs ys hb)
  constructor
  · have hc1 : (1 : ℚ) ≤ inverseSupportAllowance r c U := by exact_mod_cast hc0
    exact div_le_div_of_nonneg_right hc1 hA.le
  · have hscale : U = 11 * dimensionAllowance
        (I := Fin (positiveMargins xs).length) (J := Fin (positiveMargins ys).length) *
        ((positiveMargins xs).length + (positiveMargins ys).length - 2) := by
      simp only [U, positiveTraceCutoff_code, squareCutoff, Fintype.card_fin]
    have hs : positiveTraceCorrectionSuccess xs ys ≤
        1 - (terminalIdealCorrectedLaw r c U 7).mass none := by
      unfold positiveTraceCorrectionSuccess
      change (inverseSupportAllowance r c U : ℚ) / _ ≤ _
      subst U
      exact actualShape_terminalCorrected_success_lower r c
        (filteredMargin_positive xs) (filteredMargin_positive ys)
    exact hs.trans (sub_le_self _ ((terminalIdealCorrectedLaw r c U 7).nonnegative none))

/-- Reuse the finite geometric reciprocal-block lemma for the outer failures. -/
theorem positiveTraceOuter_failure_budget (xs ys : List ℕ)
    (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys)
      (positiveTraceCutoff xs ys) 7) (t : ℕ) :
    (1 - positiveTraceCorrectionSuccess xs ys)^(positiveTraceOuterAttempts xs ys t) ≤
      dyadic (t + 2) := by
  have hs := positiveTraceCorrectionSuccess_bounds xs ys hb start
  have hA := positiveTraceOuterBlock_positive xs ys hb
  have hq : 0 ≤ 1 - positiveTraceCorrectionSuccess xs ys := sub_nonneg.mpr hs.2
  have hrecip : 1 - positiveTraceCorrectionSuccess xs ys ≤
      1 - 1 / (positiveTraceOuterBlock xs ys : ℚ) := by linarith [hs.1]
  unfold positiveTraceOuterAttempts
  rw [pow_mul]
  calc
    _ ≤ (1 / 2 : ℚ)^(t + 2) := by
      apply pow_le_pow_left₀ (pow_nonneg hq _)
      exact (pow_le_pow_left₀ hq hrecip _).trans
        (Math115.PhysicalStarBudget.reciprocal_block _ hA)
    _ = dyadic (t + 2) := by simp [dyadic]

/-- Each of the two corrected-word accuracy settings is computed from the
outer retry count, so their accumulated contribution fits a quarter-budget. -/
theorem positiveTraceOuter_draw_budget (xs ys : List ℕ) (t : ℕ) :
    (positiveTraceOuterAttempts xs ys t : ℚ) *
      dyadic (positiveTraceOuterPrecision xs ys t) ≤ dyadic (t + 3) := by
  have hclog : (positiveTraceOuterAttempts xs ys t : ℚ) ≤
      (2 : ℚ)^Nat.clog 2 (positiveTraceOuterAttempts xs ys t) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (positiveTraceOuterAttempts xs ys t)
  calc
    _ ≤ (2 : ℚ)^Nat.clog 2 (positiveTraceOuterAttempts xs ys t) *
        dyadic (positiveTraceOuterPrecision xs ys t) :=
      mul_le_mul_of_nonneg_right hclog (dyadic_positive _).le
    _ = dyadic (t + 3) := by
      unfold dyadic positiveTraceOuterPrecision
      rw [pow_add]
      field_simp

theorem positiveTraceOuter_budget (xs ys : List ℕ)
    (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys)
      (positiveTraceCutoff xs ys) 7) (t : ℕ) :
    (1 - positiveTraceCorrectionSuccess xs ys)^(positiveTraceOuterAttempts xs ys t) +
      (positiveTraceOuterAttempts xs ys t : ℚ) *
        (dyadic (positiveTraceOuterPrecision xs ys t) +
          dyadic (positiveTraceOuterPrecision xs ys t)) ≤ dyadic t := by
  have hf := positiveTraceOuter_failure_budget xs ys hb start t
  have hd := positiveTraceOuter_draw_budget xs ys t
  have he := dyadic_succ (t + 2)
  have ht := dyadic_antitone_step (t + 1)
  have ht' := dyadic_antitone_step t
  have : (1 - positiveTraceCorrectionSuccess xs ys)^(positiveTraceOuterAttempts xs ys t) +
      (positiveTraceOuterAttempts xs ys t : ℚ) *
        (dyadic (positiveTraceOuterPrecision xs ys t) +
          dyadic (positiveTraceOuterPrecision xs ys t)) ≤ dyadic (t + 1) := by
    have he' := dyadic_succ (t + 1)
    nlinarith
  exact this.trans ht'

def positiveTraceOuterScheduledLaw (xs ys : List ℕ)
    (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) 7)
    (fallback : Table (filteredMargin xs) (filteredMargin ys)) (t : ℕ) :
    RationalLaw (Table (listMargin xs) (listMargin ys)) :=
  positiveTraceCorrectedRetryLaw xs ys hb start
    (positiveTraceOuterPrecision xs ys t) (positiveTraceOuterPrecision xs ys t)
    fallback (positiveTraceOuterAttempts xs ys t)

/-- The requested dyadic accuracy is now the only supplied accuracy setting.
This law still has independent retries and supplied start/fallback values. -/
theorem positiveTraceOuterScheduled_accuracy (xs ys : List ℕ)
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) 7)
    (fallback : Table (filteredMargin xs) (filteredMargin ys)) (t : ℕ) :
    letI := table_nonempty (listMargin xs) (listMargin ys) htotal
    variation (positiveTraceOuterScheduledLaw xs ys hb start fallback t)
      (uniformLaw (α := Table (listMargin xs) (listMargin ys))) ≤ dyadic t := by
  exact (positiveTraceCorrectedRetry_accuracy xs ys htotal hb start
    (positiveTraceOuterPrecision xs ys t) (positiveTraceOuterPrecision xs ys t)
    fallback (positiveTraceOuterAttempts xs ys t)).trans
      (positiveTraceOuter_budget xs ys hb start t)

end
end Math115.PhysicalTraceJoin
