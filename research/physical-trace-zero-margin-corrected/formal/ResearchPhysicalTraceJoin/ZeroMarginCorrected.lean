/-
SPDX-License-Identifier: Apache-2.0
Ordered positive-margin preprocessing, computed scale/reference branch,
actual corrected trials and fresh retries, then exact ordinary-table zero
restoration. A reduced defect start and feasible fallback remain supplied.
-/
import ResearchPhysicalTraceJoin.GeneralCorrectedRetry
import ResearchPhysicalTraceJoin.ZeroMarginPreparation

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

private theorem correctionSuccessAtCutoff {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (U : ℕ) (hU : U = 11 * dimensionAllowance (I := Fin m) (J := Fin n) * (m + n - 2))
    [Nonempty (DefectVertices r c U 7)] (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) :
    let p := Fintype.card (Cells (firstPaperSmall r c U))
    (inverseSupportAllowance r c U : ℚ) / ((2 * (p * (p - 1)) : ℕ) : ℚ) ≤
      1 - (terminalIdealCorrectedLaw r c U 7).mass none := by
  subst U
  exact actualShape_terminalCorrected_success_lower r c hr hc

variable (xs ys : List ℕ)

/-- All counts and scales are recomputed on the ordered positive margins. -/
def positiveTraceCorrectionSuccess : ℚ :=
  let r := filteredMargin xs
  let c := filteredMargin ys
  let U := positiveTraceCutoff xs ys
  let p := Fintype.card (Cells (firstPaperSmall r c U))
  (inverseSupportAllowance r c U : ℚ) / ((2 * (p * (p - 1)) : ℕ) : ℚ)

def positiveTraceCorrectedRetryLaw (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) 7)
    (h k : ℕ) (fallback : Table (filteredMargin xs) (filteredMargin ys)) (R : ℕ) :
    RationalLaw (Table (listMargin xs) (listMargin ys)) :=
  restoreZeroMarginListsLaw xs ys
    (terminalCorrectedRetryLaw (filteredMargin xs) (filteredMargin ys)
      (positiveTraceCutoff xs ys) 7
      (positiveTraceReference_conditions xs ys hb).2.2.2.1
      (positiveTraceReference_conditions xs ys hb).2.2.2.2 start h k fallback R)

/-- The reference tag supplies dimensions, small-cell count and scale. -/
theorem positiveTraceCorrectionSuccess_positive
    (hb : positiveTraceBranch xs ys = .reference) :
    0 < positiveTraceCorrectionSuccess xs ys := by
  have hb' := positiveTraceReference_conditions xs ys hb
  have hp := hb'.2.2.1
  have hc0 := inverseSupportAllowance_positive (filteredMargin xs) (filteredMargin ys)
    (positiveTraceCutoff xs ys) hb'.1 hb'.2.1 (by omega)
  unfold positiveTraceCorrectionSuccess
  apply div_pos (Nat.cast_pos.mpr hc0)
  apply Nat.cast_pos.mpr
  exact Nat.mul_pos (by decide) (Nat.mul_pos (by omega) (by omega))

/-- The original-table error is the same as the reduced-table error. The
branch tag discharges scale/catalog guards and positive filtering discharges
margin positivity; there is no supplied counting or desired-error premise. -/
theorem positiveTraceCorrectedRetry_accuracy
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) 7)
    (h k : ℕ) (fallback : Table (filteredMargin xs) (filteredMargin ys)) (R : ℕ) :
    letI := table_nonempty (listMargin xs) (listMargin ys) htotal
    variation (positiveTraceCorrectedRetryLaw xs ys hb start h k fallback R)
      (uniformLaw (α := Table (listMargin xs) (listMargin ys))) ≤
        (1 - positiveTraceCorrectionSuccess xs ys)^R +
          (R : ℚ) * (dyadic h + dyadic k) := by
  letI := table_nonempty (listMargin xs) (listMargin ys) htotal
  letI := table_nonempty (filteredMargin xs) (filteredMargin ys) (filtered_totals_equal xs ys htotal)
  let r := filteredMargin xs
  let c := filteredMargin ys
  let U := positiveTraceCutoff xs ys
  letI : Nonempty (DefectVertices r c U 7) := ⟨start⟩
  have hb' := positiveTraceReference_conditions xs ys hb
  have hp := hb'.2.2.1
  have hrL := hb'.2.2.2.1
  have hcL := hb'.2.2.2.2
  have hscale : U = 11 * dimensionAllowance
      (I := Fin (positiveMargins xs).length) (J := Fin (positiveMargins ys).length) *
      ((positiveMargins xs).length + (positiveMargins ys).length - 2) := by
    simp only [U, positiveTraceCutoff_code, squareCutoff, Fintype.card_fin]
  have hs := correctionSuccessAtCutoff r c U hscale
    (filteredMargin_positive xs) (filteredMargin_positive ys)
  have hred := terminalCorrectedRetry_accuracy_of_success r c U 7 hrL hcL
    (filtered_totals_equal xs ys htotal) (positiveTraceReference_cutoff xs ys hb)
    (by decide) hp (filteredMargin_positive xs) (filteredMargin_positive ys)
    start h k fallback R (positiveTraceCorrectionSuccess xs ys) hs
  have hz := restoreZeroMarginListsLaw_uniform_variation xs ys htotal
    (terminalCorrectedRetryLaw r c U 7 hrL hcL start h k fallback R)
  exact hz.le.trans hred

end
end Math115.PhysicalTraceJoin
