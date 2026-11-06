/-
SPDX-License-Identifier: Apache-2.0
List arithmetic for the sharper reference schedule. The runtime definitions
use only margin lists, catalogs and natural arithmetic. The correspondence
proofs refer to the existing semantic schedule; no state/table construction
or replacement accuracy premise enters the computed numbers.
-/
import ResearchPhysicalTraceJoin.GeneralCompleteReference

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalCompletionWidth Math115.LegacyResidualCap
open Research.ResidualSelectedBudget
open scoped BigOperators

def rawScheduleDimension (rs cs : List ℕ) : ℕ := marginDimension (rs,cs)

def rawScheduleSmallCount (rs cs : List ℕ) (U : ℕ) : ℕ :=
  (smallCellCatalog ((rs,cs),U)).length

def rawScheduleSmallLines (rs : List ℕ) (U : ℕ) : ℕ :=
  (rs.map (fun v => if v < U then 1 else 0)).sum

def rawScheduleLargeLines (rs : List ℕ) (U : ℕ) : ℕ :=
  (rs.map (fun v => if U ≤ v then 1 else 0)).sum

def rawScheduleResidualMass (rs cs : List ℕ) (U L : ℕ) : ℕ :=
  rs.sum + L * (rawScheduleLargeLines rs U * rawScheduleLargeLines cs U)

def rawUniformCompletionBits (rs cs : List ℕ) (U L h : ℕ) : ℕ :=
  CompletionRandomBudget.budgetCoefficient *
    (CompletionRandomBudget.combinedSize (rawScheduleDimension rs cs)
      (rawScheduleResidualMass rs cs U L) h)^85

def rawScheduleClockDenominator (rs cs : List ℕ) (U : ℕ) : ℕ :=
  2 * (4 * rawScheduleSmallCount rs cs U - 3)

def rawScheduleGapCount (rs cs : List ℕ) (U : ℕ) : ℕ :=
  let p := rawScheduleSmallCount rs cs U
  32 * p^3 * (U * (U-1) +
    4 * ((rawScheduleSmallLines rs U + rawScheduleSmallLines cs U) * U^2 + p * U))

def rawScheduleBase (rs cs : List ℕ) (U L : ℕ) : ℕ :=
  (rs.sum + rawScheduleDimension rs cs * L + U + 2) + 1

def rawScheduleSteps (rs cs : List ℕ) (U L h : ℕ) : ℕ :=
  rawScheduleGapCount rs cs U *
    (h + 2 + 2 * rawScheduleDimension rs cs * Nat.clog 2 (rawScheduleBase rs cs U L))

def rawScheduleStepPrecision (rs cs : List ℕ) (U L h : ℕ) : ℕ :=
  h + 2 + Nat.clog 2 (rawScheduleSteps rs cs U L h)

/-- The scalar star-exit choices are repeated as natural arithmetic because
their semantic declarations live in a noncomputable section. -/
def rawScheduleExitAttempts (d t : ℕ) : ℕ :=
  (2 * 2^(Nat.clog 2 (32*d^2))) * (t+2)

def rawScheduleExitPrecision (d t : ℕ) : ℕ :=
  t + 2 + Nat.clog 2 (rawScheduleExitAttempts d t)

def rawUniformStepWidth (rs cs : List ℕ) (U L N hIn J hExit : ℕ) : ℕ :=
  N * Nat.clog 2 (rawScheduleClockDenominator rs cs U) +
    rawUniformCompletionBits rs cs U L hIn +
    J * (Nat.clog 2 (32 * (rawScheduleDimension rs cs)^2) +
      rawUniformCompletionBits rs cs U L hExit)

def rawTerminalScheduleWordWidth (rs cs : List ℕ) (U L h : ℕ) : ℕ :=
  let t := rawScheduleStepPrecision rs cs U L h
  let d := rawScheduleDimension rs cs
  rawScheduleSteps rs cs U L h *
    rawUniformStepWidth rs cs U L (t+2) (t+2)
      (rawScheduleExitAttempts d t) (rawScheduleExitPrecision d t) +
    rawUniformCompletionBits rs cs U L (h+2)

def rawScheduleOuterBlock (rs cs : List ℕ) (U : ℕ) : ℕ :=
  let p := rawScheduleSmallCount rs cs U
  min (2 * (p * (p-1))) (4*p)

def rawPositiveOuterAttempts (xs ys : List ℕ) (t : ℕ) : ℕ :=
  rawScheduleOuterBlock (positiveMargins xs) (positiveMargins ys)
    (positiveTraceCutoff xs ys) * (t+1)

def rawPositiveOuterPrecision (xs ys : List ℕ) (t : ℕ) : ℕ :=
  t + 2 + Nat.clog 2 (rawPositiveOuterAttempts xs ys t)

def rawPositiveTrialWordWidth (xs ys : List ℕ) (t : ℕ) : ℕ :=
  let k := rawPositiveOuterPrecision xs ys t
  rawTerminalScheduleWordWidth (positiveMargins xs) (positiveMargins ys)
    (positiveTraceCutoff xs ys) 7 k + k

def rawPositiveWordWidth (xs ys : List ℕ) (t : ℕ) : ℕ :=
  rawPositiveOuterAttempts xs ys t * rawPositiveTrialWordWidth xs ys t

open scoped Classical
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)

lemma rawScheduleDimension_eq :
    rawScheduleDimension (List.ofFn r) (List.ofFn c) =
      dimensionAllowance (I := Fin m) (J := Fin n) := by
  simp only [rawScheduleDimension, marginDimension, List.length_ofFn,
    dimensionAllowance, Fintype.card_fin]

lemma rawScheduleSmallCount_eq :
    rawScheduleSmallCount (List.ofFn r) (List.ofFn c) U =
      Fintype.card (Cells (firstPaperSmall r c U)) := by
  exact (Fintype.card_fin _).symm.trans
    (Fintype.card_congr (Math115.PhysicalComputedProposal.computedCellEquiv r c U))

lemma rawScheduleSmallLines_eq :
    rawScheduleSmallLines (List.ofFn r) U = smallLineCount r U := by
  simp only [rawScheduleSmallLines, List.map_ofFn, List.sum_ofFn, smallLineCount,
    Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter, Function.comp_apply]

lemma rawScheduleLargeLines_row_eq :
    rawScheduleLargeLines (List.ofFn r) U = largeRowCount r U := by
  simp only [rawScheduleLargeLines, List.map_ofFn, List.sum_ofFn, largeRowCount, Function.comp_apply]

lemma rawScheduleLargeLines_column_eq :
    rawScheduleLargeLines (List.ofFn c) U = largeColumnCount c U := by
  simp only [rawScheduleLargeLines, List.map_ofFn, List.sum_ofFn, largeColumnCount, Function.comp_apply]

theorem rawUniformCompletionBits_eq (h : ℕ) :
    rawUniformCompletionBits (List.ofFn r) (List.ofFn c) U L h =
      uniformCompletionBits r c U L h := by
  simp only [rawUniformCompletionBits, rawScheduleResidualMass,
    rawScheduleDimension_eq, rawScheduleLargeLines_row_eq r U,
    rawScheduleLargeLines_column_eq c U, List.sum_ofFn,
    uniformCompletionBits, residualMassBound]

theorem rawScheduleClockDenominator_eq :
    rawScheduleClockDenominator (List.ofFn r) (List.ofFn c) U =
      Math115.RationalClockProposal.denominator r c U := by
  simp only [rawScheduleClockDenominator, rawScheduleSmallCount_eq,
    Math115.RationalClockProposal.denominator, defectAllowance]

lemma rawScheduleGapCount_eq :
    rawScheduleGapCount (List.ofFn r) (List.ofFn c) U = terminalGapCount r c U := by
  simp only [rawScheduleGapCount, rawScheduleSmallCount_eq, rawScheduleSmallLines_eq,
    terminalGapCount, terminalAggregateCount]

lemma rawScheduleBase_eq :
    rawScheduleBase (List.ofFn r) (List.ofFn c) U L = terminalScheduleBase (n := n) r U L := by
  simp only [rawScheduleBase, rawScheduleDimension_eq, List.sum_ofFn,
    terminalScheduleBase, Math115.PhysicalFiniteWalk.capacityBound]

theorem rawScheduleSteps_eq (h : ℕ) :
    rawScheduleSteps (List.ofFn r) (List.ofFn c) U L h = terminalScheduleSteps r c U L h := by
  simp only [rawScheduleSteps, rawScheduleGapCount_eq, rawScheduleDimension_eq,
    rawScheduleBase_eq, terminalScheduleSteps, terminalScheduleExponent]

lemma rawScheduleStepPrecision_eq (h : ℕ) :
    rawScheduleStepPrecision (List.ofFn r) (List.ofFn c) U L h =
      terminalScheduleStepPrecision r c U L h := by
  simp only [rawScheduleStepPrecision, rawScheduleSteps_eq, terminalScheduleStepPrecision]

lemma rawScheduleExitAttempts_eq (d t : ℕ) :
    rawScheduleExitAttempts d t = Math115.PhysicalStarBudget.attempts d t := rfl

lemma rawScheduleExitPrecision_eq (d t : ℕ) :
    rawScheduleExitPrecision d t = Math115.PhysicalStarBudget.precision d t := rfl

theorem rawUniformStepWidth_eq (N hIn J hExit : ℕ) :
    rawUniformStepWidth (List.ofFn r) (List.ofFn c) U L N hIn J hExit =
      uniformStepWidth r c U L N hIn J hExit := by
  simp only [rawUniformStepWidth, rawScheduleClockDenominator_eq,
    rawUniformCompletionBits_eq, rawScheduleDimension_eq,
    uniformStepWidth, commonExitWidth, Math115.RationalClockProposal.precision]

theorem rawTerminalScheduleWordWidth_eq (h : ℕ) :
    rawTerminalScheduleWordWidth (List.ofFn r) (List.ofFn c) U L h =
      terminalScheduleWordWidth r c U L h := by
  simp only [rawTerminalScheduleWordWidth, rawScheduleStepPrecision_eq,
    rawScheduleDimension_eq, rawScheduleSteps_eq, rawUniformStepWidth_eq,
    rawScheduleExitAttempts_eq, rawScheduleExitPrecision_eq,
    rawUniformCompletionBits_eq, terminalScheduleWordWidth, terminalBankWidth,
    terminalScheduleTerminalPrecision]

variable (xs ys : List ℕ)

lemma rawPositiveSmallCount_eq :
    rawScheduleSmallCount (positiveMargins xs) (positiveMargins ys) (positiveTraceCutoff xs ys) =
      Fintype.card (Cells (firstPaperSmall (filteredMargin xs) (filteredMargin ys)
        (positiveTraceCutoff xs ys))) := by
  simpa only [ofFn_filteredMargin] using rawScheduleSmallCount_eq
    (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys)

theorem rawPositiveOuterAttempts_eq (t : ℕ) :
    rawPositiveOuterAttempts xs ys t = positiveTraceLinearAttempts xs ys t := by
  simp only [rawPositiveOuterAttempts, rawScheduleOuterBlock, rawPositiveSmallCount_eq,
    positiveTraceLinearAttempts, positiveTraceLinearBlock, positiveTraceOuterBlock]

theorem rawPositiveOuterPrecision_eq (t : ℕ) :
    rawPositiveOuterPrecision xs ys t = positiveTraceLinearPrecision xs ys t := by
  simp only [rawPositiveOuterPrecision, rawPositiveOuterAttempts_eq, positiveTraceLinearPrecision]

theorem rawPositiveTrialWordWidth_eq (t : ℕ) :
    rawPositiveTrialWordWidth xs ys t =
      terminalCorrectedWordWidth (filteredMargin xs) (filteredMargin ys)
        (positiveTraceCutoff xs ys) 7 (positiveTraceLinearPrecision xs ys t)
        (positiveTraceLinearPrecision xs ys t) := by
  have hw := rawTerminalScheduleWordWidth_eq (filteredMargin xs) (filteredMargin ys)
    (positiveTraceCutoff xs ys) 7 (positiveTraceLinearPrecision xs ys t)
  simp only [ofFn_filteredMargin] at hw
  simp only [rawPositiveTrialWordWidth, rawPositiveOuterPrecision_eq,
    hw, terminalCorrectedWordWidth]

theorem rawPositiveWordWidth_eq (t : ℕ) :
    rawPositiveWordWidth xs ys t = positiveReferenceWordWidth xs ys t := by
  simp only [rawPositiveWordWidth, rawPositiveOuterAttempts_eq, rawPositiveTrialWordWidth_eq,
    positiveReferenceWordWidth, terminalCorrectedRetryWordWidth]

/-- This is the substantive positive-width premise of list chunking. The
correction suffix alone supplies it, independently of internal walk widths. -/
theorem rawPositiveTrialWordWidth_positive (t : ℕ) : 0 < rawPositiveTrialWordWidth xs ys t := by
  change 0 < rawTerminalScheduleWordWidth (positiveMargins xs) (positiveMargins ys)
    (positiveTraceCutoff xs ys) 7 (rawPositiveOuterPrecision xs ys t) + rawPositiveOuterPrecision xs ys t
  have hk : 0 < rawPositiveOuterPrecision xs ys t := by
    unfold rawPositiveOuterPrecision
    omega
  omega

end
end Math115.PhysicalTraceJoin
