/-
SPDX-License-Identifier: Apache-2.0
An explicit natural accuracy schedule for the literal defect-joint draw.
The schedule pays for trace mixing, accumulated step error, and one fresh
terminal completion. Its target remains the defect-labelled joint space.
No initialization, table correction or machine-time bound is supplied.
-/
import ResearchPhysicalTraceJoin.Terminal
import Math115.CompletionScheduleArithmetic

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open FirstSuccess ResidualMixture
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.AggregateDefectTrace Math115.CompletionRetryBudget
open Math115.CompletionOuterSchedule Research.ResidualSelectedBudget
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

local notation "dimension" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "p" => Fintype.card (Cells (firstPaperSmall r c U))

/-- A natural representative of the existing aggregate correction budget. -/
def terminalAggregateCount : ℕ :=
  U * (U - 1) + 4 * ((smallLineCount r U + smallLineCount c U) * U^2 + p * U)

def terminalGapCount : ℕ := 32 * p^3 * terminalAggregateCount r c U

theorem terminalGapCount_cast (hU : 2 ≤ U) :
    (terminalGapCount r c U : ℝ) = aggregateMixingAllowance r c U := by
  have hU1 : 1 ≤ U := by omega
  simp only [terminalGapCount, terminalAggregateCount, aggregateMixingAllowance,
    aggregateCT, aggregateK0, Nat.cast_mul, Nat.cast_add, Nat.cast_pow,
    Nat.cast_sub hU1, Nat.cast_one, Nat.cast_ofNat]

lemma terminalGapCount_positive (hU : 2 ≤ U) (hp : 2 ≤ p) :
    0 < terminalGapCount r c U := by
  have hpos : (0 : ℝ) < (terminalGapCount r c U : ℝ) := by
    rw [terminalGapCount_cast r c U hU]
    exact lt_of_lt_of_le (by norm_num) (aggregateMixingAllowance_at_least_one r c U hU hp)
  exact_mod_cast hpos

def terminalScheduleBase : ℕ := Math115.PhysicalFiniteWalk.capacityBound (J := Fin n) r U L + 1

def terminalScheduleExponent (h : ℕ) : ℕ :=
  h + 2 + 2 * dimension * Nat.clog 2 (terminalScheduleBase (n := n) r U L)

def terminalScheduleSteps (h : ℕ) : ℕ :=
  terminalGapCount r c U * terminalScheduleExponent (n := n) r U L h

/-- This is the target t for the existing per-step local schedule; its
incoming clock/completion settings are then t+2 as before. -/
def terminalScheduleStepPrecision (h : ℕ) : ℕ :=
  h + 2 + Nat.clog 2 (terminalScheduleSteps r c U L h)

def terminalScheduleTerminalPrecision (h : ℕ) : ℕ := h + 2

lemma terminalScheduleSteps_positive (hU : 2 ≤ U) (hp : 2 ≤ p) (h : ℕ) :
    0 < terminalScheduleSteps r c U L h := by
  exact Nat.mul_pos (terminalGapCount_positive r c U hU hp)
    (by unfold terminalScheduleExponent; omega)

/-- The existing natural mass charge pays for the full physical allowance,
which bounds the defect normalizer even with zero original margins. -/
lemma terminalSchedule_mixing_budget (hU : 2 ≤ U) (hp : 2 ≤ p) (h : ℕ) :
    Math115.PhysicalFiniteWalk.massAllowance (J := Fin n) r U L *
      Real.exp (-(terminalScheduleSteps r c U L h : ℝ) / aggregateMixingAllowance r c U) ≤
      (dyadic (h + 2) : ℝ) := by
  have hg : (terminalGapCount r c U : ℝ) ≠ 0 := by
    exact_mod_cast (terminalGapCount_positive r c U hU hp).ne'
  have hratio : -(terminalScheduleSteps r c U L h : ℝ) /
      aggregateMixingAllowance r c U = -(terminalScheduleExponent (n := n) r U L h : ℝ) := by
    rw [← terminalGapCount_cast r c U hU]
    simp only [terminalScheduleSteps, Nat.cast_mul]
    field_simp [hg]
  rw [hratio]
  have hexp := exp_neg_nat_le_dyadic (terminalScheduleExponent (n := n) r U L h)
  have hm := mul_le_mul_of_nonneg_left hexp
    (show (0 : ℝ) ≤ Math115.PhysicalFiniteWalk.massAllowance (J := Fin n) r U L from
      (Math115.PhysicalFiniteWalk.massAllowance_positive r U L).le)
  have hcharge : (terminalScheduleBase (n := n) r U L)^(2 * dimension) ≤
      2^(2 * dimension * Nat.clog 2 (terminalScheduleBase (n := n) r U L)) := by
    simpa using mass_charge_bound 1 (terminalScheduleBase (n := n) r U L) dimension
  have hc := dyadic_charge ((terminalScheduleBase (n := n) r U L)^(2 * dimension))
    (2 * dimension * Nat.clog 2 (terminalScheduleBase (n := n) r U L)) (h + 2) hcharge
  push_cast at hc
  exact hm.trans hc

lemma terminalSchedule_step_budget (h : ℕ) :
    (terminalScheduleSteps r c U L h : ℝ) *
      (dyadic (terminalScheduleStepPrecision r c U L h) : ℝ) ≤
      (dyadic (h + 2) : ℝ) :=
  dyadic_charge (terminalScheduleSteps r c U L h)
    (Nat.clog 2 (terminalScheduleSteps r c U L h)) (h + 2)
    (Nat.le_pow_clog (by decide) _)

/-- Three quarter-target allocations leave a quarter-target safety margin. -/
theorem terminalSchedule_error_budget (hU : 2 ≤ U) (hp : 2 ≤ p) (h : ℕ) :
    (terminalScheduleSteps r c U L h : ℝ) *
        (dyadic (terminalScheduleStepPrecision r c U L h) : ℝ) +
      Math115.PhysicalFiniteWalk.massAllowance (J := Fin n) r U L *
        Real.exp (-(terminalScheduleSteps r c U L h : ℝ) / aggregateMixingAllowance r c U) +
      (dyadic (terminalScheduleTerminalPrecision h) : ℝ) ≤ (dyadic h : ℝ) := by
  have hs := terminalSchedule_step_budget r c U L h
  have hm := terminalSchedule_mixing_budget r c U L hU hp h
  have hfourQ : 4 * dyadic (h + 2) = dyadic h := by
    unfold dyadic
    rw [pow_add]
    norm_num
    ring
  have hfourR : (4 : ℝ) * (dyadic (h + 2) : ℝ) = (dyadic h : ℝ) := by
    exact_mod_cast hfourQ
  have hnonneg : (0 : ℝ) ≤ (dyadic (h + 2) : ℝ) := by
    rw [dyadic_real]
    positivity
  unfold terminalScheduleTerminalPrecision
  linarith only [hs, hm, hfourR, hnonneg]

def terminalScheduleWordWidth (h : ℕ) : ℕ :=
  let t := terminalScheduleStepPrecision r c U L h
  terminalBankWidth r c U L (t + 2) (t + 2)
    (Math115.PhysicalStarBudget.attempts dimension t)
    (Math115.PhysicalStarBudget.precision dimension t)
    (terminalScheduleSteps r c U L h) (terminalScheduleTerminalPrecision h)

def terminalScheduleWord (start : DefectVertices r c U L) (h : ℕ)
    (word : Fin (terminalScheduleWordWidth r c U L h) → Bool) : DefectJoint r c U L :=
  let t := terminalScheduleStepPrecision r c U L h
  terminalJoinedWord r c U L hr hc start (t + 2) (t + 2)
    (Math115.PhysicalStarBudget.attempts dimension t)
    (Math115.PhysicalStarBudget.precision dimension t)
    (terminalScheduleSteps r c U L h) (terminalScheduleTerminalPrecision h) word

/-- Explicit natural choices supply dyadic accuracy for the literal joint
program, without a stationary start or a desired-error hypothesis. -/
theorem terminalScheduleWord_accuracy [Nonempty (DefectVertices r c U L)]
    (htotal : (∑ i, r i) = ∑ j, c j) (hU : 2 ≤ U) (hL : 7 ≤ L) (hp : 2 ≤ p)
    (start : DefectVertices r c U L) (h : ℕ) :
    (variation
      (mapLaw (uniformLaw (α := Fin (terminalScheduleWordWidth r c U L h) → Bool))
        (terminalScheduleWord r c U L hr hc start h))
      (uniformLaw (α := DefectJoint r c U L)) : ℝ) ≤ (dyadic h : ℝ) := by
  exact (scheduledTerminalJoinedWord_accuracy r c U L hr hc htotal hU hL hp start
    (terminalScheduleStepPrecision r c U L h) (terminalScheduleSteps r c U L h)
    (terminalScheduleTerminalPrecision h)).trans
      (terminalSchedule_error_budget r c U L hU hp h)

end
end Math115.PhysicalTraceJoin
