/-
SPDX-License-Identifier: Apache-2.0
A concrete precision and retry schedule for the physical balanced-star exit.
This local schedule is not a global trace walk or a complete sampler budget.
-/
import ResearchPhysicalStarRetry.Exit

set_option maxHeartbeats 800000

namespace Math115.PhysicalStarBudget

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles PhysicalCompletionFibres
open FirstPaperPhysicalMarginal FirstPaperProfiles CompletionCounts
open FirstSuccess ResidualMixture
open Math115.PhysicalRationalKernel Math115.PhysicalDefectTrace
open Math115.PhysicalCompletionOracle Math115.LegacyPhysicalCompletion
open Math115.PhysicalStarRetry Math115.CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section

/-- A finite geometric-sum argument: A trials of success at least 1/A
reduce the remaining mass by at least half. -/
lemma reciprocal_block (A : ℕ) (hA : 0 < A) :
    (1 - 1 / (A : ℚ))^A ≤ 1 / 2 := by
  let q : ℚ := 1 - 1 / (A : ℚ)
  have hAr : (0 : ℚ) < A := by exact_mod_cast hA
  have hAone : (1 : ℚ) ≤ A := by exact_mod_cast (Nat.succ_le_iff.mpr hA)
  have hq0 : 0 ≤ q := by
    dsimp [q]
    exact sub_nonneg.mpr ((div_le_one hAr).mpr hAone)
  have hq1 : q ≤ 1 := by
    dsimp [q]
    have hn : (0 : ℚ) ≤ 1 / (A : ℚ) := div_nonneg (by norm_num) hAr.le
    linarith
  have hs : (A : ℚ) * q^A ≤ ∑ i ∈ Finset.range A, q^i := by
    calc
      _ = ∑ _i ∈ Finset.range A, q^A := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi =>
        pow_le_pow_right_of_le_one₀ hq0 hq1 (Nat.le_of_lt (Finset.mem_range.mp hi)))
  have hg := geometric_balance q A
  have hm := mul_le_mul_of_nonneg_left hs (sub_nonneg.mpr hq1)
  have ha : (1 - q) * (A : ℚ) = 1 := by
    dsimp [q]
    field_simp
  have hm' : q^A ≤ (1 - q) * ∑ i ∈ Finset.range A, q^i := by
    simpa only [← mul_assoc, ha, one_mul] using hm
  change q^A ≤ 1 / 2
  nlinarith

def blockSize (d : ℕ) : ℕ := 2 * 2^(Nat.clog 2 (32*d^2))

def attempts (d t : ℕ) : ℕ := blockSize d * (t + 2)

def precision (d t : ℕ) : ℕ := t + 2 + Nat.clog 2 (attempts d t)

lemma blockSize_positive (d : ℕ) : 0 < blockSize d := by
  unfold blockSize
  positivity

lemma attempts_positive (d t : ℕ) : 0 < attempts d t := by
  unfold attempts
  exact Nat.mul_pos (blockSize_positive d) (by omega)

lemma half_proposal_eq (d : ℕ) : proposalRat d / 2 = 1 / (blockSize d : ℚ) := by
  unfold proposalRat blockSize
  push_cast
  ring

theorem exit_failure_budget (d t : ℕ) :
    (1 - proposalRat d / 2)^(attempts d t) ≤ dyadic (t + 2) := by
  rw [half_proposal_eq]
  unfold attempts
  rw [pow_mul]
  have hA := blockSize_positive d
  have hAr : (0 : ℚ) < blockSize d := by exact_mod_cast hA
  have hAone : (1 : ℚ) ≤ blockSize d := by exact_mod_cast (Nat.succ_le_iff.mpr hA)
  have hq : 0 ≤ 1 - 1 / (blockSize d : ℚ) :=
    sub_nonneg.mpr ((div_le_one hAr).mpr hAone)
  calc
    _ ≤ (1 / 2 : ℚ)^(t + 2) := pow_le_pow_left₀ (pow_nonneg hq _)
      (reciprocal_block (blockSize d) hA) _
    _ = dyadic (t + 2) := by simp [dyadic, div_pow]

theorem exit_draw_budget (d t : ℕ) :
    (attempts d t : ℚ) * dyadic (precision d t) ≤ dyadic (t + 2) := by
  have hclog : (attempts d t : ℚ) ≤ (2 : ℚ)^Nat.clog 2 (attempts d t) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (attempts d t)
  calc
    _ ≤ (2 : ℚ)^Nat.clog 2 (attempts d t) * dyadic (precision d t) :=
      mul_le_mul_of_nonneg_right hclog (dyadic_positive _).le
    _ = dyadic (t + 2) := by
      unfold dyadic precision
      rw [pow_add]
      field_simp

theorem exit_budget (d t : ℕ) :
    (1 - proposalRat d / 2)^(attempts d t) +
      (attempts d t : ℚ) * dyadic (precision d t) ≤ dyadic (t + 1) := by
  have hf := exit_failure_budget d t
  have hd := exit_draw_budget d t
  have he := dyadic_succ (t + 1)
  linarith

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => Nat.clog 2 (32*d^2)

/-- A concrete local schedule, with an exact fair-bit bank and half the
requested accuracy allowance reserved for other errors. -/
theorem scheduledExit_variation (htotal : (∑ i, r i) = ∑ j, c j)
    (hL : 7 ≤ L) (b : BalancedVertices r c U L)
    (entering : DefectVertices r c U L)
    (hbe : physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L)
      b.val entering.val) (t : ℕ) :
    variation
      (mapLaw (uniformLaw (α := Fin (attempts d t *
        (s + bits r c U L hr hc b.val (precision d t))) → Bool))
        (flatExit r c U L hr hc b (precision d t) entering (attempts d t)))
      (targetLaw r c U L hr hc b (starMass_pos_of_edge r c U L hr hc hL b entering hbe))
      ≤ dyadic (t + 1) :=
  (flatExit_variation_of_edge r c U L hr hc htotal hL b (precision d t)
    entering hbe (attempts d t)).trans (exit_budget d t)

end
end Math115.PhysicalStarBudget
