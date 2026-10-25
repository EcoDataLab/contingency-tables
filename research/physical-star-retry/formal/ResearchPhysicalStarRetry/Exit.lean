/-
SPDX-License-Identifier: Apache-2.0
Bounded physical balanced-star exits from the checked fixed-state trial.
The proposal rate here is the old dyadic rate, which cancels in the target
exit law. This does not identify the incoming canonical trace clock.
-/
import ResearchPhysicalStar.Trial
import ResearchWeightedExit.FirstSuccess

set_option maxHeartbeats 800000

namespace Math115.PhysicalStarRetry

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles CompletionTranslation
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open CompletionCounts PaddedCompletions FirstSuccess ResidualMixture
open Math115.ReducedSmallChain Math115.PhysicalCompletionOracle
open Math115.PhysicalRationalKernel Math115.PhysicalDefectTrace
open Math115.ComputedReferenceTrace Math115.LegacyPhysicalCompletion
open Math115.PhysicalStarTrial Math115.WeightedExit
open Math115.CompletionRetryBudget Math115.CompletionBooleanRetry
open Research.ConstantPaddingAcceptance
open scoped BigOperators Classical

noncomputable section

lemma successMass_id {D : Type*} [Fintype D] [DecidableEq D]
    (q : RationalLaw (Option D)) (e : D) : successMass q id e = q.mass (some e) := by
  simp [successMass, Fintype.sum_option]

lemma retry_point_none {D : Type*} [Fintype D] [DecidableEq D]
    (fallback : D) (J : ℕ) :
    retryLaw (pointLaw (none : Option D)) id fallback J = pointLaw fallback := by
  apply RationalLaw.ext
  funext e
  rw [retryLaw_mass]
  simp [successMass, failureMass, pointLaw, Fintype.sum_option, outputMass]

lemma retry_variation_from_hold {D : Type*} [Fintype D] [DecidableEq D]
    (p q : RationalLaw (Option D)) (hq : q = pointLaw none)
    (fallback : D) (J : ℕ) (δ : ℚ) (hδ : variation p q ≤ δ) :
    variation (retryLaw p id fallback J) (pointLaw fallback) ≤ (J : ℚ) * δ := by
  have he := retryLaw_variation p q id fallback J
  rw [hq, retry_point_none] at he
  rw [hq] at hδ
  exact he.trans (mul_le_mul_of_nonneg_left hδ (by positivity))

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => Nat.clog 2 (32 * d^2)
local notation "B" => capacity r c U L
local notation "i₀" => largeOptionEquiv r U hr none
local notation "j₀" => largeOptionEquiv c U hc none

lemma crossRat_nonnegative (b : BalancedVertices r c U L)
    (e : DefectVertices r c U L) : 0 ≤ crossRat r c U L hr hc b e := by
  unfold crossRat
  split_ifs <;> positivity

lemma weightRat_pos (b : BalancedVertices r c U L) :
    0 < weightRat r c U L hr hc b := by
  have hw : (0 : ℝ) < (weightRat r c U L hr hc b : ℝ) := by
    rw [weightRat_cast]
    exact weight_positive r c U L b.val
  exact_mod_cast hw

def starMass (b : BalancedVertices r c U L) : ℚ := ∑ e, crossRat r c U L hr hc b e

def successProbability (b : BalancedVertices r c U L) : ℚ :=
  proposalRat d * starMass r c U L hr hc b / weightRat r c U L hr hc b

lemma starMass_nonnegative (b : BalancedVertices r c U L) :
    0 ≤ starMass r c U L hr hc b :=
  Finset.sum_nonneg (fun e _ => crossRat_nonnegative r c U L hr hc b e)

lemma starMass_cast (b : BalancedVertices r c U L) :
    (starMass r c U L hr hc b : ℝ) = ∑ e, referenceCross r c U L i₀ j₀ b e := by
  simp only [starMass, Rat.cast_sum, crossRat_cast]

def targetLaw (b : BalancedVertices r c U L) (hstar : 0 < starMass r c U L hr hc b) :
    RationalLaw (DefectVertices r c U L) :=
  starLaw (crossRat r c U L hr hc b) (crossRat_nonnegative r c U L hr hc b) hstar

theorem targetLaw_mass_cast (b : BalancedVertices r c U L)
    (hstar : 0 < starMass r c U L hr hc b) (e : DefectVertices r c U L) :
    ((targetLaw r c U L hr hc b hstar).mass e : ℝ) =
      referenceCross r c U L i₀ j₀ b e / (∑ f, referenceCross r c U L i₀ j₀ b f) := by
  change ((crossRat r c U L hr hc b e / starMass r c U L hr hc b : ℚ) : ℝ) = _
  simp only [Rat.cast_div, crossRat_cast, starMass_cast]

lemma ideal_successMass (b : BalancedVertices r c U L) (e : DefectVertices r c U L) :
    successMass (idealTrialLaw r c U L hr hc b) id e =
      proposalRat d * crossRat r c U L hr hc b e / weightRat r c U L hr hc b := by
  rw [successMass_id, idealTrialLaw_mass_some]

lemma ideal_success_total (b : BalancedVertices r c U L) :
    (∑ e, (idealTrialLaw r c U L hr hc b).mass (some e)) =
      successProbability r c U L hr hc b := by
  simp_rw [idealTrialLaw_mass_some]
  rw [← Finset.sum_div, ← Finset.mul_sum]
  rfl

lemma ideal_failureMass (b : BalancedVertices r c U L) :
    failureMass (idealTrialLaw r c U L hr hc b) id =
      1 - successProbability r c U L hr hc b := by
  have ht := success_failure_total (idealTrialLaw r c U L hr hc b) id
  simp_rw [successMass_id] at ht
  rw [ideal_success_total] at ht
  linarith

/-- Normalization supplies the probability bounds even for a zero star. -/
lemma successProbability_bounds (b : BalancedVertices r c U L) :
    0 ≤ successProbability r c U L hr hc b ∧ successProbability r c U L hr hc b ≤ 1 := by
  constructor
  · rw [← ideal_success_total]
    exact Finset.sum_nonneg (fun e _ => (idealTrialLaw r c U L hr hc b).nonnegative (some e))
  · have hf : 0 ≤ failureMass (idealTrialLaw r c U L hr hc b) id := by
      simpa [failureMass] using (idealTrialLaw r c U L hr hc b).nonnegative none
    rw [ideal_failureMass] at hf
    linarith

/-- Returning the entering defect, if accepted, is a successful trial. -/
def flatExit (b : BalancedVertices r c U L) (h : ℕ)
    (fallback : DefectVertices r c U L) (J : ℕ)
    (word : Fin (J * (s + bits r c U L hr hc b.val h)) → Bool) : DefectVertices r c U L :=
  flatRetry (actualTrial r c U L hr hc b h) fallback J word

theorem flatExit_law (b : BalancedVertices r c U L) (h : ℕ)
    (fallback : DefectVertices r c U L) (J : ℕ) :
    mapLaw (uniformLaw (α := Fin (J * (s + bits r c U L hr hc b.val h)) → Bool))
      (flatExit r c U L hr hc b h fallback J) =
    retryLaw (actualTrialLaw r c U L hr hc b h) id fallback J :=
  flatRetry_law (actualTrial r c U L hr hc b h) id fallback J

theorem idealExit_mass (b : BalancedVertices r c U L)
    (hstar : 0 < starMass r c U L hr hc b)
    (fallback e : DefectVertices r c U L) (J : ℕ) :
    (retryLaw (idealTrialLaw r c U L hr hc b) id fallback J).mass e =
      (1 - (1 - successProbability r c U L hr hc b)^J) *
        (targetLaw r c U L hr hc b hstar).mass e +
      if e = fallback then (1 - successProbability r c U L hr hc b)^J else 0 := by
  have he := star_retry_mass (idealTrialLaw r c U L hr hc b) id
    (crossRat r c U L hr hc b) (crossRat_nonnegative r c U L hr hc b) hstar
    (proposalRat d) (weightRat r c U L hr hc b) (weightRat_pos r c U L hr hc b)
    (ideal_successMass r c U L hr hc b) fallback e J
  by_cases hef : e = fallback
  · simpa only [successProbability, starMass, targetLaw, starLaw, ite_eq_left hef] using he
  · simpa only [successProbability, starMass, targetLaw, starLaw, ite_eq_right hef] using he

/-- Exactly J*(s+q_b(h)) fresh fair bits implement this capped physical exit.
The symbolic target weights are used only in the comparison law. -/
theorem flatExit_variation (htotal : (∑ i, r i) = ∑ j, c j)
    (b : BalancedVertices r c U L) (h : ℕ)
    (hstar : 0 < starMass r c U L hr hc b)
    (fallback : DefectVertices r c U L) (J : ℕ) :
    variation
      (mapLaw (uniformLaw (α := Fin (J * (s + bits r c U L hr hc b.val h)) → Bool))
        (flatExit r c U L hr hc b h fallback J))
      (targetLaw r c U L hr hc b hstar) ≤
      (1 - successProbability r c U L hr hc b)^J + (J : ℚ) * dyadic h :=
  flat_star_retry_variation (actualTrial r c U L hr hc b h) id
    (idealTrialLaw r c U L hr hc b)
    (crossRat r c U L hr hc b) (crossRat_nonnegative r c U L hr hc b) hstar
    (proposalRat d) (weightRat r c U L hr hc b) (weightRat_pos r c U L hr hc b)
    (ideal_successMass r c U L hr hc b) fallback J (dyadic h)
    (actualTrialLaw_accuracy r c U L hr hc htotal b h)

/-- Padding seven bounds the count from the balanced source itself. -/
lemma crossRat_ge_half_weight (hL : 7 ≤ L) (b : BalancedVertices r c U L)
    (entering : DefectVertices r c U L)
    (hbe : physicalAdjacent r c U L B (capacity_small r c U L) b.val entering.val) :
    weightRat r c U L hr hc b / 2 ≤ crossRat r c U L hr hc b entering := by
  have ha := reference_edge_acceptance_seven r c U L B (capacity_small r c U L)
    i₀ j₀ hL (physical_paper_capacity _ r c _ L U dimension_le_allowance) b.val entering.val hbe
  have ha' : (weightRat r c U L hr hc b : ℝ) / 2 ≤
      (crossRat r c U L hr hc b entering : ℝ) := by
    simpa only [weightRat, crossRat, if_pos hbe, Rat.cast_natCast] using ha
  exact_mod_cast ha'

theorem starMass_ge_half_weight (hL : 7 ≤ L) (b : BalancedVertices r c U L)
    (entering : DefectVertices r c U L)
    (hbe : physicalAdjacent r c U L B (capacity_small r c U L) b.val entering.val) :
    weightRat r c U L hr hc b / 2 ≤ starMass r c U L hr hc b := by
  exact (crossRat_ge_half_weight r c U L hr hc hL b entering hbe).trans
    (Finset.single_le_sum (fun e _ => crossRat_nonnegative r c U L hr hc b e)
      (Finset.mem_univ entering))

theorem starMass_pos_of_edge (hL : 7 ≤ L) (b : BalancedVertices r c U L)
    (entering : DefectVertices r c U L)
    (hbe : physicalAdjacent r c U L B (capacity_small r c U L) b.val entering.val) :
    0 < starMass r c U L hr hc b := by
  have hw := weightRat_pos r c U L hr hc b
  have hs := starMass_ge_half_weight r c U L hr hc hL b entering hbe
  linarith

theorem successProbability_ge_half_proposal (hL : 7 ≤ L) (b : BalancedVertices r c U L)
    (entering : DefectVertices r c U L)
    (hbe : physicalAdjacent r c U L B (capacity_small r c U L) b.val entering.val) :
    proposalRat d / 2 ≤ successProbability r c U L hr hc b := by
  unfold successProbability
  apply (le_div_iff₀ (weightRat_pos r c U L hr hc b)).2
  have hs := starMass_ge_half_weight r c U L hr hc hL b entering hbe
  nlinarith [mul_le_mul_of_nonneg_left hs (proposalRat_nonnegative d)]

/-- The actual entering edge discharges positive-star and success hypotheses. -/
theorem flatExit_variation_of_edge (htotal : (∑ i, r i) = ∑ j, c j)
    (hL : 7 ≤ L) (b : BalancedVertices r c U L) (h : ℕ)
    (entering : DefectVertices r c U L)
    (hbe : physicalAdjacent r c U L B (capacity_small r c U L) b.val entering.val) (J : ℕ) :
    variation
      (mapLaw (uniformLaw (α := Fin (J * (s + bits r c U L hr hc b.val h)) → Bool))
        (flatExit r c U L hr hc b h entering J))
      (targetLaw r c U L hr hc b (starMass_pos_of_edge r c U L hr hc hL b entering hbe)) ≤
      (1 - proposalRat d / 2)^J + (J : ℚ) * dyadic h := by
  have he := flatExit_variation r c U L hr hc htotal b h
    (starMass_pos_of_edge r c U L hr hc hL b entering hbe) entering J
  have hs := successProbability_ge_half_proposal r c U L hr hc hL b entering hbe
  have ha := (successProbability_bounds r c U L hr hc b).2
  exact he.trans (add_le_add
    (pow_le_pow_left₀ (sub_nonneg.mpr ha) (by linarith) J) le_rfl)

/-- A zero star gives an ideal hold. No pointwise assertion about the actual
approximate draw is inferred from this ideal mass calculation. -/
theorem idealTrialLaw_zero_star (b : BalancedVertices r c U L)
    (hzero : starMass r c U L hr hc b = 0) :
    idealTrialLaw r c U L hr hc b = pointLaw none := by
  have hs (e : DefectVertices r c U L) : (idealTrialLaw r c U L hr hc b).mass (some e) = 0 := by
    have hle : crossRat r c U L hr hc b e ≤ starMass r c U L hr hc b :=
      Finset.single_le_sum (fun f _ => crossRat_nonnegative r c U L hr hc b f)
        (Finset.mem_univ e)
    have hz : crossRat r c U L hr hc b e = 0 :=
      le_antisymm (by simpa only [hzero] using hle) (crossRat_nonnegative r c U L hr hc b e)
    rw [idealTrialLaw_mass_some, hz, mul_zero, zero_div]
  apply RationalLaw.ext
  funext e
  cases e with
  | none =>
      have ht := (idealTrialLaw r c U L hr hc b).total
      rw [Fintype.sum_option] at ht
      simp_rw [hs] at ht
      simpa [pointLaw] using ht
  | some e => simpa [pointLaw] using hs e

theorem flatExit_zero_star_variation (htotal : (∑ i, r i) = ∑ j, c j)
    (b : BalancedVertices r c U L) (h : ℕ) (hzero : starMass r c U L hr hc b = 0)
    (fallback : DefectVertices r c U L) (J : ℕ) :
    variation
      (mapLaw (uniformLaw (α := Fin (J * (s + bits r c U L hr hc b.val h)) → Bool))
        (flatExit r c U L hr hc b h fallback J))
      (pointLaw fallback) ≤ (J : ℚ) * dyadic h := by
  have he := retry_variation_from_hold
    (actualTrialLaw r c U L hr hc b h) (idealTrialLaw r c U L hr hc b)
    (idealTrialLaw_zero_star r c U L hr hc b hzero) fallback J (dyadic h)
    (actualTrialLaw_accuracy r c U L hr hc htotal b h)
  exact (congrArg (fun p => variation p (pointLaw fallback))
    (flatExit_law r c U L hr hc b h fallback J)).le.trans he

end
end Math115.PhysicalStarRetry
