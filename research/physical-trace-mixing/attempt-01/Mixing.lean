/-
SPDX-License-Identifier: Apache-2.0
Mixing to the completion-count stationary law on defects, from a supplied
defect and a literal bounded fair-word walk. No terminal table draw, output
correction, whole-sampler restart or encoded-machine cost is asserted.
-/
import ResearchPhysicalTraceJoin.Walk
import Math115.PhysicalFiniteWalk

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open FirstSuccess ResidualMixture
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalStationaryLaw Math115.ComputedReferenceTrace
open Math115.AggregateDefectTrace Math115.CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

local notation "dimension" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "p" => Fintype.card (Cells (firstPaperSmall r c U))

def defectStationaryRat (d : DefectVertices r c U L) : ℚ :=
  (Fintype.card (Fibre r c U L d.val) : ℚ) /
    (∑ e : DefectVertices r c U L, (Fintype.card (Fibre r c U L e.val) : ℚ))

/-- Normalize only over defect fibres, not all physical states. -/
def defectStationaryLaw [Nonempty (DefectVertices r c U L)] :
    RationalLaw (DefectVertices r c U L) where
  mass := defectStationaryRat r c U L
  nonnegative := fun d => div_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _))
  total := by
    have hcard (d : DefectVertices r c U L) :
        (0 : ℚ) < Fintype.card (Fibre r c U L d.val) := by
      exact_mod_cast (Fintype.card_pos (α := Fibre r c U L d.val))
    have hs : (0 : ℚ) < ∑ d : DefectVertices r c U L,
        (Fintype.card (Fibre r c U L d.val) : ℚ) :=
      Finset.sum_pos (fun d _ => hcard d) Finset.univ_nonempty
    simp only [defectStationaryRat, ← Finset.sum_div]
    exact div_self (ne_of_gt hs)

lemma defectStationaryRat_cast [Nonempty (DefectVertices r c U L)]
    (hp : 2 ≤ p) (d : DefectVertices r c U L) :
    (defectStationaryRat r c U L d : ℝ) =
      (computedReferenceTrace r c U L hr hc hp).π d := by
  rw [computedReferenceTrace_pi]
  simp only [defectStationaryRat, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast,
    fibre_card_weight, defectWeight]

lemma defectStationaryLaw_cast [Nonempty (DefectVertices r c U L)]
    (hp : 2 ≤ p) (d : DefectVertices r c U L) :
    ((defectStationaryLaw r c U L).mass d : ℝ) =
      (computedReferenceTrace r c U L hr hc hp).π d :=
  defectStationaryRat_cast r c U L hr hc hp d

def defectTotalMass : ℝ := ∑ d : DefectVertices r c U L, defectWeight r c U L d

lemma defectTotalMass_le_full :
    defectTotalMass r c U L ≤ ∑ x : States r c U L, weight r c U L x := by
  have he := (partitionEquiv r c U L).sum_comp (weight r c U L)
  rw [Fintype.sum_sum_type] at he
  change (∑ b : BalancedVertices r c U L, balancedWeight r c U L b) +
    (∑ d : DefectVertices r c U L, defectWeight r c U L d) =
    (∑ x : States r c U L, weight r c U L x) at he
  have hb : 0 ≤ ∑ b : BalancedVertices r c U L, balancedWeight r c U L b :=
    Finset.sum_nonneg (fun b _ => (weight_positive r c U L b.val).le)
  unfold defectTotalMass
  linarith

lemma defectTotalMass_le_allowance :
    defectTotalMass r c U L ≤ Math115.PhysicalFiniteWalk.massAllowance (J := Fin n) r U L :=
  (defectTotalMass_le_full r c U L).trans (Math115.PhysicalFiniteWalk.total_mass_le r c U L)

lemma computedTrace_pi_lower [Nonempty (DefectVertices r c U L)]
    (hp : 2 ≤ p) (d : DefectVertices r c U L) :
    1 / Math115.PhysicalFiniteWalk.massAllowance (J := Fin n) r U L ≤
      (computedReferenceTrace r c U L hr hc hp).π d := by
  have hZ : 0 < defectTotalMass r c U L :=
    Finset.sum_pos (fun d _ => weight_positive r c U L d.val) Finset.univ_nonempty
  rw [computedReferenceTrace_pi]
  exact (one_div_le_one_div_of_le hZ (defectTotalMass_le_allowance r c U L)).trans
    (div_le_div_of_nonneg_right (Math115.PhysicalFiniteWalk.weight_at_least_one r c U L d.val) hZ.le)

def aggregateMixingAllowance : ℝ := 32 * (p : ℝ)^3 * aggregateCT r c U

lemma aggregateMixingAllowance_at_least_one (hU : 2 ≤ U) (hp : 2 ≤ p) :
    1 ≤ aggregateMixingAllowance r c U := by
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hp)
  have hp3 : (1 : ℝ) ≤ (p : ℝ)^3 := one_le_pow₀ hpR
  have hC := aggregateCT_at_least_six r c U hU hp
  unfold aggregateMixingAllowance
  calc
    1 ≤ 32 * (p : ℝ)^3 * 6 := by nlinarith [hp3]
    _ ≤ _ := mul_le_mul_of_nonneg_left hC (by positivity)

/-- The existing aggregate Poincare theorem supplies the actual computed
trace mixing coefficient; it is not assumed as a new kernel premise. -/
theorem idealJoinedWalk_mixing [Nonempty (DefectVertices r c U L)]
    (htotal : (∑ i, r i) = ∑ j, c j) (hU : 2 ≤ U) (hL : 7 ≤ L) (hp : 2 ≤ p)
    (start : DefectVertices r c U L) (T : ℕ) :
    (variation (walkLaw (idealJoinedLaw r c U L hr hc hp) start T)
      (defectStationaryLaw r c U L) : ℝ) ≤
      Math115.PhysicalFiniteWalk.massAllowance (J := Fin n) r U L *
        Real.exp (-(T : ℝ) / aggregateMixingAllowance r c U) := by
  let C := computedReferenceTrace r c U L hr hc hp
  let B := Math115.PhysicalFiniteWalk.massAllowance (J := Fin n) r U L
  have hB : 0 < B := Math115.PhysicalFiniteWalk.massAllowance_positive r U L
  apply rationalWalk_variation (idealJoinedLaw r c U L hr hc hp) C
    (fun d e => idealJoinedLaw_row r c U L hr hc htotal hp d e)
    (defectStationaryLaw r c U L) (defectStationaryLaw_cast r c U L hr hc hp)
    start T _ (by positivity)
  intro y
  have hm := C.point_mixing_exp (aggregateMixingAllowance r c U) (1 / B)
    (aggregateMixingAllowance_at_least_one r c U hU hp) (by positivity)
    (computedTrace_pi_lower r c U L hr hc hp)
    (fun H => computedReferenceTrace_poincare_aggregate r c U L hr hc hU hL hp H)
    T start y
  simpa only [one_div, div_eq_mul_inv, one_mul, inv_inv, mul_comm, B] using hm

/-- Literal fair-word walk plus proved ideal-trace mixing. The target is
the completion-weighted stationary distribution on defects, not tables. -/
theorem scheduledJoinedWalkWord_mixing [Nonempty (DefectVertices r c U L)]
    (htotal : (∑ i, r i) = ∑ j, c j) (hU : 2 ≤ U) (hL : 7 ≤ L) (hp : 2 ≤ p)
    (start : DefectVertices r c U L) (t T : ℕ) :
    (variation
      (mapLaw (uniformLaw (α := Fin
        (T * uniformStepWidth r c U L (t + 2) (t + 2)
          (Math115.PhysicalStarBudget.attempts dimension t)
          (Math115.PhysicalStarBudget.precision dimension t)) → Bool))
        (joinedWalkWord r c U L hr hc start (t + 2) (t + 2)
          (Math115.PhysicalStarBudget.attempts dimension t)
          (Math115.PhysicalStarBudget.precision dimension t) T))
      (defectStationaryLaw r c U L) : ℝ) ≤
      (T : ℝ) * (dyadic t : ℝ) +
      Math115.PhysicalFiniteWalk.massAllowance (J := Fin n) r U L *
        Real.exp (-(T : ℝ) / aggregateMixingAllowance r c U) := by
  let actual := mapLaw (uniformLaw (α := Fin
      (T * uniformStepWidth r c U L (t + 2) (t + 2)
        (Math115.PhysicalStarBudget.attempts dimension t)
        (Math115.PhysicalStarBudget.precision dimension t)) → Bool))
    (joinedWalkWord r c U L hr hc start (t + 2) (t + 2)
      (Math115.PhysicalStarBudget.attempts dimension t)
      (Math115.PhysicalStarBudget.precision dimension t) T)
  let ideal := walkLaw (idealJoinedLaw r c U L hr hc hp) start T
  have htriangle := (Rat.cast_le (K := ℝ)).mpr
    (variation_triangle actual ideal (defectStationaryLaw r c U L))
  simp only [Rat.cast_add] at htriangle
  have hword := (Rat.cast_le (K := ℝ)).mpr
    (scheduledJoinedWalkWord_accuracy r c U L hr hc htotal hL hp start t T)
  simp only [Rat.cast_mul, Rat.cast_natCast] at hword
  exact htriangle.trans (add_le_add hword
    (idealJoinedWalk_mixing r c U L hr hc htotal hU hL hp start T))

end
end Math115.PhysicalTraceJoin
