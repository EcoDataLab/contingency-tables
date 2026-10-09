/-
SPDX-License-Identifier: Apache-2.0
Restarted finite-walk, exact terminal completion, and bounded retry laws.
The error theorem is an ideal finite-law result, not an oracle implementation
or a finite-bit machine-cost theorem.
-/
import Math115.PhysicalRationalKernel
import Math115.IdealRepairRefinement
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalMassBound

namespace Math115.PhysicalFiniteWalk

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open ReducedSmallChain ReducedAllSmallChain PhysicalStateNonempty
open PhysicalRationalKernel PhysicalStationarySuccess
open SmallGraphProfiles CompletionCounts PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates SmallContextFibres ResidualMixture FirstSuccess
open scoped BigOperators Classical

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

def capacityBound (r : I → ℕ) (U L : ℕ) : ℕ :=
  (∑ i, r i) + dimensionAllowance (I := I) (J := J) * L + U + 2

def massAllowance (r : I → ℕ) (U L : ℕ) : ℝ :=
  ((capacityBound (J := J) r U L + 1 : ℕ) : ℝ) ^
    (2 * dimensionAllowance (I := I) (J := J))

lemma massAllowance_positive (r : I → ℕ) (U L : ℕ) : 0 < massAllowance (J := J) r U L := by
  unfold massAllowance
  positivity

lemma capacity_le_bound (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (i : I) (j : J) :
    capacity r c U L i j ≤ capacityBound (J := J) r U L := by
  unfold capacity capacityBound paperCapacity
  split_ifs <;> omega

lemma weight_at_least_one (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (z : States r c U L) :
    1 ≤ weight r c U L z := by
  rw [← PhysicalStationaryLaw.fibre_card_weight r c U L z]
  exact_mod_cast (show 1 ≤ Fintype.card (Fibre r c U L z) from
    Nat.succ_le_of_lt (Fintype.card_pos (α := Fibre r c U L z)))

theorem total_mass_le (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :
    (∑ z : States r c U L, weight r c U L z) ≤ massAllowance (J := J) r U L :=
  physical_total_mass_le (firstPaperSmall r c U) (capacity r c U L) r c L
    (capacityBound (J := J) r U L) (capacity_le_bound r c U L)

theorem selectedChain_pi_lower (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (z : States r c U L) :
    1 / massAllowance (J := J) r U L ≤ (ReducedAllSmallChain.selectedChain r c U L).π z := by
  have hZ : 0 < ∑ y : States r c U L, weight r c U L y :=
    Finset.sum_pos (fun y _ => weight_positive r c U L y) Finset.univ_nonempty
  rw [ReducedAllSmallChain.selectedChain_pi]
  exact (one_div_le_one_div_of_le hZ (total_mass_le r c U L)).trans
    (div_le_div_of_nonneg_right (weight_at_least_one r c U L z) hZ.le)

/-- A finite rational walk bound on the actual selected kernel at any free scales. -/
theorem selectedWalkLaw_variation (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (K : ℝ) (hK : 1 ≤ K)
    (hp : ∀ H : States r c U L → ℝ,
      (ReducedAllSmallChain.selectedChain r c U L).variance H ≤
        K * (ReducedAllSmallChain.selectedChain r c U L).energy H)
    (x : States r c U L) (T : ℕ) :
    (variation (selectedWalkLaw r c U L x T) (PhysicalStationaryLaw.stationaryLaw r c U L) : ℝ) ≤
      massAllowance (J := J) r U L * Real.exp (-(T : ℝ) / K) := by
  let C := ReducedAllSmallChain.selectedChain r c U L
  let B := massAllowance (J := J) r U L
  have hB : 0 < B := massAllowance_positive r U L
  apply rationalWalk_variation (selectedTransitionLaw r c U L) C
    (selectedTransitionLaw_cast r c U L) (PhysicalStationaryLaw.stationaryLaw r c U L)
    (PhysicalStationaryLaw.stationaryRat_cast r c U L) x T _ (by positivity)
  intro y
  have h := C.point_mixing_exp K (1 / B) hK (by positivity)
    (selectedChain_pi_lower r c U L) hp T x y
  simpa only [one_div, div_eq_mul_inv, one_mul, inv_inv, mul_comm, B] using h

/-- A fresh uniform completion of the terminal state, retaining the actual fibre. -/
def walkJointLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (x : States r c U L) (T : ℕ) :
    RationalLaw (StateJoint r c U L) :=
  dependentJointLaw (selectedWalkLaw r c U L x T) (fun z => uniformLaw (α := Fibre r c U L z))

theorem walkJointLaw_variation_le (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (x : States r c U L) (T : ℕ) :
    variation (walkJointLaw r c U L x T) (PhysicalStationaryLaw.jointLaw r c U L) ≤
      variation (selectedWalkLaw r c U L x T) (PhysicalStationaryLaw.stationaryLaw r c U L) := by
  have h := variation_dependentJoint (selectedWalkLaw r c U L x T)
    (PhysicalStationaryLaw.stationaryLaw r c U L)
    (fun z => uniformLaw (α := Fibre r c U L z)) (fun z => uniformLaw (α := Fibre r c U L z))
  simpa only [walkJointLaw, PhysicalStationaryLaw.jointLaw, variation_self,
    mul_zero, Finset.sum_const_zero, add_zero] using h

theorem walkJointLaw_variation (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (K : ℝ) (hK : 1 ≤ K)
    (hp : ∀ H : States r c U L → ℝ,
      (ReducedAllSmallChain.selectedChain r c U L).variance H ≤
        K * (ReducedAllSmallChain.selectedChain r c U L).energy H)
    (x : States r c U L) (T : ℕ) :
    (variation (walkJointLaw r c U L x T) (PhysicalStationaryLaw.jointLaw r c U L) : ℝ) ≤
      massAllowance (J := J) r U L * Real.exp (-(T : ℝ) / K) := by
  have h : (variation (walkJointLaw r c U L x T) (PhysicalStationaryLaw.jointLaw r c U L) : ℝ) ≤
      (variation (selectedWalkLaw r c U L x T) (PhysicalStationaryLaw.stationaryLaw r c U L) : ℝ) := by
    exact_mod_cast walkJointLaw_variation_le r c U L x T
  exact h.trans (selectedWalkLaw_variation r c U L K hK hp x T)

/-- Each retry restarts the same finite walk using independent randomness. -/
def outerLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (x : States r c U L) (T R : ℕ) (fallback : Table r c) :
    RationalLaw (Table r c) :=
  retryLaw (walkJointLaw r c U L x T) (PhysicalStationaryLaw.stateTrial r c U L) fallback R

theorem outerLaw_variation (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] [Nonempty (Table r c)]
    (htotal : ∑ i, r i = ∑ j, c j) (A : ℝ) (hA : 0 < A)
    (hcount : (Fintype.card (PhysicalStationaryMass.PaddedTables r c U L) : ℝ) ≤
      A * (Fintype.card (Table r c) : ℝ)) (K : ℝ) (hK : 1 ≤ K)
    (hp : ∀ H : States r c U L → ℝ,
      (ReducedAllSmallChain.selectedChain r c U L).variance H ≤
        K * (ReducedAllSmallChain.selectedChain r c U L).energy H)
    (x : States r c U L) (T R : ℕ) (fallback : Table r c) :
    (variation (outerLaw r c U L x T R fallback) (uniformLaw (α := Table r c)) : ℝ) ≤
      Real.exp (-(R : ℝ) / (A * (1 + (Fintype.card (Cells (firstPaperSmall r c U)) : ℝ)^2))) +
      (R : ℝ) * (massAllowance (J := J) r U L * Real.exp (-(T : ℝ) / K)) := by
  have hr := retryLaw_variation (walkJointLaw r c U L x T)
    (PhysicalStationaryLaw.jointLaw r c U L) (PhysicalStationaryLaw.stateTrial r c U L) fallback R
  have ht := variation_triangle (outerLaw r c U L x T R fallback)
    (retryLaw (PhysicalStationaryLaw.jointLaw r c U L)
      (PhysicalStationaryLaw.stateTrial r c U L) fallback R) (uniformLaw (α := Table r c))
  have hrR := (Rat.cast_le (K := ℝ)).mpr hr
  have htR := (Rat.cast_le (K := ℝ)).mpr ht
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] at hrR htR
  have hm := mul_le_mul_of_nonneg_left (walkJointLaw_variation r c U L K hK hp x T)
    (show (0 : ℝ) ≤ R by positivity)
  have hi := PhysicalStationaryLaw.stationary_retry_variation r c U L htotal A hA hcount fallback R
  dsimp only [outerLaw] at htR ⊢
  linarith only [hrR, htR, hm, hi]

/-- A supplied feasible fallback gives a specific positive initial state. -/
def initialState (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (fallback : Table r c) : States r c U L :=
  ((originalStateSuccessEquiv r c U L) fallback).val.1

def idealGapAllowance (d : ℕ) : ℝ := 80000 * (d : ℝ)^17

lemma idealGapAllowance_at_least_one (d : ℕ) (hd : 1 ≤ d) : 1 ≤ idealGapAllowance d := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hp : (1 : ℝ) ≤ (d : ℝ)^17 := one_le_pow₀ hdR
  unfold idealGapAllowance
  nlinarith only [hp]

def successAllowance (r : I → ℕ) (c : J → ℕ) (U : ℕ) : ℝ :=
  2 * (1 + (Fintype.card (Cells (firstPaperSmall r c U)) : ℝ)^2)

lemma successAllowance_positive (r : I → ℕ) (c : J → ℕ) (U : ℕ) :
    0 < successAllowance r c U := by unfold successAllowance; positivity

def idealOuterLaw (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j)
    (fallback : Table r c) (T R : ℕ) : RationalLaw (Table r c) := by
  let U := IdealOracleScales.cutoff (I := I) (J := J)
  let L := IdealOracleScales.padding (I := I) (J := J)
  letI := states_nonempty r c U L htotal
  exact outerLaw r c U L (initialState r c U L fallback) T R fallback

/-- Actual ideal d17 kernel, finite walk, terminal completion and bounded retry.
No assumed stationary start or output conditioning is used. -/
theorem idealOuterLaw_variation (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j)
    (fallback : Table r c) (T R : ℕ) :
    letI := table_nonempty r c htotal
    (variation (idealOuterLaw r c htotal fallback T R) (uniformLaw (α := Table r c)) : ℝ) ≤
      Real.exp (-(R : ℝ) / successAllowance r c (IdealOracleScales.cutoff (I := I) (J := J))) +
      (R : ℝ) * (massAllowance (J := J) r (IdealOracleScales.cutoff (I := I) (J := J))
        (IdealOracleScales.padding (I := I) (J := J)) *
        Real.exp (-(T : ℝ) / idealGapAllowance (dimensionAllowance (I := I) (J := J)))) := by
  let U := IdealOracleScales.cutoff (I := I) (J := J)
  let L := IdealOracleScales.padding (I := I) (J := J)
  let d := dimensionAllowance (I := I) (J := J)
  letI := states_nonempty r c U L htotal
  letI := table_nonempty r c htotal
  have hd : 1 ≤ d := by dsimp [d, dimensionAllowance]; omega
  have hp (H : States r c U L → ℝ) :
      (ReducedAllSmallChain.selectedChain r c U L).variance H ≤
        idealGapAllowance d * (ReducedAllSmallChain.selectedChain r c U L).energy H := by
    have h := IdealRepairRefinement.selectedChain_poincare_d17_refined r c H
    change (ReducedAllSmallChain.selectedChain r c U L).variance H ≤
      ((128 * 5^4 : ℝ) * (d : ℝ)^17) * (ReducedAllSmallChain.selectedChain r c U L).energy H at h
    simpa only [idealGapAllowance, show (128 * 5^4 : ℝ) = 80000 by norm_num] using h
  exact outerLaw_variation r c U L htotal 2 (by norm_num) (PhysicalStationaryLaw.ideal_padded_count r c)
    (idealGapAllowance d) (idealGapAllowance_at_least_one d hd) hp
    (initialState r c U L fallback) T R fallback

/-- A scalar sufficient-schedule interface that includes any positive target. -/
lemma exp_neg_steps_le_inverse (K a : ℝ) (hK : 0 < K) (ha : 0 < a)
    (n : ℕ) (hn : K * Real.log a ≤ n) : Real.exp (-(n : ℝ) / K) ≤ 1 / a := by
  have hlog : Real.log a ≤ (n : ℝ) / K := by
    apply (le_div_iff₀ hK).mpr
    simpa only [mul_comm] using hn
  calc
    _ ≤ Real.exp (-Real.log a) := Real.exp_le_exp.mpr (by
      rw [neg_div]
      exact neg_le_neg hlog)
    _ = 1 / a := by rw [Real.exp_neg, Real.exp_log ha, one_div]

/-- Explicit logarithmic sufficient schedules; R>0 is stated to avoid any
division by zero. Natural ceilings satisfying these inequalities may be used. -/
theorem idealOuterLaw_variation_of_log_schedule
    (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j)
    (fallback : Table r c) (T R : ℕ) (ε : ℝ) (hε : 0 < ε) (hR : 0 < R)
    (hretry : successAllowance r c (IdealOracleScales.cutoff (I := I) (J := J)) *
      Real.log (2 / ε) ≤ R)
    (hwalk : idealGapAllowance (dimensionAllowance (I := I) (J := J)) *
      Real.log (2 * (R : ℝ) * massAllowance (J := J) r
        (IdealOracleScales.cutoff (I := I) (J := J)) (IdealOracleScales.padding (I := I) (J := J)) / ε) ≤ T) :
    letI := table_nonempty r c htotal
    (variation (idealOuterLaw r c htotal fallback T R) (uniformLaw (α := Table r c)) : ℝ) ≤ ε := by
  let U := IdealOracleScales.cutoff (I := I) (J := J)
  let L := IdealOracleScales.padding (I := I) (J := J)
  let d := dimensionAllowance (I := I) (J := J)
  let B := massAllowance (J := J) r U L
  let S := successAllowance r c U
  let K := idealGapAllowance d
  letI := table_nonempty r c htotal
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR
  have hB : 0 < B := massAllowance_positive r U L
  have hS : 0 < S := successAllowance_positive r c U
  have hK : 0 < K := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    (idealGapAllowance_at_least_one d (by dsimp [d, dimensionAllowance]; omega))
  have hf := exp_neg_steps_le_inverse S (2 / ε) hS (by positivity) R hretry
  have hf' : Real.exp (-(R : ℝ) / S) ≤ ε / 2 := by
    convert hf using 1 <;> field_simp
  have hw := exp_neg_steps_le_inverse K (2 * (R : ℝ) * B / ε) hK (by positivity) T hwalk
  have hm := mul_le_mul_of_nonneg_left hw (mul_nonneg hRR.le hB.le)
  have hid : (R : ℝ) * B * (1 / (2 * (R : ℝ) * B / ε)) = ε / 2 := by
    field_simp [ne_of_gt hRR, ne_of_gt hB]
    <;> ring
  rw [hid] at hm
  have hi := idealOuterLaw_variation r c htotal fallback T R
  change _ ≤ Real.exp (-(R : ℝ) / S) + (R : ℝ) * (B * Real.exp (-(T : ℝ) / K)) at hi
  nlinarith only [hi, hf', hm]

end
end Math115.PhysicalFiniteWalk
