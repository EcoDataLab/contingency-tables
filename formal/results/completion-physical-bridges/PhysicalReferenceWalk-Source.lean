/-
SPDX-License-Identifier: Apache-2.0
Finite-walk and approximate-oracle output laws for explicit reference indices.
No reference-kernel invariance is assumed: mixing follows the chain belonging
to the supplied pair. These are finite-law semantics, not executable neighbor
generation, reference selection, or machine-cost claims.
-/
import Math115.PhysicalLatticeCompletion

namespace Math115.PhysicalReferenceWalk

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open ReducedSmallChain PhysicalRationalKernel PhysicalFiniteWalk
open PhysicalCompletionOracle PhysicalStationarySuccess PhysicalStateNonempty
open PhysicalApproximateOracle SmallGraphProfiles CompletionCounts
open ResidualMixture FirstSuccess CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The supplied pair's transition law casts to its own actual chain. -/
theorem referenceTransitionLaw_cast (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (x y : States r c U L) :
    ((referenceTransitionLaw r c U L i₀ j₀ x).mass y : ℝ) =
      (ReducedSmallChain.chain r c U L i₀ j₀).P x y :=
  referenceTransitionRat_cast r c U L i₀ j₀ x y

/-- Stationary normalization is shared; equality of transition kernels is
neither required nor asserted. -/
theorem referenceStationaryLaw_cast (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (z : States r c U L) :
    ((PhysicalStationaryLaw.stationaryLaw r c U L).mass z : ℝ) =
      (ReducedSmallChain.chain r c U L i₀ j₀).π z := by
  rw [ReducedSmallChain.chain_pi]
  change (PhysicalStationaryLaw.stationaryRat r c U L z : ℝ) = _
  simp only [PhysicalStationaryLaw.stationaryRat, Rat.cast_div, Rat.cast_sum,
    Rat.cast_natCast, PhysicalStationaryLaw.fibre_card_weight]

theorem referenceChain_pi_lower (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (z : States r c U L) :
    1 / massAllowance (J := J) r U L ≤ (ReducedSmallChain.chain r c U L i₀ j₀).π z := by
  have hZ : 0 < ∑ y : States r c U L, weight r c U L y :=
    Finset.sum_pos (fun y _ => weight_positive r c U L y) Finset.univ_nonempty
  rw [ReducedSmallChain.chain_pi]
  exact (one_div_le_one_div_of_le hZ (total_mass_le r c U L)).trans
    (div_le_div_of_nonneg_right (weight_at_least_one r c U L z) hZ.le)

def referenceWalkLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (x : States r c U L) (T : ℕ) : RationalLaw (States r c U L) :=
  walkLaw (referenceTransitionLaw r c U L i₀ j₀) x T

theorem referenceWalkLaw_cast (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (T : ℕ) (x y : States r c U L) :
    ((referenceWalkLaw r c U L i₀ j₀ x T).mass y : ℝ) =
      ((ReducedSmallChain.chain r c U L i₀ j₀).kernel.power T).P x y :=
  walkLaw_cast_kernel _ _ (referenceTransitionLaw_cast r c U L i₀ j₀) T x y

theorem referenceWalkLaw_variation (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (K : ℝ) (hK : 1 ≤ K)
    (hp : ∀ H : States r c U L → ℝ,
      (ReducedSmallChain.chain r c U L i₀ j₀).variance H ≤
        K * (ReducedSmallChain.chain r c U L i₀ j₀).energy H)
    (x : States r c U L) (T : ℕ) :
    (variation (referenceWalkLaw r c U L i₀ j₀ x T)
      (PhysicalStationaryLaw.stationaryLaw r c U L) : ℝ) ≤
        massAllowance (J := J) r U L * Real.exp (-(T : ℝ) / K) := by
  let C := ReducedSmallChain.chain r c U L i₀ j₀
  let B := massAllowance (J := J) r U L
  have hB : 0 < B := massAllowance_positive r U L
  apply rationalWalk_variation (referenceTransitionLaw r c U L i₀ j₀) C
    (referenceTransitionLaw_cast r c U L i₀ j₀) (PhysicalStationaryLaw.stationaryLaw r c U L)
    (referenceStationaryLaw_cast r c U L i₀ j₀) x T _ (by positivity)
  intro y
  have h := C.point_mixing_exp K (1 / B) hK (by positivity)
    (referenceChain_pi_lower r c U L i₀ j₀) hp T x y
  simpa only [one_div, div_eq_mul_inv, one_mul, inv_inv, mul_comm, B] using h

def referenceJointLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (x : States r c U L) (T : ℕ) : RationalLaw (StateJoint r c U L) :=
  dependentJointLaw (referenceWalkLaw r c U L i₀ j₀ x T)
    (fun z => uniformLaw (α := Fibre r c U L z))

theorem referenceJointLaw_variation_le (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (x : States r c U L) (T : ℕ) :
    variation (referenceJointLaw r c U L i₀ j₀ x T) (PhysicalStationaryLaw.jointLaw r c U L) ≤
      variation (referenceWalkLaw r c U L i₀ j₀ x T) (PhysicalStationaryLaw.stationaryLaw r c U L) := by
  have h := variation_dependentJoint (referenceWalkLaw r c U L i₀ j₀ x T)
    (PhysicalStationaryLaw.stationaryLaw r c U L)
    (fun z => uniformLaw (α := Fibre r c U L z)) (fun z => uniformLaw (α := Fibre r c U L z))
  simpa only [referenceJointLaw, PhysicalStationaryLaw.jointLaw, variation_self,
    mul_zero, Finset.sum_const_zero, add_zero] using h

theorem referenceJointLaw_variation (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (K : ℝ) (hK : 1 ≤ K)
    (hp : ∀ H : States r c U L → ℝ,
      (ReducedSmallChain.chain r c U L i₀ j₀).variance H ≤
        K * (ReducedSmallChain.chain r c U L i₀ j₀).energy H)
    (x : States r c U L) (T : ℕ) :
    (variation (referenceJointLaw r c U L i₀ j₀ x T) (PhysicalStationaryLaw.jointLaw r c U L) : ℝ) ≤
      massAllowance (J := J) r U L * Real.exp (-(T : ℝ) / K) := by
  have h : (variation (referenceJointLaw r c U L i₀ j₀ x T)
      (PhysicalStationaryLaw.jointLaw r c U L) : ℝ) ≤
      (variation (referenceWalkLaw r c U L i₀ j₀ x T)
        (PhysicalStationaryLaw.stationaryLaw r c U L) : ℝ) := by
    exact_mod_cast referenceJointLaw_variation_le r c U L i₀ j₀ x T
  exact h.trans (referenceWalkLaw_variation r c U L i₀ j₀ K hK hp x T)

/-- Independent attempts restart this reference pair's actual finite walk. -/
def referenceOuterLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (x : States r c U L) (T R : ℕ) (fallback : Table r c) : RationalLaw (Table r c) :=
  retryLaw (referenceJointLaw r c U L i₀ j₀ x T)
    (PhysicalStationaryLaw.stateTrial r c U L) fallback R

theorem referenceOuterLaw_variation (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] [Nonempty (Table r c)]
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (htotal : ∑ i, r i = ∑ j, c j) (A : ℝ) (hA : 0 < A)
    (hcount : (Fintype.card (PhysicalStationaryMass.PaddedTables r c U L) : ℝ) ≤
      A * (Fintype.card (Table r c) : ℝ)) (K : ℝ) (hK : 1 ≤ K)
    (hp : ∀ H : States r c U L → ℝ,
      (ReducedSmallChain.chain r c U L i₀ j₀).variance H ≤
        K * (ReducedSmallChain.chain r c U L i₀ j₀).energy H)
    (x : States r c U L) (T R : ℕ) (fallback : Table r c) :
    (variation (referenceOuterLaw r c U L i₀ j₀ x T R fallback)
      (uniformLaw (α := Table r c)) : ℝ) ≤
      Real.exp (-(R : ℝ) / (A * (1 + (Fintype.card (SmallContextCoordinates.Cells (firstPaperSmall r c U)) : ℝ)^2))) +
      (R : ℝ) * (massAllowance (J := J) r U L * Real.exp (-(T : ℝ) / K)) := by
  have hr := retryLaw_variation (referenceJointLaw r c U L i₀ j₀ x T)
    (PhysicalStationaryLaw.jointLaw r c U L) (PhysicalStationaryLaw.stateTrial r c U L) fallback R
  have ht := variation_triangle (referenceOuterLaw r c U L i₀ j₀ x T R fallback)
    (retryLaw (PhysicalStationaryLaw.jointLaw r c U L)
      (PhysicalStationaryLaw.stateTrial r c U L) fallback R) (uniformLaw (α := Table r c))
  have hrR := (Rat.cast_le (K := ℝ)).mpr hr
  have htR := (Rat.cast_le (K := ℝ)).mpr ht
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] at hrR htR
  have hm := mul_le_mul_of_nonneg_left (referenceJointLaw_variation r c U L i₀ j₀ K hK hp x T)
    (show (0 : ℝ) ≤ R by positivity)
  have hi := PhysicalStationaryLaw.stationary_retry_variation r c U L htotal A hA hcount fallback R
  dsimp only [referenceOuterLaw] at htR ⊢
  linarith only [hrR, htR, hm, hi]

/-- Generic perturbation estimate around the supplied pair's exact kernel. -/
theorem referenceApproximateJoint_variation (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (Q : States r c U L → RationalLaw (States r c U L))
    (F : (z : States r c U L) → RationalLaw (Fibre r c U L z)) (δ η : ℚ)
    (hQ : ∀ z, variation (Q z) (referenceTransitionLaw r c U L i₀ j₀ z) ≤ δ)
    (hF : ∀ z, variation (F z) (uniformLaw (α := Fibre r c U L z)) ≤ η)
    (x : States r c U L) (T : ℕ) :
    variation (approximateJointLaw r c U L Q F x T) (referenceJointLaw r c U L i₀ j₀ x T) ≤
      (T : ℚ) * δ + η := by
  have hj := variation_dependentJoint_uniform (walkLaw Q x T)
    (referenceWalkLaw r c U L i₀ j₀ x T) F
    (fun z => uniformLaw (α := Fibre r c U L z)) η hF
  have hw := walkLaw_variation Q (referenceTransitionLaw r c U L i₀ j₀) δ hQ x T
  exact hj.trans (add_le_add hw (le_refl η))

theorem referenceApproximateOuter_variation_le (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (Q : States r c U L → RationalLaw (States r c U L))
    (F : (z : States r c U L) → RationalLaw (Fibre r c U L z)) (δ η : ℚ)
    (hQ : ∀ z, variation (Q z) (referenceTransitionLaw r c U L i₀ j₀ z) ≤ δ)
    (hF : ∀ z, variation (F z) (uniformLaw (α := Fibre r c U L z)) ≤ η)
    (x : States r c U L) (T R : ℕ) (fallback : Table r c) :
    variation (approximateOuterLaw r c U L Q F x T R fallback)
      (referenceOuterLaw r c U L i₀ j₀ x T R fallback) ≤
      (R : ℚ) * ((T : ℚ) * δ + η) :=
  (retryLaw_variation _ _ _ fallback R).trans
    (mul_le_mul_of_nonneg_left
      (referenceApproximateJoint_variation r c U L i₀ j₀ Q F δ η hQ hF x T) (Nat.cast_nonneg R))

theorem referenceApproximateOuter_variation (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] [Nonempty (Table r c)]
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (Q : States r c U L → RationalLaw (States r c U L))
    (F : (z : States r c U L) → RationalLaw (Fibre r c U L z)) (δ η : ℚ)
    (hQ : ∀ z, variation (Q z) (referenceTransitionLaw r c U L i₀ j₀ z) ≤ δ)
    (hF : ∀ z, variation (F z) (uniformLaw (α := Fibre r c U L z)) ≤ η)
    (x : States r c U L) (T R : ℕ) (fallback : Table r c) :
    (variation (approximateOuterLaw r c U L Q F x T R fallback) (uniformLaw (α := Table r c)) : ℝ) ≤
      (variation (referenceOuterLaw r c U L i₀ j₀ x T R fallback) (uniformLaw (α := Table r c)) : ℝ) +
      (R : ℝ) * ((T : ℝ) * (δ : ℝ) + (η : ℝ)) := by
  have ht := variation_triangle (approximateOuterLaw r c U L Q F x T R fallback)
    (referenceOuterLaw r c U L i₀ j₀ x T R fallback) (uniformLaw (α := Table r c))
  have hr := referenceApproximateOuter_variation_le r c U L i₀ j₀ Q F δ η hQ hF x T R fallback
  have htR := (Rat.cast_le (K := ℝ)).mpr ht
  have hrR := (Rat.cast_le (K := ℝ)).mpr hr
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] at htR hrR
  linarith only [htR, hrR]

local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "U" => IdealOracleScales.cutoff (I := I) (J := J)
local notation "L" => IdealOracleScales.padding (I := I) (J := J)

theorem idealReference_poincare (r : I → ℕ) (c : J → ℕ) [Nonempty (States r c U L)]
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (H : States r c U L → ℝ) :
    (ReducedSmallChain.chain r c U L i₀ j₀).variance H ≤
      idealGapAllowance d * (ReducedSmallChain.chain r c U L i₀ j₀).energy H := by
  have h := IdealRepairRefinement.referenceChain_poincare_d17_refined r c i₀ j₀ H
  change (ReducedSmallChain.chain r c U L i₀ j₀).variance H ≤
    ((128 * 5^4 : ℝ) * (d : ℝ)^17) * (ReducedSmallChain.chain r c U L i₀ j₀).energy H at h
  simpa only [idealGapAllowance, show (128 * 5^4 : ℝ) = 80000 by norm_num] using h

def idealReferenceOuterLaw (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (fallback : Table r c) (T R : ℕ) :
    RationalLaw (Table r c) := by
  letI := states_nonempty r c U L htotal
  exact referenceOuterLaw r c U L i₀ j₀ (initialState r c U L fallback) T R fallback

theorem idealReferenceOuterLaw_variation (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (fallback : Table r c) (T R : ℕ) :
    letI := table_nonempty r c htotal
    (variation (idealReferenceOuterLaw r c htotal i₀ j₀ fallback T R)
      (uniformLaw (α := Table r c)) : ℝ) ≤
      Real.exp (-(R : ℝ) / successAllowance r c U) +
      (R : ℝ) * (massAllowance (J := J) r U L * Real.exp (-(T : ℝ) / idealGapAllowance d)) := by
  let _ := states_nonempty r c U L htotal
  let _ := table_nonempty r c htotal
  exact referenceOuterLaw_variation r c U L i₀ j₀ htotal 2 (by norm_num)
    (PhysicalStationaryLaw.ideal_padded_count r c) (idealGapAllowance d)
    (idealGapAllowance_at_least_one d (by unfold dimensionAllowance; omega))
    (idealReference_poincare r c i₀ j₀) (initialState r c U L fallback) T R fallback

set_option linter.unusedVariables false in
/-- Transition and terminal experiments use the supplied pair throughout. -/
def idealReferenceOracleOuterLaw (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (fallback : Table r c) (T R : ℕ)
    (transitionOracle terminalOracle : OracleFamily r c U L) : RationalLaw (Table r c) := by
  letI := states_nonempty r c U L htotal
  exact approximateOuterLaw r c U L
    (referenceStepLaw r c U L i₀ j₀ (transitionOracle i₀ j₀))
    (referenceCompletionLaw r c U L i₀ j₀ (terminalOracle i₀ j₀))
    (initialState r c U L fallback) T R fallback

/-- Accuracy need only hold at every state for the actual supplied pair.
No relation to the classical selected approximate law is required. -/
theorem idealReferenceOracleOuterLaw_variation (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (fallback : Table r c) (T R : ℕ) (transitionOracle terminalOracle : OracleFamily r c U L)
    (ζstep ζterminal : ℚ) (hstep : 0 ≤ ζstep)
    (haccuracyStep : ∀ z, variation (transitionOracle i₀ j₀ z)
      (uniformLaw (α := ReferenceTable r c U L i₀ j₀ z)) ≤ ζstep)
    (haccuracyTerminal : ∀ z, variation (terminalOracle i₀ j₀ z)
      (uniformLaw (α := ReferenceTable r c U L i₀ j₀ z)) ≤ ζterminal) :
    letI := table_nonempty r c htotal
    (variation (idealReferenceOracleOuterLaw r c htotal i₀ j₀ fallback T R transitionOracle terminalOracle)
      (uniformLaw (α := Table r c)) : ℝ) ≤
      Real.exp (-(R : ℝ) / successAllowance r c U) +
      (R : ℝ) * (massAllowance (J := J) r U L * Real.exp (-(T : ℝ) / idealGapAllowance d)) +
      (R : ℝ) * ((T : ℝ) * (proposalAllowance d : ℝ) * (ζstep : ℝ) + (ζterminal : ℝ)) := by
  let _ := states_nonempty r c U L htotal
  let _ := table_nonempty r c htotal
  have h := referenceApproximateOuter_variation r c U L i₀ j₀
    (referenceStepLaw r c U L i₀ j₀ (transitionOracle i₀ j₀))
    (referenceCompletionLaw r c U L i₀ j₀ (terminalOracle i₀ j₀))
    (proposalAllowance d * ζstep) ζterminal
    (referenceStep_variation_uniform r c U L i₀ j₀ _ ζstep hstep haccuracyStep)
    (fun z => by rw [referenceCompletionLaw_variation]; exact haccuracyTerminal z)
    (initialState r c U L fallback) T R fallback
  have hi := idealReferenceOuterLaw_variation r c htotal i₀ j₀ fallback T R
  simp only [Rat.cast_mul] at h
  change (variation (idealReferenceOracleOuterLaw r c htotal i₀ j₀ fallback T R transitionOracle terminalOracle)
      (uniformLaw (α := Table r c)) : ℝ) ≤
    (variation (idealReferenceOuterLaw r c htotal i₀ j₀ fallback T R)
      (uniformLaw (α := Table r c)) : ℝ) +
      (R : ℝ) * ((T : ℝ) * ((proposalAllowance d : ℝ) * (ζstep : ℝ)) + (ζterminal : ℝ)) at h
  nlinarith only [h, hi]

/-- Concrete dense completion laws for an arbitrary explicitly supplied pair. -/
def denseReferenceOuterLaw (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (fallback : Table r c)
    (T R hStep hTerminal : ℕ) : RationalLaw (Table r c) :=
  idealReferenceOracleOuterLaw r c htotal i₀ j₀ fallback T R
    (PhysicalLatticeCompletion.denseOracle r c hStep)
    (PhysicalLatticeCompletion.denseOracle r c hTerminal)

/-- All oracle, stationary, mass, success and Poincaré premises are discharged.
The supplied references may be the outputs of a future computable selector. -/
theorem denseReferenceOuterLaw_variation (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (fallback : Table r c) (T R hStep hTerminal : ℕ) :
    letI := table_nonempty r c htotal
    (variation (denseReferenceOuterLaw r c htotal i₀ j₀ fallback T R hStep hTerminal)
      (uniformLaw (α := Table r c)) : ℝ) ≤
      Real.exp (-(R : ℝ) / successAllowance r c U) +
      (R : ℝ) * (massAllowance (J := J) r U L * Real.exp (-(T : ℝ) / idealGapAllowance d)) +
      (R : ℝ) * ((T : ℝ) * (proposalAllowance d : ℝ) * (dyadic hStep : ℝ) +
        (dyadic hTerminal : ℝ)) := by
  exact idealReferenceOracleOuterLaw_variation r c htotal i₀ j₀ fallback T R
    (PhysicalLatticeCompletion.denseOracle r c hStep)
    (PhysicalLatticeCompletion.denseOracle r c hTerminal) (dyadic hStep) (dyadic hTerminal)
    (dyadic_positive hStep).le (PhysicalLatticeCompletion.denseOracle_accuracy r c hStep i₀ j₀)
    (PhysicalLatticeCompletion.denseOracle_accuracy r c hTerminal i₀ j₀)

end
end Math115.PhysicalReferenceWalk
