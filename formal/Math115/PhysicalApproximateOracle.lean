/-
SPDX-License-Identifier: Apache-2.0
Approximate normalized completion laws in the actual finite-walk sampler.
Accuracy and fresh conditional randomness are hypotheses, not an efficient
oracle construction or a machine-cost theorem.
-/
import Math115.PhysicalFiniteWalk
import Math115.PhysicalCompletionOracle

namespace Math115.PhysicalApproximateOracle

open OAI.ContingencyTables
open ResidualMixture FirstSuccess ReducedSmallChain PhysicalRationalKernel
open PhysicalFiniteWalk PhysicalCompletionOracle PhysicalStationarySuccess PhysicalStateNonempty
open CompletionCounts
open scoped BigOperators Classical

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

def approximateJointLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (Q : States r c U L → RationalLaw (States r c U L))
    (F : (z : States r c U L) → RationalLaw (Fibre r c U L z))
    (x : States r c U L) (T : ℕ) : RationalLaw (StateJoint r c U L) :=
  dependentJointLaw (walkLaw Q x T) F

/-- Uniform row error controls adaptively visited states. The terminal
error is for the actual state's conditional completion space. -/
theorem approximateJointLaw_variation (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)]
    (Q : States r c U L → RationalLaw (States r c U L))
    (F : (z : States r c U L) → RationalLaw (Fibre r c U L z)) (δ η : ℚ)
    (hQ : ∀ z, variation (Q z) (selectedTransitionLaw r c U L z) ≤ δ)
    (hF : ∀ z, variation (F z) (uniformLaw (α := Fibre r c U L z)) ≤ η)
    (x : States r c U L) (T : ℕ) :
    variation (approximateJointLaw r c U L Q F x T) (walkJointLaw r c U L x T) ≤ (T : ℚ) * δ + η := by
  have hj := variation_dependentJoint_uniform (walkLaw Q x T) (selectedWalkLaw r c U L x T)
    F (fun z => uniformLaw (α := Fibre r c U L z)) η hF
  have hw := walkLaw_variation Q (selectedTransitionLaw r c U L) δ hQ x T
  exact hj.trans (add_le_add hw (le_refl η))

def approximateOuterLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (Q : States r c U L → RationalLaw (States r c U L))
    (F : (z : States r c U L) → RationalLaw (Fibre r c U L z))
    (x : States r c U L) (T R : ℕ) (fallback : Table r c) : RationalLaw (Table r c) :=
  retryLaw (approximateJointLaw r c U L Q F x T) (PhysicalStationaryLaw.stateTrial r c U L) fallback R

/-- Independent restarted trials charge oracle error before success testing. -/
theorem approximateOuterLaw_variation_le (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)]
    (Q : States r c U L → RationalLaw (States r c U L))
    (F : (z : States r c U L) → RationalLaw (Fibre r c U L z)) (δ η : ℚ)
    (hQ : ∀ z, variation (Q z) (selectedTransitionLaw r c U L z) ≤ δ)
    (hF : ∀ z, variation (F z) (uniformLaw (α := Fibre r c U L z)) ≤ η)
    (x : States r c U L) (T R : ℕ) (fallback : Table r c) :
    variation (approximateOuterLaw r c U L Q F x T R fallback) (outerLaw r c U L x T R fallback) ≤
      (R : ℚ) * ((T : ℚ) * δ + η) :=
  (retryLaw_variation _ _ _ fallback R).trans
    (mul_le_mul_of_nonneg_left (approximateJointLaw_variation r c U L Q F δ η hQ hF x T)
      (Nat.cast_nonneg R))

theorem approximateOuterLaw_variation (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] [Nonempty (Table r c)]
    (Q : States r c U L → RationalLaw (States r c U L))
    (F : (z : States r c U L) → RationalLaw (Fibre r c U L z)) (δ η : ℚ)
    (hQ : ∀ z, variation (Q z) (selectedTransitionLaw r c U L z) ≤ δ)
    (hF : ∀ z, variation (F z) (uniformLaw (α := Fibre r c U L z)) ≤ η)
    (x : States r c U L) (T R : ℕ) (fallback : Table r c) :
    (variation (approximateOuterLaw r c U L Q F x T R fallback) (uniformLaw (α := Table r c)) : ℝ) ≤
      (variation (outerLaw r c U L x T R fallback) (uniformLaw (α := Table r c)) : ℝ) +
      (R : ℝ) * ((T : ℝ) * (δ : ℝ) + (η : ℝ)) := by
  have ht := variation_triangle (approximateOuterLaw r c U L Q F x T R fallback)
    (outerLaw r c U L x T R fallback) (uniformLaw (α := Table r c))
  have hr := approximateOuterLaw_variation_le r c U L Q F δ η hQ hF x T R fallback
  have htR := (Rat.cast_le (K := ℝ)).mpr ht
  have hrR := (Rat.cast_le (K := ℝ)).mpr hr
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_natCast] at htR hrR
  linarith only [htR, hrR]

/-- Transition and terminal calls may use distinct accuracy settings. -/
def idealOracleOuterLaw (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j)
    (fallback : Table r c) (T R : ℕ)
    (transitionOracle terminalOracle : OracleFamily r c
      (IdealOracleScales.cutoff (I := I) (J := J)) (IdealOracleScales.padding (I := I) (J := J))) :
    RationalLaw (Table r c) := by
  let U := IdealOracleScales.cutoff (I := I) (J := J)
  let L := IdealOracleScales.padding (I := I) (J := J)
  letI := states_nonempty r c U L htotal
  exact approximateOuterLaw r c U L (selectedStepLaw r c U L transitionOracle)
    (selectedCompletionLaw r c U L terminalOracle) (initialState r c U L fallback) T R fallback

/-- An approximate ordinary-completion oracle plugged into the actual
proposal/draw/test chain has no unproved approximate-chain stationary law. -/
theorem idealOracleOuterLaw_variation (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j)
    (fallback : Table r c) (T R : ℕ)
    (transitionOracle terminalOracle : OracleFamily r c
      (IdealOracleScales.cutoff (I := I) (J := J)) (IdealOracleScales.padding (I := I) (J := J)))
    (ζstep ζterminal : ℚ) (hstep : 0 ≤ ζstep) (hterminal : 0 ≤ ζterminal)
    (haccuracyStep : ∀ i₀ j₀ z, variation (transitionOracle i₀ j₀ z)
      (uniformLaw (α := ReferenceTable r c (IdealOracleScales.cutoff (I := I) (J := J))
        (IdealOracleScales.padding (I := I) (J := J)) i₀ j₀ z)) ≤ ζstep)
    (haccuracyTerminal : ∀ i₀ j₀ z, variation (terminalOracle i₀ j₀ z)
      (uniformLaw (α := ReferenceTable r c (IdealOracleScales.cutoff (I := I) (J := J))
        (IdealOracleScales.padding (I := I) (J := J)) i₀ j₀ z)) ≤ ζterminal) :
    letI := table_nonempty r c htotal
    (variation (idealOracleOuterLaw r c htotal fallback T R transitionOracle terminalOracle)
      (uniformLaw (α := Table r c)) : ℝ) ≤
      Real.exp (-(R : ℝ) / successAllowance r c (IdealOracleScales.cutoff (I := I) (J := J))) +
      (R : ℝ) * (massAllowance (J := J) r (IdealOracleScales.cutoff (I := I) (J := J))
        (IdealOracleScales.padding (I := I) (J := J)) *
        Real.exp (-(T : ℝ) / idealGapAllowance (dimensionAllowance (I := I) (J := J)))) +
      (R : ℝ) * ((T : ℝ) * (proposalAllowance (dimensionAllowance (I := I) (J := J)) : ℝ) *
        (ζstep : ℝ) + (ζterminal : ℝ)) := by
  let U := IdealOracleScales.cutoff (I := I) (J := J)
  let L := IdealOracleScales.padding (I := I) (J := J)
  letI := states_nonempty r c U L htotal
  letI := table_nonempty r c htotal
  have h := approximateOuterLaw_variation r c U L (selectedStepLaw r c U L transitionOracle)
    (selectedCompletionLaw r c U L terminalOracle)
    (proposalAllowance (dimensionAllowance (I := I) (J := J)) * ζstep) ζterminal
    (selectedStepLaw_variation r c U L transitionOracle ζstep hstep haccuracyStep)
    (selectedCompletionLaw_variation r c U L terminalOracle ζterminal hterminal haccuracyTerminal)
    (initialState r c U L fallback) T R fallback
  have hi := idealOuterLaw_variation r c htotal fallback T R
  simp only [Rat.cast_mul] at h
  change (variation (idealOracleOuterLaw r c htotal fallback T R transitionOracle terminalOracle)
      (uniformLaw (α := Table r c)) : ℝ) ≤
    (variation (idealOuterLaw r c htotal fallback T R) (uniformLaw (α := Table r c)) : ℝ) +
      (R : ℝ) * ((T : ℝ) * ((proposalAllowance (dimensionAllowance (I := I) (J := J)) : ℝ) *
        (ζstep : ℝ)) + (ζterminal : ℝ)) at h
  nlinarith only [h, hi]

/-- Allocate ideal mixing/retry error and oracle error before rejection. -/
theorem approximateOuterLaw_variation_of_budget (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] [Nonempty (Table r c)]
    (Q : States r c U L → RationalLaw (States r c U L))
    (F : (z : States r c U L) → RationalLaw (Fibre r c U L z)) (δ η : ℚ)
    (hQ : ∀ z, variation (Q z) (selectedTransitionLaw r c U L z) ≤ δ)
    (hF : ∀ z, variation (F z) (uniformLaw (α := Fibre r c U L z)) ≤ η)
    (x : States r c U L) (T R : ℕ) (fallback : Table r c) (ε : ℝ)
    (hideal : (variation (outerLaw r c U L x T R fallback) (uniformLaw (α := Table r c)) : ℝ) ≤ ε / 2)
    (horacle : (R : ℝ) * ((T : ℝ) * (δ : ℝ) + (η : ℝ)) ≤ ε / 2) :
    (variation (approximateOuterLaw r c U L Q F x T R fallback) (uniformLaw (α := Table r c)) : ℝ) ≤ ε := by
  have h := approximateOuterLaw_variation r c U L Q F δ η hQ hF x T R fallback
  linarith only [h, hideal, horacle]

end
end Math115.PhysicalApproximateOracle
