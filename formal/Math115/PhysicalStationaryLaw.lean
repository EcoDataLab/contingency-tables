/-
SPDX-License-Identifier: Apache-2.0
Exact stationary completion and rejection laws at free physical scales.
These are laws of independent exact stationary trials, not finite-bit costs.
-/
import Math115.PhysicalStationarySuccess
import Math115.IdealOracleScales
import OAI.Combinatorics.ContingencyTables.Transport.FiniteDependentLaw
import OAI.Combinatorics.ContingencyTables.Transport.UniformPartialRejection

set_option maxHeartbeats 1200000

namespace Math115.PhysicalStationaryLaw

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open ReducedSmallChain PhysicalStateNonempty PhysicalStationaryMass PhysicalStationarySuccess
open SmallGraphProfiles PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates SmallContextFibres PaddedCompletions CompletionCounts
open ResidualMixture FirstSuccess

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

lemma fibre_card_weight (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (z : States r c U L) :
    (Fintype.card (Fibre r c U L z) : ℝ) = weight r c U L z :=
  (hardMarginal_eq_fibre_card _ _ r c L _ (naturalProfile_bounded z.val.val)).symm

instance fibreNonempty (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (z : States r c U L) :
    Nonempty (Fibre r c U L z) := by
  apply Fintype.card_pos_iff.mp
  have h := weight_positive r c U L z
  rw [← fibre_card_weight r c U L z] at h
  exact_mod_cast h

lemma stateJoint_card (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :
    (Fintype.card (StateJoint r c U L) : ℝ) = normalizer r c U L := by
  rw [Fintype.card_sigma, Nat.cast_sum]
  exact Finset.sum_congr rfl (fun z _ => fibre_card_weight r c U L z)

def stationaryRat (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (z : States r c U L) : ℚ :=
  (Fintype.card (Fibre r c U L z) : ℚ) /
    ∑ y : States r c U L, (Fintype.card (Fibre r c U L y) : ℚ)

/-- This rational state law is the stationary law of the actual selected
physical chain in either the reference or unit branch. -/
lemma stationaryRat_cast (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (z : States r c U L) :
    (stationaryRat r c U L z : ℝ) = (ReducedAllSmallChain.selectedChain r c U L).π z := by
  rw [ReducedAllSmallChain.selectedChain_pi]
  simp only [stationaryRat, Rat.cast_div, Rat.cast_sum, Rat.cast_natCast, fibre_card_weight]

def stationaryLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] : RationalLaw (States r c U L) where
  mass := stationaryRat r c U L
  nonnegative := fun z => by
    have h := (ReducedAllSmallChain.selectedChain r c U L).positive z
    rw [← stationaryRat_cast] at h
    exact_mod_cast h.le
  total := by
    apply Rat.cast_injective (α := ℝ)
    simp only [Rat.cast_sum, stationaryRat_cast, Rat.cast_one]
    exact (ReducedAllSmallChain.selectedChain r c U L).normalized

/-- Exact stationary state draw followed by a uniform completion of that
same state. Completion multiplicities remain part of the law. -/
def jointLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] : RationalLaw (StateJoint r c U L) :=
  dependentJointLaw (stationaryLaw r c U L) (fun z => uniformLaw (α := Fibre r c U L z))

theorem jointLaw_uniform (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] :
    jointLaw r c U L = uniformLaw (α := StateJoint r c U L) := by
  apply dependentJointLaw_uniform
  intro z
  rfl

abbrev stateTrial (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :
    StateJoint r c U L → Option (Table r c) :=
  partialEquivDraw (StateJointSuccess r c U L) (originalStateSuccessEquiv r c U L)

/-- Every original table has exactly one accepted physical joint preimage. -/
theorem stationary_trial_mass (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (X : Table r c) :
    successMass (jointLaw r c U L) (stateTrial r c U L) X =
      1 / (Fintype.card (StateJoint r c U L) : ℚ) := by
  rw [jointLaw_uniform]
  exact partialEquiv_success_mass _ _ X

theorem stationary_trial_mass_real (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (X : Table r c) :
    (successMass (jointLaw r c U L) (stateTrial r c U L) X : ℝ) =
      1 / normalizer r c U L := by
  rw [← stateJoint_card]
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast] using
    congrArg (fun q : ℚ => (q : ℝ)) (stationary_trial_mass r c U L X)

/-- Exact failure mass, hence exact success probability `N/Z`. -/
theorem stationary_failure_mass (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] :
    failureMass (jointLaw r c U L) (stateTrial r c U L) =
      1 - (Fintype.card (Table r c) : ℚ) / (Fintype.card (StateJoint r c U L) : ℚ) := by
  rw [jointLaw_uniform]
  exact partialEquiv_failure_mass _ _

theorem stationary_success_probability (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] :
    (1 - failureMass (jointLaw r c U L) (stateTrial r c U L) : ℝ) =
      (Fintype.card (Table r c) : ℝ) / normalizer r c U L := by
  rw [stationary_failure_mass]
  push_cast
  rw [stateJoint_card]
  ring

/-- The stationary trial probability is bounded using the ordinary count
ratio and the defect charge. Equal ordinary totals discharge nonemptiness. -/
theorem stationary_success_lower (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (A : ℝ) (hA : 0 < A)
    (hcount : (Fintype.card (PaddedTables r c U L) : ℝ) ≤
      A * (Fintype.card (Table r c) : ℝ)) :
    1 / (A * (1 + (Fintype.card (Cells (firstPaperSmall r c U)) : ℝ)^2)) ≤
      (Fintype.card (Table r c) : ℝ) / (Fintype.card (StateJoint r c U L) : ℝ) := by
  rw [stateJoint_card]
  exact success_ratio_lower r c U L htotal A hA hcount

/-- Direct success-probability interface for the actual stationary
state/completion trial, with its Nonempty premise discharged. -/
theorem stationary_success_probability_lower (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (A : ℝ) (hA : 0 < A)
    (hcount : (Fintype.card (PaddedTables r c U L) : ℝ) ≤
      A * (Fintype.card (Table r c) : ℝ)) :
    letI := states_nonempty r c U L htotal
    1 / (A * (1 + (Fintype.card (Cells (firstPaperSmall r c U)) : ℝ)^2)) ≤
      (1 - failureMass (jointLaw r c U L) (stateTrial r c U L) : ℝ) := by
  letI := states_nonempty r c U L htotal
  rw [stationary_success_probability]
  exact success_ratio_lower r c U L htotal A hA hcount

/-- The bounded retry law is exactly uniform output mixed with its fixed
fallback. The mixture coefficient is the probability all trials fail. -/
theorem stationary_retry_mass (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] [Nonempty (Table r c)]
    (fallback X : Table r c) (n : ℕ) :
    (retryLaw (jointLaw r c U L) (stateTrial r c U L) fallback n).mass X =
      (1 - (1 - (Fintype.card (Table r c) : ℚ) /
        (Fintype.card (StateJoint r c U L) : ℚ))^n) * uniformMass (α := Table r c) +
      if X = fallback then (1 - (Fintype.card (Table r c) : ℚ) /
        (Fintype.card (StateJoint r c U L) : ℚ))^n else 0 := by
  have hN : (Fintype.card (Table r c) : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := Table r c)).ne'
  have he : 1 / (Fintype.card (StateJoint r c U L) : ℚ) =
      ((Fintype.card (Table r c) : ℚ) / (Fintype.card (StateJoint r c U L) : ℚ)) *
        uniformMass (α := Table r c) := by
    unfold uniformMass
    field_simp [hN]
  have hg : successMass (jointLaw r c U L) (stateTrial r c U L) =
      fun _ => ((Fintype.card (Table r c) : ℚ) /
        (Fintype.card (StateJoint r c U L) : ℚ)) * uniformMass (α := Table r c) := by
    funext Y
    rw [stationary_trial_mass]
    exact he
  rw [retryLaw_mass, stationary_failure_mass, hg]
  exact stationary_output_mass _ n fallback X

/-- Independent exact stationary trials have only geometric fallback error.
This theorem makes no assertion about a finite walk or completion bit cost. -/
theorem stationary_retry_variation (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (A : ℝ) (hA : 0 < A)
    (hcount : (Fintype.card (PaddedTables r c U L) : ℝ) ≤
      A * (Fintype.card (Table r c) : ℝ)) (fallback : Table r c) (n : ℕ) :
    letI := states_nonempty r c U L htotal
    letI := table_nonempty r c htotal
    (variation (retryLaw (jointLaw r c U L) (stateTrial r c U L) fallback n)
      (uniformLaw (α := Table r c)) : ℝ) ≤
        Real.exp (-(n : ℝ) /
          (A * (1 + (Fintype.card (Cells (firstPaperSmall r c U)) : ℝ)^2))) := by
  letI := states_nonempty r c U L htotal
  letI := table_nonempty r c htotal
  rw [jointLaw_uniform]
  exact uniform_partial_retry_exp _ _ fallback n _
    (stationary_success_lower r c U L htotal A hA hcount)

/-- The ordinary padded count bound for the actual ideal threshold set,
rewritten in the physical mass theorem's row/column coordinates. -/
theorem ideal_padded_count (r : I → ℕ) (c : J → ℕ) :
    (Fintype.card (PaddedTables r c (IdealOracleScales.cutoff (I := I) (J := J))
      (IdealOracleScales.padding (I := I) (J := J))) : ℝ) ≤
        2 * (Fintype.card (Table r c) : ℝ) := by
  have h := IdealOracleScales.ideal_large_padded_count_le_twice_original r c
  unfold IdealOracleScales.idealLarge at h
  rw [large_padding_rows, large_padding_columns] at h
  exact_mod_cast h

/-- The actual ideal-scale stationary success bound, retaining p rather
than the coarser dimension allowance. -/
theorem ideal_stationary_success_lower (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) :
    1 / (2 * (1 + (Fintype.card (Cells (firstPaperSmall r c
      (IdealOracleScales.cutoff (I := I) (J := J)))) : ℝ)^2)) ≤
      (Fintype.card (Table r c) : ℝ) /
        (Fintype.card (StateJoint r c (IdealOracleScales.cutoff (I := I) (J := J))
          (IdealOracleScales.padding (I := I) (J := J))) : ℝ) :=
  stationary_success_lower r c _ _ htotal 2 (by norm_num) (ideal_padded_count r c)

theorem ideal_stationary_success_probability_lower (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) :
    letI := states_nonempty r c (IdealOracleScales.cutoff (I := I) (J := J))
      (IdealOracleScales.padding (I := I) (J := J)) htotal
    1 / (2 * (1 + (Fintype.card (Cells (firstPaperSmall r c
      (IdealOracleScales.cutoff (I := I) (J := J)))) : ℝ)^2)) ≤
      (1 - failureMass (jointLaw r c (IdealOracleScales.cutoff (I := I) (J := J))
        (IdealOracleScales.padding (I := I) (J := J))) (stateTrial r c _ _) : ℝ) :=
  stationary_success_probability_lower r c _ _ htotal 2 (by norm_num) (ideal_padded_count r c)

/-- Ideal-scale rejection uses independent exact stationary completion
trials; it does not implement a finite walk or finite-bit completion oracle. -/
theorem ideal_stationary_retry_variation (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (fallback : Table r c) (n : ℕ) :
    letI := states_nonempty r c (IdealOracleScales.cutoff (I := I) (J := J))
      (IdealOracleScales.padding (I := I) (J := J)) htotal
    letI := table_nonempty r c htotal
    (variation (retryLaw (jointLaw r c (IdealOracleScales.cutoff (I := I) (J := J))
      (IdealOracleScales.padding (I := I) (J := J)))
      (stateTrial r c _ _) fallback n) (uniformLaw (α := Table r c)) : ℝ) ≤
        Real.exp (-(n : ℝ) / (2 * (1 + (Fintype.card (Cells (firstPaperSmall r c
          (IdealOracleScales.cutoff (I := I) (J := J)))) : ℝ)^2))) :=
  stationary_retry_variation r c _ _ htotal 2 (by norm_num) (ideal_padded_count r c) fallback n

end
end Math115.PhysicalStationaryLaw
