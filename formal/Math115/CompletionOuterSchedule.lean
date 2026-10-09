import Math115.CompletionScheduleArithmetic
import Math115.PhysicalLatticeCompletion

namespace Math115.CompletionOuterSchedule

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open CompletionRetryBudget PhysicalFiniteWalk PhysicalCompletionOracle
open SmallGraphProfiles SmallContextCoordinates CompletionCounts
open scoped BigOperators

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

local notation "d" => CompletionCounts.dimensionAllowance (I := I) (J := J)
local notation "U" => IdealOracleScales.cutoff (I := I) (J := J)
local notation "L" => IdealOracleScales.padding (I := I) (J := J)

/-- The explicit schedule attains dyadic target accuracy for every actual
physical margin pair with equal totals, including empty index types. -/
theorem denseOuterLaw_explicit_accuracy_half (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (fallback : Table r c) (h : ℕ) :
    let p := physicalSmallCount r c
    let base := physicalMassBase (J := J) r
    letI := OAI.ContingencyTables.table_nonempty r c htotal
    (FirstSuccess.variation (PhysicalLatticeCompletion.denseOuterLaw r c htotal fallback
      (walkCount p d base h) (restartCount p h) (stepPrecision p d base h)
      (terminalPrecision p h)) (FirstSuccess.uniformLaw (α := Table r c)) : ℝ) ≤
      (dyadic (h + 1) : ℝ) := by
  let p := physicalSmallCount r c
  let base := physicalMassBase (J := J) r
  have hd : 1 ≤ d := by unfold CompletionCounts.dimensionAllowance; omega
  have hγ : (proposalAllowance d : ℝ) ≤ 1 := by
    have hh := proposalAllowance_le_half d hd
    have hhR : (proposalAllowance d : ℝ) ≤ 1 / 2 := by
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        ((Rat.cast_le (K := ℝ)).mpr hh)
    exact hhR.trans (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hbound := PhysicalLatticeCompletion.denseOuterLaw_variation r c htotal fallback
    (walkCount p d base h) (restartCount p h) (stepPrecision p d base h) (terminalPrecision p h)
  have heS : successAllowance r c U = (successFactor p : ℝ) := by
    simp only [successAllowance, successFactor, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat,
      Nat.cast_pow, p, physicalSmallCount]
  have heK : idealGapAllowance d = (gapFactor d : ℝ) := by
    simp only [idealGapAllowance, gapFactor, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow]
  have heB : massAllowance (J := J) r U L = (base : ℝ) ^ (2 * d) := by
    unfold massAllowance capacityBound
    congr 2
  rw [heS, heK, heB] at hbound
  exact hbound.trans (arithmetic_schedule_half p d base h hd (proposalAllowance d) hγ)

theorem denseOuterLaw_explicit_accuracy (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (fallback : Table r c) (h : ℕ) :
    let p := physicalSmallCount r c
    let base := physicalMassBase (J := J) r
    letI := OAI.ContingencyTables.table_nonempty r c htotal
    (FirstSuccess.variation (PhysicalLatticeCompletion.denseOuterLaw r c htotal fallback
      (walkCount p d base h) (restartCount p h) (stepPrecision p d base h)
      (terminalPrecision p h)) (FirstSuccess.uniformLaw (α := Table r c)) : ℝ) ≤
      (dyadic h : ℝ) := by
  exact (denseOuterLaw_explicit_accuracy_half r c htotal fallback h).trans
    (by exact_mod_cast dyadic_antitone_step h)

end

end Math115.CompletionOuterSchedule
