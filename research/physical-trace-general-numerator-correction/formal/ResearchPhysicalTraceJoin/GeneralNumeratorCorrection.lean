/-
SPDX-License-Identifier: Apache-2.0
Generic valid-numerator correction of the actual scheduled joint draw.
The augmented numerator gives an ideal success allowance of 1/(2p).
Current raw sampler definitions and their existing c0 remain unchanged.
-/
import ResearchPhysicalTraceJoin.GeneralAugmentedLower
import ResearchPhysicalTraceJoin.GeneralCorrectedRetry

set_option maxHeartbeats 1000000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open FirstSuccess ResidualMixture FairBits CompletionCounts
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.CompletionRetryBudget
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)

/-- The same clipped reciprocal-fibre correction, with an explicit
shape-dependent numerator. The numerator does not depend on the output. -/
def terminalNumeratorIdealLaw [Nonempty (DefectJoint r c U L)] (C : ℕ) :
    RationalLaw (Option (Table r c)) :=
  bindLaw (uniformLaw (α := DefectJoint r c U L))
    (terminalIdealCorrectionRow r c U L C)

/-- A valid common numerator makes every ordinary-table mass exactly C/Z. -/
theorem terminalNumeratorIdeal_mass [Nonempty (DefectJoint r c U L)]
    (C : ℕ) (hC : ∀ X : Table r c, C ≤ terminalInverseCount r c U L X)
    (X : Table r c) :
    (terminalNumeratorIdealLaw r c U L C).mass (some X) =
      (C : ℚ) / Fintype.card (DefectJoint r c U L) :=
  terminalIdealCorrection_mass_of_le r c U L C X (hC X)

/-- Exact ideal success, including C=0. No success premise is supplied. -/
theorem terminalNumeratorIdeal_success [Nonempty (DefectJoint r c U L)]
    (C : ℕ) (hC : ∀ X : Table r c, C ≤ terminalInverseCount r c U L X) :
    1 - (terminalNumeratorIdealLaw r c U L C).mass none =
      (Fintype.card (Table r c) : ℚ) * C / Fintype.card (DefectJoint r c U L) := by
  let law := terminalNumeratorIdealLaw r c U L C
  have ht := success_failure_total law id
  have hs (X : Table r c) : successMass law id X =
      (C : ℚ) / Fintype.card (DefectJoint r c U L) := by
    simpa only [successMass, id_eq, Option.some.injEq, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] using terminalNumeratorIdeal_mass r c U L C hC X
  have hf : failureMass law id = law.mass none := by simp [failureMass]
  simp only [hs, hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ht
  change 1 - law.mass none = _
  rw [← mul_div_assoc] at ht
  linarith

variable (hrLarge : 0 < (largeIndices (U,List.ofFn r)).length)
variable (hcLarge : 0 < (largeIndices (U,List.ofFn c)).length)

/-- Actual scheduled endpoint followed by an independent fresh bounded-bit
coin with numerator C. Padding failures remain none, with no conditioning. -/
def terminalNumeratorTrialLaw (C : ℕ) (start : DefectVertices r c U L) (h k : ℕ) :
    RationalLaw (Option (Table r c)) :=
  bindLaw
    (mapLaw (uniformLaw (α := Fin (terminalScheduleWordWidth r c U L h) → Bool))
      (terminalScheduleWord r c U L hrLarge hcLarge start h))
    (fun a => PartialRepairCorrection.finiteRow (terminalPartialRepair r c U L a)
      (terminalListedCount r c U) k C)

/-- Generic bounded-coin error, on the whole Option-valued trial law.
The numerator requires no extra premise for this approximation theorem. -/
theorem terminalNumeratorTrial_accuracy [Nonempty (DefectVertices r c U L)]
    (htotal : (∑ i, r i) = ∑ j, c j) (hU : 2 ≤ U) (hL : 7 ≤ L)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (C : ℕ) (start : DefectVertices r c U L) (h k : ℕ) :
    variation (terminalNumeratorTrialLaw r c U L hrLarge hcLarge C start h k)
      (terminalNumeratorIdealLaw r c U L C) ≤ dyadic h + dyadic k := by
  let p := mapLaw (uniformLaw (α := Fin (terminalScheduleWordWidth r c U L h) → Bool))
    (terminalScheduleWord r c U L hrLarge hcLarge start h)
  let q := uniformLaw (α := DefectJoint r c U L)
  have hw := terminalScheduleWord_accuracy r c U L hrLarge hcLarge htotal hU hL hp start h
  have hwQ : variation p q ≤ dyadic h := (Rat.cast_le (K := ℝ)).mp hw
  have hb := PartialRepairCorrection.finiteRow_bind_variation
    (terminalPartialRepair r c U L) (terminalListedCount r c U)
    (fun X => terminalListedCount_eq_terminalInverseCount r c U L (by omega) X)
    k C p q
  have hsum : variation p q + dyadic k ≤ dyadic h + dyadic k := by linarith
  exact hb.trans hsum

def terminalNumeratorRetryLaw (C : ℕ) (start : DefectVertices r c U L) (h k : ℕ)
    (fallback : Table r c) (R : ℕ) : RationalLaw (Table r c) :=
  retryLaw (terminalNumeratorTrialLaw r c U L hrLarge hcLarge C start h k) id fallback R

/-- The existing generic retry theorem applies to every valid common
numerator. All count and success premises are explicit at this reusable seam. -/
theorem terminalNumeratorRetry_accuracy [Nonempty (DefectVertices r c U L)]
    (htotal : (∑ i, r i) = ∑ j, c j) (hU : 2 ≤ U) (hL : 7 ≤ L)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (C : ℕ) (hC : ∀ X : Table r c, C ≤ terminalInverseCount r c U L X)
    (start : DefectVertices r c U L) (h k : ℕ) (fallback : Table r c) (R : ℕ)
    (s : ℚ) (hs : s ≤ 1 - (terminalNumeratorIdealLaw r c U L C).mass none) :
    letI : Nonempty (Table r c) := ⟨fallback⟩
    variation (terminalNumeratorRetryLaw r c U L hrLarge hcLarge C start h k fallback R)
      (uniformLaw (α := Table r c)) ≤
        (1 - s)^R + (R : ℚ) * (dyadic h + dyadic k) := by
  letI : Nonempty (Table r c) := ⟨fallback⟩
  have hequal (X : Table r c) : successMass (terminalNumeratorIdealLaw r c U L C) id X =
      (C : ℚ) / Fintype.card (DefectJoint r c U L) := by
    simpa only [successMass, id_eq, Option.some.injEq, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true] using terminalNumeratorIdeal_mass r c U L C hC X
  have hf : failureMass (terminalNumeratorIdealLaw r c U L C) id =
      (terminalNumeratorIdealLaw r c U L C).mass none := by simp [failureMass]
  exact approximate_retry_variation_of_success
    (terminalNumeratorTrialLaw r c U L hrLarge hcLarge C start h k)
    (terminalNumeratorIdealLaw r c U L C) id _ hequal fallback R
    (dyadic h + dyadic k) s
    (terminalNumeratorTrial_accuracy r c U L hrLarge hcLarge htotal hU hL hp C start h k)
    (by rwa [hf])

/-- The proved ordinary support bound discharges the new numerator's
validity for the actual partial-repair fibre. -/
theorem terminalAugmentedNumerator_le_count (hL : 1 ≤ L)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) (X : Table r c) :
    augmentedInverseSupportAllowance r c U ≤ terminalInverseCount r c U L X := by
  rw [terminalInverseCount_eq_supportCount r c U L hL X]
  exact augmentedInverseSupportAllowance_le_count r c U X hr hc

/-- Pure ratio improvement; the nontrivial branch's p>=2 is substantive. -/
theorem augmentedInverseSupportAllowance_ratio_lower
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U))) :
    let p := Fintype.card (Cells (firstPaperSmall r c U))
    1 / (2 * (p : ℚ)) ≤
      (augmentedInverseSupportAllowance r c U : ℚ) / ((2 * (p * (p - 1)) : ℕ) : ℚ) := by
  dsimp only
  let p := Fintype.card (Cells (firstPaperSmall r c U))
  let C := augmentedInverseSupportAllowance r c U
  have hC : p - 1 ≤ C := le_max_right _ _
  have hpQ : (0 : ℚ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1Q : (0 : ℚ) < p - 1 := by
    have h : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
    linarith
  have hCQ : (p : ℚ) - 1 ≤ C := by
    have h := (Nat.cast_le (α := ℚ)).mpr hC
    simpa only [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one] using h
  change 1 / (2 * (p : ℚ)) ≤ (C : ℚ) / ((2 * (p * (p - 1)) : ℕ) : ℚ)
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul,
    Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

local notation "cutoff" => 11 * dimensionAllowance (I := Fin m) (J := Fin n) * (m + n - 2)
local notation "p" => Fintype.card (Cells (firstPaperSmall r c cutoff))

/-- Reuse the checked total-joint count bound for any valid numerator. -/
theorem actualShape_terminalNumerator_success_lower
    [Nonempty (DefectJoint r c cutoff 7)]
    (C : ℕ) (hC : ∀ X : Table r c, C ≤ terminalInverseCount r c cutoff 7 X) :
    (C : ℚ) / ((2 * (p * (p - 1)) : ℕ) : ℚ) ≤
      1 - (terminalNumeratorIdealLaw r c cutoff 7 C).mass none := by
  let D := 2 * (p * (p - 1))
  have hZ : 0 < Fintype.card (DefectJoint r c cutoff 7) := Fintype.card_pos
  have hb := actualShape_defectJoint_card_le r c
  change Fintype.card (DefectJoint r c cutoff 7) ≤ D * Fintype.card (Table r c) at hb
  have hD : 0 < D := Nat.pos_of_mul_pos_right (hZ.trans_le hb)
  have hDR : (0 : ℚ) < D := by exact_mod_cast hD
  have hZR : (0 : ℚ) < Fintype.card (DefectJoint r c cutoff 7) := by exact_mod_cast hZ
  rw [terminalNumeratorIdeal_success r c cutoff 7 C hC]
  apply (div_le_div_iff₀ hDR hZR).mpr
  have hbR : (Fintype.card (DefectJoint r c cutoff 7) : ℚ) ≤
      (D : ℚ) * Fintype.card (Table r c) := by exact_mod_cast hb
  have h := mul_le_mul_of_nonneg_left hbR (Nat.cast_nonneg C : (0 : ℚ) ≤ _)
  calc
    (C : ℚ) * Fintype.card (DefectJoint r c cutoff 7) ≤
        (C : ℚ) * ((D : ℚ) * Fintype.card (Table r c)) := h
    _ = _ := by ring

/-- At the actual cutoff and L=7, the augmented correction's ideal success
is at least 1/(2p), without a supplied success or counting premise. -/
theorem actualShape_terminalAugmented_success_lower
    [Nonempty (DefectJoint r c cutoff 7)]
    (hp : 2 ≤ p) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j) :
    1 / (2 * (p : ℚ)) ≤
      1 - (terminalNumeratorIdealLaw r c cutoff 7
        (augmentedInverseSupportAllowance r c cutoff)).mass none :=
  (augmentedInverseSupportAllowance_ratio_lower r c cutoff hp).trans
    (actualShape_terminalNumerator_success_lower r c
      (augmentedInverseSupportAllowance r c cutoff)
      (terminalAugmentedNumerator_le_count r c cutoff 7 (by decide) hr hc))

/-- Concrete improved retry error for the new acceptance law. This does
not alter the existing raw program, reserve widths, or schedule definitions. -/
theorem actualShape_terminalAugmentedRetry_accuracy
    (hrLarge : 0 < (largeIndices (cutoff,List.ofFn r)).length)
    (hcLarge : 0 < (largeIndices (cutoff,List.ofFn c)).length)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (htotal : (∑ i, r i) = ∑ j, c j)
    (hp : 2 ≤ p) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (start : DefectVertices r c cutoff 7) (h k : ℕ) (fallback : Table r c) (R : ℕ) :
    letI : Nonempty (Table r c) := ⟨fallback⟩
    variation (terminalNumeratorRetryLaw r c cutoff 7 hrLarge hcLarge
      (augmentedInverseSupportAllowance r c cutoff) start h k fallback R)
      (uniformLaw (α := Table r c)) ≤
        (1 - 1 / (2 * (p : ℚ)))^R + (R : ℚ) * (dyadic h + dyadic k) := by
  letI : Nonempty (Table r c) := ⟨fallback⟩
  letI : Nonempty (DefectVertices r c cutoff 7) := ⟨start⟩
  have hd : 11 ≤ dimensionAllowance (I := Fin m) (J := Fin n) :=
    Math115.PhysicalRepairRefinement.dimension_at_least_eleven
  have hU : 2 ≤ cutoff := by
    have hmul := Nat.mul_le_mul
      (show 1 ≤ 11 * dimensionAllowance (I := Fin m) (J := Fin n) by omega)
      (show 2 ≤ m + n - 2 by omega)
    simpa only [one_mul] using hmul
  exact terminalNumeratorRetry_accuracy r c cutoff 7 hrLarge hcLarge
    htotal hU (by decide) hp (augmentedInverseSupportAllowance r c cutoff)
    (terminalAugmentedNumerator_le_count r c cutoff 7 (by decide) hr hc)
    start h k fallback R _ (actualShape_terminalAugmented_success_lower r c hp hr hc)

end
end Math115.PhysicalTraceJoin
