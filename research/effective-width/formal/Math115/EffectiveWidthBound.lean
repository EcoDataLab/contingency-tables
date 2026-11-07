import Math115.PhysicalRepairRefinement

namespace Math115.EffectiveWidthBound

open Math115.PhysicalRepairRefinement Math115.PhysicalFullVariance

/-- Keep the negative linear term in the actual cell-count coefficient. -/
lemma transversal_actual_width (p V : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V) :
    transversalConstant p V ≤ ((27 * (p : ℝ) - 15) / 32) * (V : ℝ)^4 := by
  have hpR : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hVR : (2 : ℝ) ≤ V := by exact_mod_cast hV
  have hT : (V : ℝ) * ((V : ℝ) + 1) / 2 ≤ 3 / 4 * (V : ℝ)^2 := by
    nlinarith only [hVR, sq_nonneg ((V : ℝ) - 2)]
  have hq : ((V : ℝ) + 1)^2 ≤ 9 / 4 * (V : ℝ)^2 := by
    nlinarith only [hVR, sq_nonneg ((V : ℝ) - 2)]
  have hV2 : (4 : ℝ) ≤ (V : ℝ)^2 := by
    nlinarith only [hVR, sq_nonneg ((V : ℝ) - 2)]
  have hinner : 2 + ((p - 1 : ℕ) : ℝ) * ((V : ℝ) + 1)^2 / 2 ≤
      ((9 * (p : ℝ) - 5) / 8) * (V : ℝ)^2 := by
    rw [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
    have hm := mul_le_mul_of_nonneg_left hq (show 0 ≤ (p : ℝ) - 1 by linarith)
    nlinarith only [hm, hV2]
  unfold transversalConstant
  calc
    _ ≤ (3 / 4 * (V : ℝ)^2) * (((9 * (p : ℝ) - 5) / 8) * (V : ℝ)^2) :=
      mul_le_mul hT hinner (by positivity) (by positivity)
    _ = _ := by ring

/-- Bound the square-root term by squaring a nonnegative candidate bound. -/
lemma refined_coefficient (p V : ℕ) (a s : ℝ) (hV : 2 ≤ V) (hs : 0 ≤ s)
    (hC : transversalConstant p V ≤ a * (V : ℝ)^4) (ha : a ≤ s^2) :
    refinedConstant p V ≤
      ((1 + (p : ℝ)^2) * a + (p : ℝ) * s / 2 + 1 / 16) * (V : ℝ)^4 := by
  have hVR : (2 : ℝ) ≤ V := by exact_mod_cast hV
  have hV2 : (4 : ℝ) ≤ (V : ℝ)^2 := by
    nlinarith only [hVR, sq_nonneg ((V : ℝ) - 2)]
  have hV4 : (16 : ℝ) ≤ (V : ℝ)^4 := by
    nlinarith only [hV2, sq_nonneg ((V : ℝ)^2 - 4)]
  have hscale : (V : ℝ)^2 ≤ (V : ℝ)^4 / 4 := by
    nlinarith only [hV2, sq_nonneg ((V : ℝ)^2 - 4)]
  have hroot : Real.sqrt ((p : ℝ)^2 * transversalConstant p V) ≤
      (p : ℝ) * s * (V : ℝ)^2 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (p : ℝ)^2 * (a * (V : ℝ)^4) :=
        mul_le_mul_of_nonneg_left hC (sq_nonneg _)
      _ ≤ (p : ℝ)^2 * (s^2 * (V : ℝ)^4) := by gcongr
      _ = _ := by ring
  have hcross : 2 * Real.sqrt ((p : ℝ)^2 * transversalConstant p V) ≤
      ((p : ℝ) * s / 2) * (V : ℝ)^4 := by
    have hm := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 2 * (p : ℝ) * s by positivity)
    nlinarith only [hroot, hm]
  have hunit : (1 : ℝ) ≤ (V : ℝ)^4 / 16 := by linarith only [hV4]
  have hmass := mul_le_mul_of_nonneg_left hC (show 0 ≤ 1 + (p : ℝ)^2 by positivity)
  have hsq := Real.sq_sqrt (mul_nonneg (sq_nonneg (p : ℝ)) (transversalConstant_nonnegative p V))
  unfold refinedConstant
  nlinarith only [hmass, hcross, hunit, hsq]

/-- Actual-width envelope, including all small widths without an auxiliary d≥11. -/
theorem refinedConstant_le_actual_width (p V : ℕ) (hp : 2 ≤ p) (hV : 2 ≤ V) :
    refinedConstant p V ≤ (p : ℝ)^3 * (V : ℝ)^4 := by
  have hC := transversal_actual_width p V hp hV
  by_cases hp2 : p = 2
  · subst p
    norm_num at hC
    have h := refined_coefficient 2 V (39 / 32) (5 / 4) hV (by norm_num)
      (by simpa using hC) (by norm_num)
    norm_num at h ⊢
    nlinarith only [h, (show 0 ≤ (V : ℝ)^4 by positivity)]
  · have hp3 : 3 ≤ p := by omega
    have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
    have ha : (27 * (p : ℝ) - 15) / 32 ≤ (p : ℝ)^2 := by
      nlinarith only [hpR, sq_nonneg ((p : ℝ) - 1)]
    have h := refined_coefficient p V ((27 * (p : ℝ) - 15) / 32) (p : ℝ)
      hV (Nat.cast_nonneg _) hC ha
    have ht : 0 ≤ (p : ℝ) - 3 := by linarith
    have hpoly : 0 ≤ 58 + 102 * ((p : ℝ) - 3) + 44 * ((p : ℝ) - 3)^2 +
        5 * ((p : ℝ) - 3)^3 := by positivity
    have hcoef : (1 + (p : ℝ)^2) * ((27 * (p : ℝ) - 15) / 32) +
        (p : ℝ) * (p : ℝ) / 2 + 1 / 16 ≤ (p : ℝ)^3 := by
      nlinarith only [hpoly]
    exact h.trans (mul_le_mul_of_nonneg_right hcoef (by positivity))

end Math115.EffectiveWidthBound

#print axioms Math115.EffectiveWidthBound.refinedConstant_le_actual_width
