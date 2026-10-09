/-
SPDX-License-Identifier: Apache-2.0
Adapted from OpenAI's IntegerRootEstimate.root_coefficient_after_repair at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Changes: generalize the repaired auxiliary coefficient and export its sharper
quarter-bound specialization independently of the upstream proof tree.
-/
import Math115.QuadraticCoefficient

namespace Math115

theorem min_mass_repair_bound (s t c Q : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hc : c ≤ Q * max s t) :
    min s t * (1 / s + 1 / t + 2 * c / (s * t)) ≤ 2 + 2 * Q := by
  have hmul : min s t * max s t = s * t := min_mul_max s t
  have hmin : 0 < min s t := lt_min hs ht
  have hratio : min s t * (1 / s + 1 / t) ≤ 2 := by
    have ha : min s t / s ≤ 1 := (div_le_one hs).mpr (min_le_left _ _)
    have hb : min s t / t ≤ 1 := (div_le_one ht).mpr (min_le_right _ _)
    calc
      _ = min s t / s + min s t / t := by ring
      _ ≤ 2 := by linarith
  have haux : min s t * c / (s * t) ≤ Q := by
    apply (div_le_iff₀ (mul_pos hs ht)).mpr
    calc
      _ ≤ min s t * (Q * max s t) := mul_le_mul_of_nonneg_left hc hmin.le
      _ = _ := by rw [mul_left_comm, hmul]
  calc
    _ = min s t * (1 / s + 1 / t) + 2 * (min s t * c / (s * t)) := by ring
    _ ≤ 2 + 2 * Q := by linarith

theorem min_mass_quarter_repair_bound (s t c : ℝ) (U d : ℕ)
    (hs : 0 < s) (ht : 0 < t) (hc : c ≤ (d : ℝ) * max s t) :
    min s t * (1 / s + 1 / t + (((U : ℝ) + 1)^2 / 2) * c / (s * t)) ≤
      2 + (d : ℝ) * ((U : ℝ) + 1)^2 / 2 := by
  have hscaled : (((U : ℝ) + 1)^2 / 4) * c ≤
      ((((U : ℝ) + 1)^2 / 4) * (d : ℝ)) * max s t := by
    have h := mul_le_mul_of_nonneg_left hc
      (show 0 ≤ (((U : ℝ) + 1)^2 / 4) by positivity)
    simpa only [mul_assoc] using h
  have h := min_mass_repair_bound s t ((((U : ℝ) + 1)^2 / 4) * c)
    ((((U : ℝ) + 1)^2 / 4) * (d : ℝ)) hs ht hscaled
  convert h using 1 <;> ring

end Math115
