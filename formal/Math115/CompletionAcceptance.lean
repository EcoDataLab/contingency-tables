/-
SPDX-License-Identifier: Apache-2.0
Analytic and scalar counting implications for the completion oracle.
The volume/count comparison is an explicit input, not proved in this module.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic

namespace Math115.CompletionAcceptance

noncomputable section

lemma two_mul_le_power_twelve (d : ℕ) (hd : 2 ≤ d) : 2 * d ≤ d^12 := by
  have hsq : 2 * d ≤ d^2 := by nlinarith
  exact hsq.trans (Nat.pow_le_pow_right (by omega : 0 < d) (by decide : 2 ≤ 12))

def dilationFactor (d k : ℕ) : ℝ :=
  (3 * (d : ℝ) + 2 + 2 / (k : ℝ)) / (3 * (d : ℝ) - 2)

def increment (d k : ℕ) : ℝ :=
  (4 + 2 / (k : ℝ)) / (3 * (d : ℝ) - 2)

lemma denominator_positive (d : ℕ) (hd : 1 ≤ d) : 0 < 3 * (d : ℝ) - 2 := by
  have h : (1 : ℝ) ≤ d := by exact_mod_cast hd
  linarith

lemma dilationFactor_eq_one_add (d k : ℕ) (hd : 1 ≤ d) :
    dilationFactor d k = 1 + increment d k := by
  unfold dilationFactor increment
  field_simp [(denominator_positive d hd).ne']
  ring

lemma increment_nonnegative (d k : ℕ) (hd : 1 ≤ d) : 0 ≤ increment d k := by
  unfold increment
  apply div_nonneg _ (denominator_positive d hd).le
  positivity

theorem dilationFactor_positive (d k : ℕ) (hd : 1 ≤ d) :
    0 < dilationFactor d k := by
  rw [dilationFactor_eq_one_add d k hd]
  have h := increment_nonnegative d k hd
  linarith

lemma two_div_k_le_inverse_d (d k : ℕ) (hd : 1 ≤ d) (hk : 2 * d ≤ k) :
    2 / (k : ℝ) ≤ 1 / (d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hkd : 2 * (d : ℝ) ≤ k := by exact_mod_cast hk
  apply (div_le_div_iff₀ hkR hdR).mpr
  linarith

/-- The strong padding margins yield the exponent allowance 4/3. -/
theorem exponent_allowance (d e k : ℕ) (hd : 1 ≤ d) (he : e ≤ d - 1)
    (hk : 2 * d ≤ k) : (e : ℝ) * increment d k ≤ 4 / 3 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have heR : (e : ℝ) ≤ (d : ℝ) - 1 := by
    have h := (show (e : ℝ) ≤ ((d - 1 : ℕ) : ℝ) by exact_mod_cast he)
    simpa only [Nat.cast_sub hd, Nat.cast_one] using h
  have hnum := two_div_k_le_inverse_d d k hd hk
  have hden := denominator_positive d hd
  have hinc : increment d k ≤ (4 + 1 / (d : ℝ)) / (3 * (d : ℝ) - 2) := by
    unfold increment
    exact div_le_div_of_nonneg_right (by linarith) hden.le
  calc
    _ ≤ ((d : ℝ) - 1) * increment d k :=
      mul_le_mul_of_nonneg_right heR (increment_nonnegative d k hd)
    _ ≤ ((d : ℝ) - 1) * ((4 + 1 / (d : ℝ)) / (3 * (d : ℝ) - 2)) :=
      mul_le_mul_of_nonneg_left hinc (by linarith)
    _ ≤ 4 / 3 := by
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hden).mpr
      have heq : 4 + 1 / (d : ℝ) = (4 * (d : ℝ) + 1) / (d : ℝ) := by
        field_simp [hdR.ne']
      rw [heq, ← mul_div_assoc]
      apply (div_le_iff₀ hdR).mpr
      nlinarith

/-- A symbolic logarithm inequality supplies the strict numeric constant. -/
theorem exp_four_thirds_lt_four : Real.exp (4 / 3 : ℝ) < 4 := by
  have hlog : (2 / 3 : ℝ) < Real.log 2 := by
    have h := Real.lt_log_one_add_of_pos (x := (1 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 2 using 1 <;> norm_num
  apply (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 4)).mp
  linarith

/-- The concrete d,k,e hypotheses force the dilation volume ratio below four.
No table count or acceptance conclusion is used to establish this inequality. -/
theorem dilationFactor_pow_lt_four (d e k : ℕ) (hd : 1 ≤ d)
    (he : e ≤ d - 1) (hk : 2 * d ≤ k) : (dilationFactor d k)^e < 4 := by
  have hbase : dilationFactor d k ≤ Real.exp (increment d k) := by
    rw [dilationFactor_eq_one_add d k hd]
    linarith [Real.add_one_le_exp (increment d k)]
  calc
    _ ≤ (Real.exp (increment d k))^e :=
      pow_le_pow_left₀ (dilationFactor_positive d k hd).le hbase e
    _ = Real.exp ((e : ℝ) * increment d k) := (Real.exp_nat_mul _ _).symm
    _ ≤ Real.exp (4 / 3 : ℝ) :=
      Real.exp_le_exp.mpr (exponent_allowance d e k hd he hk)
    _ < 4 := exp_four_thirds_lt_four

/-- Scalar bridge from a supplied volume/count comparison and exact accepted
cardinality to ideal acceptance at least one quarter. -/
theorem acceptance_lower_real (d e k Nfine Noriginal Naccepted : ℕ)
    (hd : 1 ≤ d) (he : e ≤ d - 1) (hk : 2 * d ≤ k) (hFine : 0 < Nfine)
    (hAccepted : Naccepted = k^e * Noriginal)
    (hCount : (Nfine : ℝ) ≤ (dilationFactor d k)^e * (k : ℝ)^e * (Noriginal : ℝ)) :
    (1 / 4 : ℝ) ≤ (Naccepted : ℝ) / (Nfine : ℝ) := by
  have hFineR : (0 : ℝ) < Nfine := by exact_mod_cast hFine
  have hAcceptedR : (Naccepted : ℝ) = (k : ℝ)^e * (Noriginal : ℝ) := by
    exact_mod_cast hAccepted
  have hCount' : (Nfine : ℝ) ≤ (dilationFactor d k)^e * (Naccepted : ℝ) := by
    simpa only [hAcceptedR, mul_assoc] using hCount
  have hFour := mul_le_mul_of_nonneg_right
    (dilationFactor_pow_lt_four d e k hd he hk).le
    (show (0 : ℝ) ≤ Naccepted by positivity)
  apply (le_div_iff₀ hFineR).mpr
  linarith

/-- Rational-law-compatible version; the only analytic input beyond the
concrete schedule hypotheses is the explicitly supplied real count bound. -/
theorem acceptance_lower_rat (d e k Nfine Noriginal Naccepted : ℕ)
    (hd : 1 ≤ d) (he : e ≤ d - 1) (hk : 2 * d ≤ k) (hFine : 0 < Nfine)
    (hAccepted : Naccepted = k^e * Noriginal)
    (hCount : (Nfine : ℝ) ≤ (dilationFactor d k)^e * (k : ℝ)^e * (Noriginal : ℝ)) :
    (1 / 4 : ℚ) ≤ (Naccepted : ℚ) / (Nfine : ℚ) := by
  have h := acceptance_lower_real d e k Nfine Noriginal Naccepted hd he hk hFine hAccepted hCount
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Rat.cast_natCast] using h

end
end Math115.CompletionAcceptance
