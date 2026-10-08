/-
SPDX-License-Identifier: Apache-2.0

An exact rational majorant for sequential padding growth.  This proof uses
only finite induction and ordered-field arithmetic; no exponential or
logarithm estimate is assumed.
-/
import Mathlib.Tactic

namespace Math115.PaddingGrowthAlgebra

/-- The rational envelope `1 + t + t² / (2 (1 - t/3))`, written with a
single denominator to make its finite-step certificate explicit. -/
noncomputable def envelope (t : ℝ) : ℝ := (t ^ 2 + 4 * t + 6) / (6 - 2 * t)

theorem envelope_eq (t : ℝ) (ht : t ≠ 3) :
    envelope t = 1 + t + t ^ 2 / (2 * (1 - t / 3)) := by
  unfold envelope
  have h : 6 - 2 * t ≠ 0 := by intro h; apply ht; linarith
  rw [show 2 * (1 - t / 3) = (6 - 2 * t) / 3 by ring, div_div_eq_mul_div]
  apply (div_eq_iff h).mpr
  rw [add_mul, div_mul_cancel₀ _ h]
  ring

/-- The numerator of the finite-step slack is
`2 x t³ + x² (2 t² + 6 t + 18)`, which is nonnegative. -/
theorem envelope_step (t x : ℝ) (ht : 0 ≤ t) (hx : 0 ≤ x)
    (htx : t + x < 3) :
    envelope t * (1 + x) ≤ envelope (t + x) := by
  have hd : 0 < 6 - 2 * t := by linarith
  have hd' : 0 < 6 - 2 * (t + x) := by linarith
  unfold envelope
  rw [div_mul_eq_mul_div]
  apply (div_le_div_iff₀ hd hd').mpr
  have hslack : 0 ≤ 2 * x * t ^ 3 + x ^ 2 * (2 * t ^ 2 + 6 * t + 18) := by
    positivity
  nlinarith only [hslack]

/-- A rational bound for every finite power, including exponent zero. -/
theorem one_add_pow_le_envelope (q : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hqx : (q : ℝ) * x < 3) :
    (1 + x) ^ q ≤ envelope ((q : ℝ) * x) := by
  revert hqx
  induction q with
  | zero => intro _; norm_num [envelope]
  | succ q ih =>
      intro hqx
      have hprev : (q : ℝ) * x < 3 := by
        push_cast at hqx
        nlinarith only [hqx, hx]
      have hnext : (q : ℝ) * x + x < 3 := by
        push_cast at hqx
        nlinarith only [hqx]
      calc
        (1 + x) ^ (q + 1) = (1 + x) ^ q * (1 + x) := pow_succ _ _
        _ ≤ envelope ((q : ℝ) * x) * (1 + x) :=
          mul_le_mul_of_nonneg_right (ih hprev) (by linarith)
        _ ≤ envelope ((q : ℝ) * x + x) :=
          envelope_step _ x (by positivity) hx hnext
        _ = envelope (((q + 1 : ℕ) : ℝ) * x) := by congr 1; push_cast; ring

/-- The explicit envelope value used by the `47 d⁵` scale. -/
theorem envelope_32_div_47 : envelope (32 / 47) = 10147 / 5123 := by
  norm_num [envelope]

theorem envelope_le_10147_div_5123 (t : ℝ) (ht : 0 ≤ t) (hbound : t ≤ 32 / 47) :
    envelope t ≤ 10147 / 5123 := by
  have hden : 0 < 6 - 2 * t := by linarith
  have hsq : t ^ 2 ≤ (32 / 47 : ℝ) ^ 2 := by nlinarith
  unfold envelope
  apply (div_le_iff₀ hden).mpr
  nlinarith only [hsq, hbound]

/-- A uniform finite-power certificate, with a strict margin below two. -/
theorem one_add_pow_le_10147_div_5123 (q : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hqx : (q : ℝ) * x ≤ 32 / 47) :
    (1 + x) ^ q ≤ 10147 / 5123 :=
  (one_add_pow_le_envelope q x hx (by linarith)).trans
    (envelope_le_10147_div_5123 _ (by positivity) hqx)

theorem one_add_pow_lt_two (q : ℕ) (x : ℝ) (hx : 0 ≤ x)
    (hqx : (q : ℝ) * x ≤ 32 / 47) : (1 + x) ^ q < 2 :=
  (one_add_pow_le_10147_div_5123 q x hx hqx).trans_lt (by norm_num)

/-- Turn the natural count recurrence into a twice-original bound. The
budget has no division, and `U + 1` is positive even when `U = 0`.
Neither original nor enlarged counts are assumed positive. -/
theorem count_le_twice_of_growth (enlarged original q U e : ℕ)
    (hgrowth : enlarged * (U + 1) ^ q ≤ original * (U + 1 + e) ^ q)
    (hbudget : 47 * q * e ≤ 32 * (U + 1)) : enlarged ≤ 2 * original := by
  let D : ℝ := U + 1
  let x : ℝ := e / D
  have hD : 0 < D := by dsimp [D]; positivity
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hbudgetR : (47 : ℝ) * q * e ≤ 32 * D := by
    dsimp only [D]
    exact_mod_cast hbudget
  have hqx : (q : ℝ) * x ≤ 32 / 47 := by
    dsimp [x]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hD).mpr
    nlinarith only [hbudgetR]
  have hpow := (one_add_pow_lt_two q x hx hqx).le
  have hbase : (U : ℝ) + 1 + e = (1 + x) * D := by
    dsimp only [x]
    rw [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hD)]
  have hcount : (enlarged : ℝ) * D ^ q ≤ (original : ℝ) * ((U : ℝ) + 1 + e) ^ q := by
    dsimp only [D]
    exact_mod_cast hgrowth
  rw [hbase, mul_pow] at hcount
  have hcancel : (enlarged : ℝ) ≤ (original : ℝ) * (1 + x) ^ q := by
    apply (mul_le_mul_iff_left₀ (pow_pos hD q)).mp
    simpa only [mul_assoc] using hcount
  have hfinal : (enlarged : ℝ) ≤ 2 * (original : ℝ) :=
    hcancel.trans (by nlinarith only [mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg original)])
  exact_mod_cast hfinal

end Math115.PaddingGrowthAlgebra
