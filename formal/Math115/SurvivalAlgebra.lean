/-
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

/-!
# Survival bounds from a shifted hazard recurrence

The recurrence `F k * (a - k) ≤ F (k + 1) * (a - k + e)` implies both
a finite-product survival bound and a linear lower-tail bound. The parameters
may be real; natural-parameter wrappers match the shifted-fiber application.
All subtractions involving the index below are real subtractions.
-/

namespace Math115.SurvivalAlgebra

open scoped BigOperators

/-- One induction step for the linear survival estimate. The slack is exactly
`f₀ * e * k * (e - 1)`, which explains the assumption `1 ≤ e`. -/
lemma linear_survival_step (a e k f₀ fₖ fₖ₁ : ℝ)
    (he : 1 ≤ e) (hk : 0 ≤ k) (hka : k ≤ a) (hf₀ : 0 ≤ f₀)
    (hprev : f₀ * (a + e - k * e) ≤ fₖ * (a + e))
    (hrec : fₖ * (a - k) ≤ fₖ₁ * (a - k + e)) :
    f₀ * (a + e - (k + 1) * e) ≤ fₖ₁ * (a + e) := by
  have hden : 0 < a - k + e := by linarith
  have htotal : 0 ≤ a + e := by linarith
  have hslack : 0 ≤ f₀ * e * k * (e - 1) := by positivity
  apply (mul_le_mul_iff_left₀ hden).mp
  calc
    f₀ * (a + e - (k + 1) * e) * (a - k + e) ≤
        f₀ * (a + e - (k + 1) * e) * (a - k + e) +
          f₀ * e * k * (e - 1) := le_add_of_nonneg_right hslack
    _ = (f₀ * (a + e - k * e)) * (a - k) := by ring
    _ ≤ (fₖ * (a + e)) * (a - k) :=
      mul_le_mul_of_nonneg_right hprev (sub_nonneg.mpr hka)
    _ = (fₖ * (a - k)) * (a + e) := by ring
    _ ≤ (fₖ₁ * (a - k + e)) * (a + e) :=
      mul_le_mul_of_nonneg_right hrec htotal
    _ = (fₖ₁ * (a + e)) * (a - k + e) := by ring

/-- A linear survival bound from the recurrence. Only the initial value needs
to be nonnegative; the recurrence supplies all later comparisons. -/
theorem survival_linear_bound (a e : ℝ) (he : 1 ≤ e)
    (F : ℕ → ℝ) (hF₀ : 0 ≤ F 0) (t : ℕ) (ht : (t : ℝ) ≤ a)
    (hrec : ∀ k < t, F k * (a - k) ≤ F (k + 1) * (a - k + e)) :
    F 0 * (a + e - (t : ℝ) * e) ≤ F t * (a + e) := by
  revert ht hrec
  induction t with
  | zero =>
      intro _ _
      simp
  | succ k ih =>
      intro ht hrec
      have hk : (k : ℝ) ≤ a :=
        (Nat.cast_le.mpr (Nat.le_succ k)).trans ht
      have hprev := ih hk (fun j hj => hrec j (Nat.lt_trans hj (Nat.lt_succ_self k)))
      have hstep := linear_survival_step a e (k : ℝ) (F 0) (F k) (F (k + 1))
        he (Nat.cast_nonneg k) hk hF₀ hprev (hrec k (Nat.lt_succ_self k))
      simpa only [Nat.cast_succ] using hstep

/-- The lower-tail mass is at most `t * e / (a + e)` times the initial mass,
stated without division so a zero initial mass is permitted. -/
theorem lower_tail_linear_bound (a e : ℝ) (he : 1 ≤ e)
    (F : ℕ → ℝ) (hF₀ : 0 ≤ F 0) (t : ℕ) (ht : (t : ℝ) ≤ a)
    (hrec : ∀ k < t, F k * (a - k) ≤ F (k + 1) * (a - k + e)) :
    (F 0 - F t) * (a + e) ≤ F 0 * (t : ℝ) * e := by
  have h := survival_linear_bound a e he F hF₀ t ht hrec
  calc
    (F 0 - F t) * (a + e) = F 0 * (a + e) - F t * (a + e) := by ring
    _ ≤ F 0 * (a + e) - F 0 * (a + e - (t : ℝ) * e) := sub_le_sub_left h _
    _ = F 0 * (t : ℝ) * e := by ring

/-- The product survival bound requires only a nonnegative hazard parameter and
does not require a sign assumption on the sequence. -/
theorem survival_product_bound (a e : ℝ) (he : 0 ≤ e)
    (F : ℕ → ℝ) (t : ℕ) (ht : (t : ℝ) ≤ a)
    (hrec : ∀ k < t, F k * (a - k) ≤ F (k + 1) * (a - k + e)) :
    F 0 * (∏ k ∈ Finset.range t, ((a - k) / (a - k + e))) ≤ F t := by
  revert ht hrec
  induction t with
  | zero =>
      intro _ _
      simp
  | succ k ih =>
      intro ht hrec
      have hk_lt : (k : ℝ) < a :=
        (Nat.cast_lt.mpr (Nat.lt_succ_self k)).trans_le ht
      have hk : (k : ℝ) ≤ a :=
        hk_lt.le
      have hden : 0 < a - (k : ℝ) + e := by linarith
      have hratio : 0 ≤ (a - (k : ℝ)) / (a - (k : ℝ) + e) :=
        div_nonneg (sub_nonneg.mpr hk) hden.le
      have hprev := ih hk (fun j hj => hrec j (Nat.lt_trans hj (Nat.lt_succ_self k)))
      rw [Finset.prod_range_succ, ← mul_assoc]
      calc
        (F 0 * ∏ j ∈ Finset.range k, ((a - j) / (a - j + e))) *
            ((a - k) / (a - k + e)) ≤
            F k * ((a - k) / (a - k + e)) :=
          mul_le_mul_of_nonneg_right hprev hratio
        _ = (F k * (a - k)) / (a - k + e) := by ring
        _ ≤ F (k + 1) := (div_le_iff₀ hden).mpr (hrec k (Nat.lt_succ_self k))

/-- Natural-parameter form of the lower-tail bound, with recurrence available
up to the original margin `a`. -/
theorem nat_lower_tail_linear_bound (a e t : ℕ) (he : 1 ≤ e) (ht : t ≤ a)
    (F : ℕ → ℝ) (hF₀ : 0 ≤ F 0)
    (hrec : ∀ k < a,
      F k * ((a : ℝ) - k) ≤ F (k + 1) * ((a : ℝ) - k + e)) :
    (F 0 - F t) * ((a : ℝ) + e) ≤ F 0 * (t : ℝ) * e := by
  exact lower_tail_linear_bound a e (by exact_mod_cast he) F hF₀ t
    (by exact_mod_cast ht) (fun k hk => hrec k (lt_of_lt_of_le hk ht))

/-- Natural-parameter form of the finite-product survival estimate, including
the zero-hazard case `e = 0`. -/
theorem nat_survival_product_bound (a e t : ℕ) (ht : t ≤ a)
    (F : ℕ → ℝ)
    (hrec : ∀ k < a,
      F k * ((a : ℝ) - k) ≤ F (k + 1) * ((a : ℝ) - k + e)) :
    F 0 * (∏ k ∈ Finset.range t, (((a : ℝ) - k) / ((a : ℝ) - k + e))) ≤
      F t := by
  exact survival_product_bound a e (Nat.cast_nonneg e) F t
    (by exact_mod_cast ht) (fun k hk => hrec k (lt_of_lt_of_le hk ht))

/-- Telescoping the potential `F k * (a - k)` bounds the partial sum of
survival counts. No sign assumptions on the parameters or sequence are needed. -/
theorem survival_sum_bound (a e : ℝ) (F : ℕ → ℝ) (t : ℕ)
    (hrec : ∀ k < t, F k * (a - k) ≤ F (k + 1) * (a - k + e)) :
    F 0 * a ≤ F t * (a - (t : ℝ)) +
      (e + 1) * (∑ k ∈ Finset.range t, F (k + 1)) := by
  let G : ℕ → ℝ := fun k => F k * (a - (k : ℝ))
  have hstep : ∀ k ∈ Finset.range t,
      G k - G (k + 1) ≤ (e + 1) * F (k + 1) := by
    intro k hk
    have h := hrec k (Finset.mem_range.mp hk)
    dsimp [G]
    simp only [Nat.cast_add, Nat.cast_one]
    nlinarith only [h]
  have hsum := Finset.sum_le_sum hstep
  rw [Finset.sum_range_sub', ← Finset.mul_sum] at hsum
  simpa only [G, Nat.cast_zero, sub_zero] using (sub_le_iff_le_add').mp hsum

/-- At the natural endpoint `a`, the potential vanishes, giving the mean-tail
sum bound without sign assumptions on `e` or `F`. -/
theorem mean_tail_sum_bound (a : ℕ) (e : ℝ) (F : ℕ → ℝ)
    (hrec : ∀ k < a,
      F k * ((a : ℝ) - k) ≤ F (k + 1) * ((a : ℝ) - k + e)) :
    F 0 * (a : ℝ) ≤ (e + 1) * (∑ k ∈ Finset.range a, F (k + 1)) := by
  simpa using survival_sum_bound a e F a hrec

/-- Natural-parameter form of the mean-tail sum bound. -/
theorem nat_mean_tail_sum_bound (a e : ℕ) (F : ℕ → ℝ)
    (hrec : ∀ k < a,
      F k * ((a : ℝ) - k) ≤ F (k + 1) * ((a : ℝ) - k + e)) :
    F 0 * (a : ℝ) ≤ ((e : ℝ) + 1) * (∑ k ∈ Finset.range a, F (k + 1)) :=
  mean_tail_sum_bound a e F hrec

end Math115.SurvivalAlgebra
