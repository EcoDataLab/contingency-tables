import Mathlib.Tactic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Factorial.BigOperators
import Research.SurvivalConvolution

/-! Normalized weak-composition tails, proved directly from binomial products. -/

namespace Research.CompositionSurvival

open scoped BigOperators

noncomputable def tail (a q k : ℕ) : ℝ :=
  if k ≤ a then (Nat.choose (a - k + q) q : ℝ) / Nat.choose (a + q) q else 0

lemma denominator_pos (a q : ℕ) : 0 < (Nat.choose (a + q) q : ℝ) := by
  exact_mod_cast Nat.choose_pos (by omega : q ≤ a + q)

lemma tail_nonneg (a q k : ℕ) : 0 ≤ tail a q k := by
  unfold tail
  split_ifs <;> positivity

lemma tail_zero (a q : ℕ) : tail a q 0 = 1 := by
  simp [tail, ne_of_gt (denominator_pos a q)]

lemma tail_vanish (a q k : ℕ) (hak : a < k) : tail a q k = 0 := by
  simp [tail, Nat.not_le.mpr hak]

/-- Exact successor relation inside the positive support, stated with real
subtraction to match weighted switching recurrences. -/
theorem tail_succ_recurrence (a q k : ℕ) (hk : k < a) :
    ((a : ℝ) - (k : ℝ) + (q : ℝ)) * tail a q (k + 1) =
      ((a : ℝ) - (k : ℝ)) * tail a q k := by
  have hk0 : k ≤ a := by omega
  have hk1 : k + 1 ≤ a := by omega
  have hn : a - (k + 1) + q + 1 = a - k + q := by omega
  have hd : a - (k + 1) + q + 1 - q = a - k := by omega
  have h := Nat.choose_mul_succ_eq (a - (k + 1) + q) q
  rw [hd, hn] at h
  have hreal : (Nat.choose (a - (k + 1) + q) q : ℝ) * ((a - k + q : ℕ) : ℝ) =
      (Nat.choose (a - k + q) q : ℝ) * ((a - k : ℕ) : ℝ) := by
    exact_mod_cast h
  rw [Nat.cast_add, Nat.cast_sub hk0] at hreal
  simp only [tail, hk0, hk1, ite_true]
  calc
    ((a : ℝ) - k + q) * ((Nat.choose (a - (k + 1) + q) q : ℝ) /
        Nat.choose (a + q) q) =
      ((Nat.choose (a - (k + 1) + q) q : ℝ) * ((a : ℝ) - k + q)) /
        Nat.choose (a + q) q := by ring
    _ = ((Nat.choose (a - k + q) q : ℝ) * ((a : ℝ) - k)) /
        Nat.choose (a + q) q := by rw [hreal]
    _ = ((a : ℝ) - k) * ((Nat.choose (a - k + q) q : ℝ) /
        Nat.choose (a + q) q) := by ring

lemma choose_factorial_eq_product (m q : ℕ) :
    (Nat.choose (m + q) q : ℝ) * (Nat.factorial q : ℝ) =
      ∏ t ∈ Finset.range q, ((m : ℝ) + (t : ℝ) + 1) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose m q
  rw [Nat.ascFactorial_eq_prod_range] at h
  have h' : (∏ t ∈ Finset.range q, ((m + 1 + t : ℕ) : ℝ)) =
      (Nat.factorial q : ℝ) * (Nat.choose (m + q) q : ℝ) := by
    exact_mod_cast h
  rw [mul_comm, ← h']
  apply Finset.prod_congr rfl
  intro t _
  push_cast
  ring

/-- Binomial cross-product bound underlying NBU; no NBU hypothesis is assumed. -/
lemma choose_cross_le (a q i j : ℕ) (hij : i + j ≤ a) :
    (Nat.choose (a - (i + j) + q) q : ℝ) * Nat.choose (a + q) q ≤
      (Nat.choose (a - i + q) q : ℝ) * Nat.choose (a - j + q) q := by
  have hfac : 0 < (Nat.factorial q : ℝ) := by positivity
  apply (mul_le_mul_iff_right₀ (mul_pos hfac hfac)).mp
  have hprod :
      (∏ t ∈ Finset.range q, (((a - (i + j) : ℕ) : ℝ) + (t : ℝ) + 1)) *
        (∏ t ∈ Finset.range q, ((a : ℝ) + (t : ℝ) + 1)) ≤
      (∏ t ∈ Finset.range q, (((a - i : ℕ) : ℝ) + (t : ℝ) + 1)) *
        (∏ t ∈ Finset.range q, (((a - j : ℕ) : ℝ) + (t : ℝ) + 1)) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod₀
    · intro t _
      positivity
    · intro t _
      rw [Nat.cast_sub hij, Nat.cast_add,
        Nat.cast_sub (by omega : i ≤ a), Nat.cast_sub (by omega : j ≤ a)]
      nlinarith [mul_nonneg (Nat.cast_nonneg i : (0 : ℝ) ≤ i)
        (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  simp_rw [← choose_factorial_eq_product] at hprod
  convert hprod using 1 <;> ring

/-- Weak-composition tails are NBU, including their zero support boundary. -/
theorem tail_nbu (a q i j : ℕ) : tail a q (i + j) ≤ tail a q i * tail a q j := by
  by_cases hij : i + j ≤ a
  · have hi : i ≤ a := by omega
    have hj : j ≤ a := by omega
    simp only [tail, hij, hi, hj, ite_true]
    have hD := denominator_pos a q
    rw [div_mul_div_comm]
    apply (div_le_div_iff₀ hD (mul_pos hD hD)).mpr
    have h := choose_cross_le a q i j hij
    nlinarith [mul_le_mul_of_nonneg_right h hD.le]
  · rw [tail_vanish a q (i + j) (by omega)]
    exact mul_nonneg (tail_nonneg a q i) (tail_nonneg a q j)

/-- Hockey-stick identity for the unnormalized tail numerators. -/
lemma sum_choose_reversed (a q : ℕ) :
    (∑ k ∈ Finset.range (a + 1), Nat.choose (a - k + q) q) =
      Nat.choose (a + q + 1) (q + 1) := by
  have h := Finset.sum_range_reflect (fun k => Nat.choose (k + q) q) (a + 1)
  simp only [Nat.add_sub_cancel] at h
  rw [h]
  exact Nat.sum_range_add_choose a q

/-- Exact finite tail mean, including the degenerate case `q = 0`. -/
theorem tail_sum (a q : ℕ) :
    (∑ k ∈ Finset.range (a + 1), tail a q k) =
      ((a : ℝ) + (q : ℝ) + 1) / ((q : ℝ) + 1) := by
  calc
    (∑ k ∈ Finset.range (a + 1), tail a q k) =
        (∑ k ∈ Finset.range (a + 1), (Nat.choose (a - k + q) q : ℝ)) /
          (Nat.choose (a + q) q : ℝ) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [tail, show k ≤ a by have := Finset.mem_range.mp hk; omega, ite_true]
    _ = (Nat.choose (a + q + 1) (q + 1) : ℝ) / Nat.choose (a + q) q := by
      congr 1
      exact_mod_cast sum_choose_reversed a q
    _ = ((a : ℝ) + (q : ℝ) + 1) / ((q : ℝ) + 1) := by
      apply (div_eq_div_iff (ne_of_gt (denominator_pos a q)) (by positivity)).mpr
      have h := Nat.add_one_mul_choose_eq (a + q) q
      have h' : ((a : ℝ) + (q : ℝ) + 1) * (Nat.choose (a + q) q : ℝ) =
          (Nat.choose (a + q + 1) (q + 1) : ℝ) * ((q : ℝ) + 1) := by
        exact_mod_cast h
      exact h'.symm

/-- Any common cutoff beyond the support has the same exact mean. -/
theorem tail_sum_of_lt (a q n : ℕ) (han : a < n) :
    (∑ k ∈ Finset.range n, tail a q k) =
      ((a : ℝ) + (q : ℝ) + 1) / ((q : ℝ) + 1) := by
  have h := Finset.sum_range_add_sum_Ico (tail a q) (by omega : a + 1 ≤ n)
  have hz : (∑ k ∈ Finset.Ico (a + 1) n, tail a q k) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact tail_vanish a q k (by have := (Finset.mem_Ico.mp hk).1; omega)
  rw [hz, add_zero, tail_sum] at h
  exact h.symm

/-- The convolution reciprocal bound instantiated with actual
weak-composition tails and their proved closed means. The cutoff is beyond
both finite supports; the two tail dimensions may differ. -/
theorem composition_reciprocal_bound (a b q p n : ℕ) (han : a < n) (hbn : b < n) :
    1 / (∑ k ∈ Finset.range n, tail a q k * tail b p k) ≤
      ((q : ℝ) + 1) / ((a : ℝ) + (q : ℝ) + 1) +
        ((p : ℝ) + 1) / ((b : ℝ) + (p : ℝ) + 1) -
        (((q : ℝ) + 1) * ((p : ℝ) + 1)) /
          (((a : ℝ) + (q : ℝ) + 1) * ((b : ℝ) + (p : ℝ) + 1)) := by
  have h := SurvivalConvolution.finite_nbu_reciprocal
    (tail a q) (tail b p) (tail_nonneg a q) (tail_nonneg b p)
    (tail_zero a q) (tail_zero b p) (tail_nbu a q) (tail_nbu b p) n (by omega)
  rw [tail_sum_of_lt a q n han, tail_sum_of_lt b p n hbn] at h
  simpa only [div_mul_div_comm, one_div_div] using h

#print axioms tail_nbu
#print axioms tail_succ_recurrence
#print axioms tail_sum
#print axioms composition_reciprocal_bound

end Research.CompositionSurvival
