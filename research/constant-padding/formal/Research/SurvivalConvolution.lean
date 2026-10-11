import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# A finite NBU convolution bound

Nonnegative normalized sequences with the NBU property
`F (a + b) ≤ F a * F b` obey the finite partial-sum inequality
`A * B ≤ S * (A + B - 1)`, where `A = ∑ F`, `B = ∑ G`,
and `S = ∑ F * G`, all over the same range containing zero.
Finite support is unnecessary: discarding the omitted nonnegative terms
already bounds the two triangular parts of the product sum.
-/

namespace Research.SurvivalConvolution

open scoped BigOperators

/-- Shifting a nonnegative tail and truncating it cannot increase its sum. -/
lemma shifted_sum_le (H : ℕ → ℝ) (hH : ∀ k, 0 ≤ H k) (n i c : ℕ) :
    (∑ j ∈ Finset.Ico (i + c) n, H (j - i)) ≤
      ∑ k ∈ Finset.Ico c n, H k := by
  rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_assoc, Nat.add_sub_cancel_left]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (by omega)
  · intro k _ _
    exact hH _

/-- The weak upper triangle of a product sum is bounded by `S * B`. -/
lemma upper_triangle_le (F G : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k)
    (hG : ∀ k, 0 ≤ G k)
    (hGNBU : ∀ a b, G (a + b) ≤ G a * G b) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∑ j ∈ Finset.Ico i n, F i * G j) ≤
      (∑ i ∈ Finset.range n, F i * G i) * (∑ j ∈ Finset.range n, G j) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  calc
    (∑ j ∈ Finset.Ico i n, F i * G j) ≤
        ∑ j ∈ Finset.Ico i n, (F i * G i) * G (j - i) := by
      apply Finset.sum_le_sum
      intro j hj
      have hij := (Finset.mem_Ico.mp hj).1
      have h := hGNBU i (j - i)
      rw [Nat.add_sub_of_le hij] at h
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left h (hF i)
    _ = (F i * G i) * (∑ j ∈ Finset.Ico i n, G (j - i)) := by
      rw [Finset.mul_sum]
    _ ≤ (F i * G i) * (∑ j ∈ Finset.range n, G j) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (hF i) (hG i))
      simpa only [Nat.add_zero, Nat.Ico_zero_eq_range] using
        shifted_sum_le G hG n i 0

/-- The strict lower triangle is bounded by `S` times the positive-index
partial sum of `F`. -/
lemma lower_triangle_le (F G : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k)
    (hG : ∀ k, 0 ≤ G k)
    (hFNBU : ∀ a b, F (a + b) ≤ F a * F b) (n : ℕ) :
    (∑ j ∈ Finset.range n, ∑ i ∈ Finset.Ico (j + 1) n, F i * G j) ≤
      (∑ j ∈ Finset.range n, F j * G j) * (∑ i ∈ Finset.Ico 1 n, F i) := by
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  calc
    (∑ i ∈ Finset.Ico (j + 1) n, F i * G j) ≤
        ∑ i ∈ Finset.Ico (j + 1) n, (F j * G j) * F (i - j) := by
      apply Finset.sum_le_sum
      intro i hi
      have hji : j ≤ i := by have := (Finset.mem_Ico.mp hi).1; omega
      have h := hFNBU j (i - j)
      rw [Nat.add_sub_of_le hji] at h
      convert mul_le_mul_of_nonneg_right h (hG j) using 1
      ring
    _ = (F j * G j) * (∑ i ∈ Finset.Ico (j + 1) n, F (i - j)) := by
      rw [Finset.mul_sum]
    _ ≤ (F j * G j) * (∑ i ∈ Finset.Ico 1 n, F i) :=
      mul_le_mul_of_nonneg_left (shifted_sum_le F hF n j 1)
        (mul_nonneg (hF j) (hG j))

/-- Generic finite convolution inequality from nonnegativity, normalization,
and NBU, rather than an assumed convolution or reciprocal bound. -/
theorem finite_nbu_convolution (F G : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k)
    (hG : ∀ k, 0 ≤ G k) (hF0 : F 0 = 1)
    (hFNBU : ∀ a b, F (a + b) ≤ F a * F b)
    (hGNBU : ∀ a b, G (a + b) ≤ G a * G b) (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ Finset.range n, F i) * (∑ j ∈ Finset.range n, G j) ≤
      (∑ k ∈ Finset.range n, F k * G k) *
        ((∑ i ∈ Finset.range n, F i) + (∑ j ∈ Finset.range n, G j) - 1) := by
  have hsplit :
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, F i * G j) =
        (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, F i * G j) +
        (∑ i ∈ Finset.range n, ∑ j ∈ Finset.Ico i n, F i * G j) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    exact (Finset.sum_range_add_sum_Ico _ (Nat.le_of_lt (Finset.mem_range.mp hi))).symm
  have hflip :
      (∑ i ∈ Finset.range n, ∑ j ∈ Finset.range i, F i * G j) =
        ∑ j ∈ Finset.range n, ∑ i ∈ Finset.Ico (j + 1) n, F i * G j := by
    simpa only [Nat.Ico_zero_eq_range] using
      (Finset.sum_Ico_Ico_comm' 0 n (fun j i => F i * G j)).symm
  have htail : (∑ i ∈ Finset.Ico 1 n, F i) = (∑ i ∈ Finset.range n, F i) - 1 := by
    have h := Finset.sum_range_eq_add_Ico F hn
    rw [hF0] at h
    linarith
  calc
    (∑ i ∈ Finset.range n, F i) * (∑ j ∈ Finset.range n, G j) =
        ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, F i * G j := by
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    _ = (∑ j ∈ Finset.range n, ∑ i ∈ Finset.Ico (j + 1) n, F i * G j) +
        (∑ i ∈ Finset.range n, ∑ j ∈ Finset.Ico i n, F i * G j) := by
      rw [hsplit, hflip]
    _ ≤ (∑ k ∈ Finset.range n, F k * G k) * (∑ i ∈ Finset.Ico 1 n, F i) +
        (∑ k ∈ Finset.range n, F k * G k) * (∑ j ∈ Finset.range n, G j) :=
      add_le_add (lower_triangle_le F G hF hG hFNBU n)
        (upper_triangle_le F G hF hG hGNBU n)
    _ = _ := by rw [htail]; ring

/-- A normalized nonnegative partial sum containing index zero is at least one. -/
lemma one_le_sum_range (H : ℕ → ℝ) (hH : ∀ k, 0 ≤ H k) (hH0 : H 0 = 1)
    (n : ℕ) (hn : 0 < n) : 1 ≤ ∑ k ∈ Finset.range n, H k := by
  have h := Finset.single_le_sum (f := H) (fun k _ => hH k)
    (Finset.mem_range.mpr hn)
  simpa only [hH0] using h

/-- Pure reciprocal algebra; the next theorem supplies its convolution input
from NBU sequence hypotheses. -/
lemma reciprocal_of_convolution (A B S : ℝ) (hA : 0 < A) (hB : 0 < B)
    (hS : 0 < S) (hconv : A * B ≤ S * (A + B - 1)) :
    1 / S ≤ 1 / A + 1 / B - 1 / (A * B) := by
  calc
    1 / S ≤ (A + B - 1) / (A * B) := by
      apply (div_le_div_iff₀ hS (mul_pos hA hB)).mpr
      nlinarith only [hconv]
    _ = 1 / A + 1 / B - 1 / (A * B) := by
      field_simp
      ring

/-- Reciprocal NBU convolution bound, with strict positivity obtained from
the normalized zeroth terms. All sequence assumptions are local mathematical
properties; the claimed bound is not supplied as an input. -/
theorem finite_nbu_reciprocal (F G : ℕ → ℝ) (hF : ∀ k, 0 ≤ F k)
    (hG : ∀ k, 0 ≤ G k) (hF0 : F 0 = 1) (hG0 : G 0 = 1)
    (hFNBU : ∀ a b, F (a + b) ≤ F a * F b)
    (hGNBU : ∀ a b, G (a + b) ≤ G a * G b) (n : ℕ) (hn : 0 < n) :
    1 / (∑ k ∈ Finset.range n, F k * G k) ≤
      1 / (∑ i ∈ Finset.range n, F i) + 1 / (∑ j ∈ Finset.range n, G j) -
        1 / ((∑ i ∈ Finset.range n, F i) * (∑ j ∈ Finset.range n, G j)) := by
  have hA := one_le_sum_range F hF hF0 n hn
  have hB := one_le_sum_range G hG hG0 n hn
  have hS := one_le_sum_range (fun k => F k * G k)
    (fun k => mul_nonneg (hF k) (hG k)) (by simp only [hF0, hG0, one_mul]) n hn
  exact reciprocal_of_convolution _ _ _ (by linarith) (by linarith) (by linarith)
    (finite_nbu_convolution F G hF hG hF0 hFNBU hGNBU n hn)

end Research.SurvivalConvolution
