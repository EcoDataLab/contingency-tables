/-
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

/-!
# Finite-sum bounds for all-donor switching

These elementary natural-number inequalities are independent of the upstream
contingency-table definitions. They include empty index sets and require no
positive lower bound on individual donor counts.
-/

namespace Math115.SwitchingFiniteSums

open scoped BigOperators

universe u v

variable {A : Type u} {B : Type v}

/-- Capping a sum loses at least as much mass as capping each summand. -/
lemma min_add_le (t a b : ℕ) :
    min t (a + b) ≤ min t a + min t b := by
  omega

/-- The total count, capped once, is bounded by the sum of capped counts. -/
theorem min_sum_le_sum_min (s : Finset A) (h : A → ℕ) (t : ℕ) :
    min t (∑ x ∈ s, h x) ≤ ∑ x ∈ s, min t (h x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx, Finset.sum_insert hx]
      exact (min_add_le t _ _).trans (Nat.add_le_add_left ih _)

/-- The smaller of two total donor counts is bounded by all pairwise minima. -/
theorem min_sums_le_sum_pairwise_min
    (s : Finset A) (t : Finset B) (u : A → ℕ) (v : B → ℕ) :
    min (∑ a ∈ s, u a) (∑ b ∈ t, v b) ≤
      ∑ a ∈ s, ∑ b ∈ t, min (u a) (v b) := by
  calc
    min (∑ a ∈ s, u a) (∑ b ∈ t, v b) =
        min (∑ b ∈ t, v b) (∑ a ∈ s, u a) := min_comm _ _
    _ ≤ ∑ a ∈ s, min (∑ b ∈ t, v b) (u a) :=
      min_sum_le_sum_min s u _
    _ ≤ ∑ a ∈ s, ∑ b ∈ t, min (u a) (v b) := by
      apply Finset.sum_le_sum
      intro a _
      rw [min_comm]
      exact min_sum_le_sum_min t v (u a)

/-- The all-donor bound on finite types, including empty types. -/
theorem min_fintype_sums_le_sum_pairwise_min [Fintype A] [Fintype B]
    (u : A → ℕ) (v : B → ℕ) :
    min (∑ a, u a) (∑ b, v b) ≤ ∑ a, ∑ b, min (u a) (v b) :=
  min_sums_le_sum_pairwise_min Finset.univ Finset.univ u v

/-- Capped counts plus the shortfalls at small entries fill every slot to its cap. -/
theorem sum_min_add_sum_deficit (s : Finset A) (h : A → ℕ) (t : ℕ) :
    (∑ x ∈ s, min t (h x)) +
        (∑ x ∈ s.filter (fun x => h x < t), (t - h x)) = t * s.card := by
  classical
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  calc
    (∑ x ∈ s, (min t (h x) + if h x < t then t - h x else 0)) =
        ∑ _x ∈ s, t := by
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> omega
    _ = t * s.card := by simp [Nat.mul_comm]

/-- The capped-count/shortfall identity on a finite type. -/
theorem fintype_sum_min_add_sum_deficit [Fintype A] (h : A → ℕ) (t : ℕ) :
    (∑ x, min t (h x)) +
        (∑ x ∈ Finset.univ.filter (fun x => h x < t), (t - h x)) =
      t * Fintype.card A := by
  simpa using sum_min_add_sum_deficit Finset.univ h t

end Math115.SwitchingFiniteSums
