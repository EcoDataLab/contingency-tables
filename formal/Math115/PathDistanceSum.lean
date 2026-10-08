/-
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Dist

/-!
# Distances to a mode on a finite path

The sum of distances to an index `m` in `0, …, U` is the sum of the two
triangular numbers on either side of `m`. Its maximum occurs at an endpoint.
-/

namespace Math115.PathDistanceSum

open scoped BigOperators

/-- The sum of the vertex indices of a path, expressed as a real number. -/
lemma sum_values_eq_triangle (U : ℕ) :
    (∑ r : Fin (U + 1), (r.val : ℝ)) = (U : ℝ) * ((U : ℝ) + 1) / 2 := by
  induction U with
  | zero => simp
  | succ U ih =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      rw [ih]
      push_cast
      ring

/-- Exact sum of distances from the path vertices to an index in the path. -/
theorem sum_dist_eq_two_triangles (U m : ℕ) (hm : m ≤ U) :
    (∑ r : Fin (U + 1), (Nat.dist r.val m : ℝ)) =
      (m : ℝ) * ((m : ℝ) + 1) / 2 +
        ((U : ℝ) - m) * ((U : ℝ) - m + 1) / 2 := by
  induction U generalizing m with
  | zero =>
      have hm0 : m = 0 := by omega
      subst m
      simp
  | succ U ih =>
      cases m with
      | zero =>
          simpa [Nat.dist_zero_right] using sum_values_eq_triangle (U + 1)
      | succ m =>
          rw [Fin.sum_univ_succ]
          simp only [Fin.val_zero, Fin.val_succ, Nat.dist_zero_left, Nat.dist_succ_succ]
          rw [ih m (by omega)]
          push_cast
          ring

/-- The exact improvement over the endpoint distance sum is `m * (U - m)`. -/
theorem sum_dist_eq_triangle_sub (U m : ℕ) (hm : m ≤ U) :
    (∑ r : Fin (U + 1), (Nat.dist r.val m : ℝ)) =
      (U : ℝ) * ((U : ℝ) + 1) / 2 - (m : ℝ) * ((U : ℝ) - m) := by
  rw [sum_dist_eq_two_triangles U m hm]
  ring

/-- Every choice of mode has total path distance at most the endpoint value. -/
theorem sum_dist_le_triangle (U m : ℕ) (hm : m ≤ U) :
    (∑ r : Fin (U + 1), (Nat.dist r.val m : ℝ)) ≤
      (U : ℝ) * ((U : ℝ) + 1) / 2 := by
  rw [sum_dist_eq_triangle_sub U m hm]
  have hnonneg : 0 ≤ (m : ℝ) * ((U : ℝ) - m) :=
    mul_nonneg (Nat.cast_nonneg m) (sub_nonneg.mpr (by exact_mod_cast hm))
  exact sub_le_self _ hnonneg

end Math115.PathDistanceSum
