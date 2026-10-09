import Mathlib.Tactic

/-! The elementary sharp coefficient used by the transport refinement. -/

namespace Math115

lemma pair_product_le_quarter_square (a M : ℝ) :
    a * (M - a) ≤ M ^ 2 / 4 := by
  nlinarith [sq_nonneg (M - 2 * a)]

lemma pair_product_eq_quarter_square_iff (a M : ℝ) :
    a * (M - a) = M ^ 2 / 4 ↔ a = M / 2 := by
  constructor
  · intro h
    nlinarith [sq_nonneg (M - 2 * a)]
  · rintro rfl
    ring

end Math115
