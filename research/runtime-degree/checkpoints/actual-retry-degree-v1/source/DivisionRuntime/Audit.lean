import DivisionRuntime.Degree

#print Math115.DivisionRuntimeNext.typed_division
#print axioms Math115.DivisionRuntimeNext.typed_division
#print Math115.DivisionRuntimeNext.typed_quotient
#print axioms Math115.DivisionRuntimeNext.typed_quotient
#print axioms Math115.DivisionRuntimeNext.divFold_intermediate
#print axioms Math115.DivisionRuntimeNext.typed_divStep
#print axioms Math115.DivisionRuntimeNext.typed_divFold
#print axioms Math115.DivisionRuntimeNext.typed_divCore

namespace Math115.DivisionRuntimeNext
open OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds

-- Unwrap the certificate to expose the exact unconditional charged-work goal.
example : ∃ p : Polynomial ℕ, p.natDegree ≤ 4 ∧
    ∀ a : ℕ × ℕ, TreeTyped.division.cost a + weight (a.1/a.2,a.1%a.2) ≤
      p.eval (weight a) := typed_division

example : ∃ p : Polynomial ℕ, p.natDegree ≤ 4 ∧
    ∀ a : ℕ × ℕ, TreeTyped.quotient.cost a + weight (a.1/a.2) ≤
      p.eval (weight a) := typed_quotient

end Math115.DivisionRuntimeNext
