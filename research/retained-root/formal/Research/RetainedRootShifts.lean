import Research.RetainedRootPhysical

namespace Math115.RetainedRootPhysical

open OAI.ContingencyTables
open FactorialSignatures IntegerWeightedTransport FirstPaperProfiles ExcessContextProfiles

/-- The left diagonal is the preceding root defect, whenever its removal is
valid; the boundary entry is literally zero. -/
lemma rootDisplay_diagonal_left (F : (Bool → ℕ) → ℝ) (U l : ℕ)
    (hl0 : 1 ≤ l) (hlU : l ≤ U) :
    integerRemovalMatrix F (rootDisplay U l) false false =
      if 2 ≤ l then F (auxRoot U (l-1)) else 0 := by
  by_cases hll : 2 ≤ l
  · have hv : ValidPair (rootDisplay U l) false false := by
      simp only [ValidPair,rootDisplay,Bool.false_eq_true,↓reduceIte]
      omega
    have he : removeTwo (rootDisplay U l) false false=auxRoot U (l-1) := by
      funext b
      cases b <;> simp only [removeTwo,removeOne,rootDisplay,auxRoot,
        Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,Nat.sub_zero] <;> omega
    rw [integerRemovalMatrix,ite_eq_left hv,he,ite_eq_left hll]
  · have hv : ¬ ValidPair (rootDisplay U l) false false := by
      simp only [ValidPair,rootDisplay,Bool.false_eq_true,↓reduceIte]
      omega
    rw [integerRemovalMatrix,ite_eq_right hv,ite_eq_right hll]

/-- The right diagonal is the following root defect, with exact zero at the
last admissible adjacent level. -/
lemma rootDisplay_diagonal_right (F : (Bool → ℕ) → ℝ) (U l : ℕ)
    (hl0 : 1 ≤ l) (hlU : l ≤ U) :
    integerRemovalMatrix F (rootDisplay U l) true true =
      if l < U then F (auxRoot U (l+1)) else 0 := by
  by_cases hll : l < U
  · have hv : ValidPair (rootDisplay U l) true true := by
      simp only [ValidPair,rootDisplay,↓reduceIte]
      omega
    have he : removeTwo (rootDisplay U l) true true=auxRoot U (l+1) := by
      funext b
      cases b <;> simp only [removeTwo,removeOne,rootDisplay,auxRoot,
        Bool.false_eq_true,Bool.true_eq_false,↓reduceIte,Nat.sub_zero] <;> omega
    rw [integerRemovalMatrix,ite_eq_left hv,he,ite_eq_left hll]
  · have hv : ¬ ValidPair (rootDisplay U l) true true := by
      simp only [ValidPair,rootDisplay,↓reduceIte]
      omega
    rw [integerRemovalMatrix,ite_eq_right hv,ite_eq_right hll]

/-- Exact actual-kernel coefficient as the discrete root-defect triple. -/
theorem retainedRootCoefficient_shift (F : (Bool → ℕ) → ℝ) (U l : ℕ)
    (s t : ℝ) (hl0 : 1 ≤ l) (hlU : l ≤ U) :
    retainedRootCoefficient (integerRemovalMatrix F (rootDisplay U l)) s t =
      1/s+1/t - (if 2 ≤ l then F (auxRoot U (l-1)) else 0)/s^2 +
        2*F (auxRoot U l)/(s*t) -
        (if l < U then F (auxRoot U (l+1)) else 0)/t^2 := by
  unfold retainedRootCoefficient
  rw [rootDisplay_diagonal_left F U l hl0 hlU,
    rootDisplay_diagonal_right F U l hl0 hlU,rootDisplay_removal F U l hl0]

end Math115.RetainedRootPhysical

#print axioms Math115.RetainedRootPhysical.retainedRootCoefficient_shift
