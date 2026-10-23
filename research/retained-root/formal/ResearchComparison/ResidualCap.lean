import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalResidualMargins

namespace Math115.LegacyResidualCap
open OAI.ContingencyTables
open SmallGraphProfiles PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open scoped BigOperators Classical

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

def markedCount (small : I → J → Bool) : ℕ := ∑ i,rowLargeCount small i

/-- Actual residual total bound for EVERY positive physical state, including
balanced and defect states. No guessed ordinary-view or zero-residual premise. -/
theorem residual_total_bound (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : PhysicalStates small B r c L) :
    (∑ i,residualRows small B r c L z i) ≤ (∑ i,r i)+markedCount small*L := by
  calc
    _ ≤ ∑ i,(r i+rowLargeCount small i*L) := by
      apply Finset.sum_le_sum
      intro i _
      unfold residualRows
      omega
    _ = _ := by rw [Finset.sum_add_distrib,←Finset.sum_mul]; rfl

/-- A state-independent source cap discharges the exact physical completion
nonrestriction condition at every positive state. -/
theorem all_state_cap (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (hB : ∀ i j,small i j=false → (∑ k,r k)+markedCount small*L ≤ B i j)
    (z : PhysicalStates small B r c L) :
    ∀ i j,small i j=false → (∑ k,residualRows small B r c L z k) ≤ B i j := by
  intro i j hs
  exact (residual_total_bound small B r c L z).trans (hB i j hs)

def largeRowCount (r : I → ℕ) (U : ℕ) : ℕ := ∑ i,if U≤r i then 1 else 0
def largeColumnCount (c : J → ℕ) (U : ℕ) : ℕ := ∑ j,if U≤c j then 1 else 0

theorem rectangle_marked_count (r : I → ℕ) (c : J → ℕ) (U : ℕ) :
    markedCount (firstPaperSmall r c U) = largeRowCount r U*largeColumnCount c U := by
  have hcell (i : I) (j : J) :
      (if firstPaperSmall r c U i j then 0 else 1) =
        (if U≤r i then 1 else 0)*(if U≤c j then 1 else 0) := by
    by_cases hs : firstPaperSmall r c U i j=false
    · have h := (firstPaperSmall_false_iff r c U i j).mp hs
      simp [hs,h.1,h.2]
    · have ht : firstPaperSmall r c U i j=true := Bool.eq_true_of_ne_false hs
      have hnot : ¬(U≤r i ∧ U≤c j) := by
        intro h
        exact hs ((firstPaperSmall_false_iff r c U i j).mpr h)
      by_cases hr : U≤r i <;> by_cases hc : U≤c j <;> simp_all
  unfold markedCount rowLargeCount largeRowCount largeColumnCount
  simp_rw [hcell,←Finset.mul_sum]
  rw [←Finset.sum_mul]

theorem all_state_l7_cap (r : I → ℕ) (c : J → ℕ) (U : ℕ) (B : I → J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,r k)+7*(largeRowCount r U*largeColumnCount c U) ≤ B i j)
    (z : PhysicalStates (firstPaperSmall r c U) B r c 7) :
    ∀ i j,firstPaperSmall r c U i j=false →
      (∑ k,residualRows (firstPaperSmall r c U) B r c 7 z k) ≤ B i j := by
  apply all_state_cap _ _ _ _ _ _ z
  intro i j hs
  rw [rectangle_marked_count,mul_comm _ 7]
  exact hB i j hs

end
end Math115.LegacyResidualCap
