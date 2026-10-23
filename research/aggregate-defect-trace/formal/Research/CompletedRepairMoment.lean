import Research.CompletedRepairInjection
import Research.ResidualSelectedBudget

namespace Math115.CompletedRepairInjection

open OAI.ContingencyTables
open SmallContextFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts
open Research.ResidualSelectedBudget
open scoped BigOperators Classical

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

/-- The real moment remains literal: natural subtraction is not used outside
its independently proved physical support. -/
def donorMoment (U x : ℕ) : ℝ := (x:ℝ)*((U:ℝ)+1-(x:ℝ))

/-- Actual original-margin partial constraints supply all nonnegativity
needed by the completion-retaining injection, including large crossings. -/
theorem physical_hard_donor_moment_le_child
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (s t : I×J) (σ : I×J → ℕ) (l : ℕ)
    (hs : firstPaperSmall r c U s.1 s.2=true)
    (ht : firstPaperSmall r c U t.1 t.2=true) (hst : RowMajorBefore s t) :
    (∑ z : DefectProfiles (firstPaperSmall r c U) B s t σ l,
      donorMoment U (smallView (firstPaperSmall r c U) (naturalProfile z.val) false t.1 t.2)*
        hardMarginal (firstPaperSmall r c U) B r c L (naturalProfile z.val))≤
      ∑ A : SmallResidualChild (firstPaperSmall r c U) r
        (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
        c (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L)
        s σ (l-1+if t.1=s.1 then 1 else 0),
        donorMoment U (A.val.val.val t.1 t.2+(if t.2=s.2 then 0 else 1)) := by
  apply hard_donor_sum_le_child L hs ht hst
  intro A
  have hcast := residual_recovered_moment_cast r c
    (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
    (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L) U A.val s ⟨t,ht⟩
  change 0≤donorMoment U (recoveredDonor A.val.val.val s t)
  unfold donorMoment
  rw [←hcast]
  exact Nat.cast_nonneg _

end
end Math115.CompletedRepairInjection
