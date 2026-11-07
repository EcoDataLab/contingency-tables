import Research.RetainedChainSquare
import Math115.PhysicalStateNonempty

namespace Math115.RetainedChainSquareTotal
open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal SmallGraphProfiles CompletionCounts LargePairEnumeration
open Math115.ReducedSmallChain Math115.ReducedAllSmallChain Math115.PhysicalStateNonempty
open Math115.RetainedChainSquare

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

/-- In dimensions at least two, a nonempty small mask has at least two cells:
one small row or small column is already an injective family of that size. -/
theorem small_count_at_least_two_of_cell (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (hI : 2≤Fintype.card I) (hJ : 2≤Fintype.card J)
    (s : Cells (firstPaperSmall r c U)) :
    2≤Fintype.card (Cells (firstPaperSmall r c U)) := by
  have hs : r s.val.1<U ∨ c s.val.2<U := by
    simpa only [firstPaperSmall,decide_eq_true_eq] using s.property
  rcases hs with hr | hc
  · let f : J → Cells (firstPaperSmall r c U) := fun j =>
      ⟨(s.val.1,j),by simp [firstPaperSmall,hr]⟩
    have hinj : Function.Injective f := by
      intro j k he
      exact congrArg (fun t : Cells (firstPaperSmall r c U) => t.val.2) he
    exact hJ.trans (Fintype.card_le_of_injective f hinj)
  · let f : I → Cells (firstPaperSmall r c U) := fun i =>
      ⟨(i,s.val.2),by simp [firstPaperSmall,hc]⟩
    have hinj : Function.Injective f := by
      intro i k he
      exact congrArg (fun t : Cells (firstPaperSmall r c U) => t.val.1) he
    exact hI.trans (Fintype.card_le_of_injective f hinj)

theorem small_cells_empty_of_not_two (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (hI : 2≤Fintype.card I) (hJ : 2≤Fintype.card J)
    (hp : ¬2≤Fintype.card (Cells (firstPaperSmall r c U))) :
    IsEmpty (Cells (firstPaperSmall r c U)) :=
  ⟨fun s => hp (small_count_at_least_two_of_cell r c U hI hJ s)⟩

/-- An empty small-view domain makes the original profile state a singleton;
its retained dense completion fiber may still contain many different tables. -/
theorem states_subsingleton_of_small_empty (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [IsEmpty (Cells (firstPaperSmall r c U))] : Subsingleton (States r c U L) := by
  constructor
  intro x y
  apply Subtype.ext
  apply Subtype.ext
  funext q
  have hf : False := isEmptyElim q.1
  exact hf.elim

theorem finiteChain_variance_subsingleton {X : Type*} [Fintype X] [Nonempty X] [Subsingleton X]
    (C : FiniteChain X) (H : X → ℝ) : C.variance H=0 := by
  let x₀ := Classical.choice (inferInstance : Nonempty X)
  have hH (x : X) : H x=H x₀ := congrArg H (Subsingleton.elim x x₀)
  have hmean : C.mean H=H x₀ := by
    unfold FiniteChain.mean
    simp_rw [hH]
    rw [←Finset.sum_mul,C.normalized,one_mul]
  unfold FiniteChain.variance FiniteChain.inner
  simp only [hmean,hH,sub_self,mul_zero,Finset.sum_const_zero]

/-- Automatic original selected-chain theorem on its original state space.
Equal ordinary totals supply Nonempty; the only possible p<2 case has zero
profile variance, so no positive-small-mask hypothesis is left. -/
theorem selectedChain_poincare_d9_total (r : I → ℕ) (c : J → ℕ)
    (hI : 2≤Fintype.card I) (hJ : 2≤Fintype.card J)
    (htotal : ∑ i,r i=∑ j,c j)
    (H : States r c (squareCutoff (I:=I) (J:=J)) 7 → ℝ) :
    letI := states_nonempty r c (squareCutoff (I:=I) (J:=J)) 7 htotal
    (selectedChain r c (squareCutoff (I:=I) (J:=J)) 7).variance H ≤
      (3442*(dimensionAllowance (I:=I) (J:=J):ℝ)^9)*
      (selectedChain r c (squareCutoff (I:=I) (J:=J)) 7).energy H := by
  letI := states_nonempty r c (squareCutoff (I:=I) (J:=J)) 7 htotal
  by_cases hp : 2≤Fintype.card (Cells (firstPaperSmall r c (squareCutoff (I:=I) (J:=J))))
  · exact selectedChain_poincare_d9 r c hI hJ hp H
  · letI := small_cells_empty_of_not_two r c (squareCutoff (I:=I) (J:=J)) hI hJ hp
    letI := states_subsingleton_of_small_empty r c (squareCutoff (I:=I) (J:=J)) 7
    rw [finiteChain_variance_subsingleton]
    exact mul_nonneg (by positivity) ((selectedChain r c (squareCutoff (I:=I) (J:=J)) 7).energy_nonneg H)

/-- A concrete branch-selected chain from equal totals, keeping the existing
original transition law; no new sampler or proposal is constructed. -/
def feasibleSquareChain (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i,r i=∑ j,c j) :
    FiniteChain (States r c (squareCutoff (I:=I) (J:=J)) 7) := by
  letI := states_nonempty r c (squareCutoff (I:=I) (J:=J)) 7 htotal
  exact selectedChain r c (squareCutoff (I:=I) (J:=J)) 7

theorem feasibleSquareChain_pi (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i,r i=∑ j,c j)
    (z : States r c (squareCutoff (I:=I) (J:=J)) 7) :
    (feasibleSquareChain r c htotal).π z =
      weight r c (squareCutoff (I:=I) (J:=J)) 7 z /
        ∑ y,weight r c (squareCutoff (I:=I) (J:=J)) 7 y := by
  letI := states_nonempty r c (squareCutoff (I:=I) (J:=J)) 7 htotal
  exact selectedChain_pi r c (squareCutoff (I:=I) (J:=J)) 7 z

theorem feasibleSquareChain_poincare_d9 (r : I → ℕ) (c : J → ℕ)
    (hI : 2≤Fintype.card I) (hJ : 2≤Fintype.card J)
    (htotal : ∑ i,r i=∑ j,c j)
    (H : States r c (squareCutoff (I:=I) (J:=J)) 7 → ℝ) :
    (feasibleSquareChain r c htotal).variance H ≤
      (3442*(dimensionAllowance (I:=I) (J:=J):ℝ)^9)*(feasibleSquareChain r c htotal).energy H :=
  selectedChain_poincare_d9_total r c hI hJ htotal H

end
end Math115.RetainedChainSquareTotal
