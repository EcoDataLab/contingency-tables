import InputNormalization.MaximalIndex
import OAI.Combinatorics.ContingencyTables.Dense.DenseNormalizeProgram

namespace Math115.InputNormalization
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open DensePrograms Math115.DegreeBounds Math115.DrawDegree Math115.InitialRuntimeNext
noncomputable section
variable {A : Type} [Codec A] [Inhabited A]

lemma weight_set_le (xs : List A) (i : ℕ) (a : A) :
    weight (xs.set i a) ≤ weight xs+weight a := by
  induction xs generalizing i with
  | nil => simp
  | cons b bs ih =>
    cases i with
    | zero => simp only [List.set_cons_zero,weight_cons]; omega
    | succ i =>
      have hh := ih i
      simp only [List.set_cons_succ,weight_cons]
      omega

/-- The original index map is exactly the two updates, even for empty lists
and out-of-range chosen indices. No permutation validity premise is needed. -/
lemma swapZeroList_eq_sets (p : ℕ) (xs : List A) :
    swapZeroList (p,xs)=(xs.set 0 (xs.getD p default)).set p (xs.getD 0 default) := by
  apply List.ext_getElem
  · simp only [swapZeroList,swapZeroIndices,List.length_map,List.length_range,List.length_set]
  · intro i hi hj
    have hil : i < xs.length := by
      simpa only [swapZeroList,swapZeroIndices,List.length_map,List.length_range] using hi
    simp only [swapZeroList,swapZeroIndices,List.getElem_map,List.getElem_range,swapZeroEntry]
    by_cases h0 : i=0
    · subst i
      by_cases hp : p=0
      · subst p
        simp [swapZeroIndex]
      · simp [swapZeroIndex,List.getElem_set,hp,Ne.symm hp]
    · by_cases hp : i=p
      · subst p
        simp [swapZeroIndex,List.getElem_set,h0,Ne.symm h0]
      · simp only [swapZeroIndex,h0,hp,ite_false]
        rw [List.getD_eq_getElem xs default hil]
        simp [List.getElem_set,h0,hp,Ne.symm h0,Ne.symm hp]

/-- A deliberately conservative affine encoding envelope for the SAME
swap program over every literal index/list pair, including malformed indices. -/
theorem swapZeroList_weight (p : ℕ) (xs : List A) :
    weight (swapZeroList (p,xs)) ≤ 3*weight xs+2*weight (default : A) := by
  rw [swapZeroList_eq_sets]
  have hs0 := weight_set_le xs 0 (xs.getD p default)
  have hs1 := weight_set_le (xs.set 0 (xs.getD p default)) p (xs.getD 0 default)
  have hg0 := weight_getD_bound xs p (default : A)
  have hg1 := weight_getD_bound xs 0 (default : A)
  omega

lemma swapZeroList_affine : Math115.PrinterRuntimeNext.AffineOutput (swapZeroList (A:=A)) := by
  refine ⟨3,2*weight (default : A),fun z => ?_⟩
  exact (swapZeroList_weight z.1 z.2).trans (by rw [weight_prod]; omega)

end
end Math115.InputNormalization
