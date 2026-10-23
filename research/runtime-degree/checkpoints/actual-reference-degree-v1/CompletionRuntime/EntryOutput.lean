import ReferenceRuntime.DenseWidthCoreDegree
import InputNormalization.CanonicalDegree
import AffineMapWith.Degree
import CountBounds.ScalarCircuitDegreeV2
import OAI.Combinatorics.ContingencyTables.Dense.DenseCompletedMatrixProgram

namespace Math115.CompletionRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open DensePrograms ProfilePrograms Math115.DegreeBounds Math115.DrawDegree
open Math115.InitialRuntimeNext Math115.ReferenceRuntimeNext
noncomputable section
set_option maxHeartbeats 1200000

lemma denseMatrixTotal_weight (M : MatrixCode) :
    weight (matrixTotal M) ≤ 4*weight M+1 := by
  have hsum : ∀ xs : List ℕ, weight xs.sum ≤ 4*weight xs+1 := by
    intro xs
    have hw := weight_nat_le xs.sum
    have hz : xs.sum.size ≤ weight xs := by
      clear hw
      induction xs with
      | nil => simp
      | cons a xs ih =>
        have ha := size_le_weight a
        have hh := nat_size_add a xs.sum
        rw [List.sum_cons,weight_cons]
        have hm : max a.size xs.sum.size ≤ weight a+weight xs := max_le (by omega) (by omega)
        omega
    omega
  have hh := hsum M.flatten
  have hf := weight_flatten M
  simpa only [matrixTotal,List.sum_flatten] using hh.trans (by omega : 4*weight M.flatten+1 ≤ 4*weight M+1)

lemma completionPositivePart_weight (z : CompletionCell) :
    weight (completionParts z).1 ≤ 20*weight z.1+15 := by
  have hr := Math115.ScalarCircuitDegreeV2.head_output_weight_zero z.1.1.1
  have ht := denseMatrixTotal_weight z.1.2
  have hs := weight_add (z.1.1.1.headD 0) (matrixTotal z.1.2)
  have hR := weight_getD_bound z.1.1.1 z.2.1 0
  have hC := weight_getD_bound z.1.1.2 z.2.2 0
  have he0 := weight_getD_bound z.1.2 (z.2.1-1) ([]:List ℕ)
  have he1 := weight_getD_bound (z.1.2.getD (z.2.1-1) []) (z.2.2-1) 0
  rcases z with ⟨⟨⟨rs,cs⟩,M⟩,⟨i,j⟩⟩
  simp only [weight_prod,weight_nil] at hr ht hs hR hC he0 he1 ⊢
  have h0 : weight (0:ℕ)=1 := rfl
  rw [h0] at hR hC he1
  unfold completionParts
  split
  · split
    · change weight (rs.headD 0+matrixTotal M) ≤ _; omega
    · change weight (cs.getD j 0) ≤ _; omega
  · split
    · change weight (rs.getD i 0) ≤ _; omega
    · change weight ((M.getD (i-1) []).getD (j-1) 0) ≤ _; omega

/-- Independent entry output bound: arbitrary margins, arbitrary ragged free
matrix and every index pair. No completion-validity or cost premise. -/
lemma completedEntry_weight (z : CompletionCell) :
    weight (completedEntry z) ≤ 80*weight z.1+61 := by
  have hh := completionPositivePart_weight z
  have hs := weight_nat_small (Nat.sub_le (completionParts z).1 (completionParts z).2)
  unfold completedEntry
  omega

lemma completedEntry_affine : Math115.PrinterRuntimeNext.AffineOutput completedEntry := by
  refine ⟨80,61,fun z => ?_⟩
  have hh := completedEntry_weight z
  have hf := weight_fst z
  omega

lemma completedRowEntry_weight (z : (CompletionData×ℕ)×ℕ) :
    weight (completedRowEntry z) ≤ 80*weight z.1.1+61 := completedEntry_weight _

lemma completedRowEntry_affine : Math115.PrinterRuntimeNext.AffineOutput completedRowEntry := by
  refine ⟨80,61,fun z => ?_⟩
  have hh := completedRowEntry_weight z
  have hf : weight z.1.1 ≤ weight z := (weight_fst _).trans (weight_fst _)
  omega

lemma completionNonnegative_affine : Math115.PrinterRuntimeNext.AffineOutput completionNonnegative :=
  ⟨0,3,fun z => by simpa only [zero_mul,zero_add] using weight_bool (completionNonnegative z)⟩

end
end Math115.CompletionRuntimeNext
