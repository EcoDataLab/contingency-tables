import CompletionRuntime.EntryOutput

namespace Math115.CompletionRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open DensePrograms ProfilePrograms Math115.DegreeBounds Math115.DrawDegree
open Math115.InitialRuntimeNext Math115.CatalogueDegreeV1
noncomputable section
set_option maxHeartbeats 1600000

lemma typed_completionNonnegative : Typed completionNonnegativeRealizer 78 := by
  unfold completionNonnegativeRealizer
  exact typed_composition
    (typed_composition Math115.ReferenceRuntimeNext.typed_completionParts (typed_pair typed_second typed_first))
    Math115.ListRepeatDegreeV1.typed_leNat

lemma completionBoolList_affine : Math115.PrinterRuntimeNext.AffineOutput
    (fun z : CompletionData×List (ℕ×ℕ) => z.2.map (fun ij => completionNonnegative (z.1,ij))) := by
  refine ⟨4,1,fun z => ?_⟩
  change weight (z.2.map (fun ij => completionNonnegative (z.1,ij))) ≤ 4*weight z+1
  have hh := weight_map_bound (as:=z.2) (f:=fun ij => completionNonnegative (z.1,ij))
    (N:=3) (fun ij hij => weight_bool _)
  have hl := (list_length_le_weight z.2).trans (weight_snd z)
  omega

lemma typed_completionBoolList : Typed (mapWith completionNonnegativeRealizer) 79 :=
  Math115.AffineMapWithNext.typed_mapWith_linear_output typed_completionNonnegative (by decide)
    completionBoolList_affine

lemma degree_catalogueArgument :
    (8*X^3+4*X^2+X+2 : Polynomial ℕ).natDegree ≤ 3 := by
  have h3 := degree_scale 8 (show (X^3 : Polynomial ℕ).natDegree ≤ 3 by simp)
  have h2 := degree_scale 4 (show (X^2 : Polynomial ℕ).natDegree ≤ 2 by simp)
  have h1 : (X : Polynomial ℕ).natDegree ≤ 1 := by simp
  have h0 : (2 : Polynomial ℕ).natDegree ≤ 0 := by simp
  simpa using degree_add (degree_add (degree_add h3 h2) h1) h0

lemma catalogueArgument_output (z : CompletionData) :
    weight (z,cellPairs z.1) ≤ (8*X^3+4*X^2+X+2 : Polynomial ℕ).eval (weight z) := by
  have hh := weight_cellPairs_output z.1
  have hm := polynomial_eval_monotone (8*X^3+4*X^2+1 : Polynomial ℕ) (weight_fst z)
  simp only [eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one] at hm ⊢
  rw [weight_prod]
  omega

lemma completionBoolList_output (z : CompletionData) :
    weight ((cellPairs z.1).map (fun ij => completionNonnegative (z,ij))) ≤
      (4*X^2+1 : Polynomial ℕ).eval (weight z) := by
  have hh := weight_map_bound (as:=cellPairs z.1) (f:=fun ij => completionNonnegative (z,ij))
    (N:=3) (fun ij hij => weight_bool _)
  have hr : z.1.1.length ≤ weight z :=
    (list_length_le_weight z.1.1).trans ((weight_fst _).trans (weight_fst _))
  have hc : z.1.2.length ≤ weight z :=
    (list_length_le_weight z.1.2).trans ((weight_snd _).trans (weight_fst _))
  have hl : (cellPairs z.1).length ≤ (weight z)^2 := by
    simpa only [cellPairs,List.length_map,List.length_range,pow_two] using Nat.mul_le_mul hr hc
  simp only [eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
  omega

/-- Exact original eager validity test, including every constructed Bool and
all intermediate map accumulators, on every raw margin/matrix input. -/
theorem typed_completionValid : Typed completionValidRealizer 504 := by
  have hprep : Typed (pair (identity (A:=CompletionData)) (composition first cellPairsRealizer)) 504 :=
    typed_pair_same (typed_weaken typed_identity (by decide))
      (typed_composition_pos typed_first typed_cellPairs (by decide)) (by decide)
  have hmap := Math115.ScalarOutputDegree.typed_composition_from_output_size hprep typed_completionBoolList
    (8*X^3+4*X^2+X+2) degree_catalogueArgument catalogueArgument_output
  have hd : (4*X^2+1 : Polynomial ℕ).natDegree ≤ 2 := by
    simpa using degree_add (degree_scale 4 (show (X^2 : Polynomial ℕ).natDegree ≤ 2 by simp))
      (show (1 : Polynomial ℕ).natDegree ≤ 0 by simp)
  have hresult := Math115.ScalarOutputDegree.typed_composition_from_output_size hmap
    Math115.ReferenceRuntimeNext.typed_all (4*X^2+1)
    hd
    (by intro z; simpa only [Function.comp_apply,id_eq] using completionBoolList_output z)
  unfold completionValidRealizer
  exact typed_congr _ (by simpa using hresult)

lemma completionValid_output (z : CompletionData) : weight (completionValid z) ≤ 3 := weight_bool _

#check typed_completionValid
#print axioms typed_completionValid
end
end Math115.CompletionRuntimeNext
