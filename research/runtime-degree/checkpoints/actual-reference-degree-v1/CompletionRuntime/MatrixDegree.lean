import CompletionRuntime.ValidDegree

namespace Math115.CompletionRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open DensePrograms ProfilePrograms Math115.DegreeBounds Math115.DrawDegree
noncomputable section
set_option maxHeartbeats 2000000

lemma typed_completedEntry : Typed completedEntryRealizer 78 := by
  unfold completedEntryRealizer
  exact typed_composition
    (typed_composition Math115.ReferenceRuntimeNext.typed_completionParts (typed_pair typed_first typed_second))
    Math115.DivisionRuntimeNext.typed_subtract_actual

lemma typed_completionRows : Typed completionRowsRealizer 3 := by
  unfold completionRowsRealizer
  apply Math115.DrawRuntimeNext.typed_boundedRange (e:=2) (d:=1)
    (typed_composition (typed_composition typed_first typed_first) Math115.WordCountSeedDegrees.typed_listLength_seed) X (by simp)
  intro z
  simp only [Function.comp_apply,eval_X]
  exact (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

lemma typed_completionColumns : Typed completionColumnsRealizer 3 := by
  unfold completionColumnsRealizer
  apply Math115.DrawRuntimeNext.typed_boundedRange (e:=2) (d:=1)
    (typed_composition (typed_composition typed_first typed_second) Math115.WordCountSeedDegrees.typed_listLength_seed) X (by simp)
  intro z
  simp only [Function.comp_apply,eval_X]
  exact (list_length_le_weight z.1.2).trans ((weight_snd z.1).trans (weight_fst z))

lemma rangeLength_weight {A : Type} [Codec A] (xs : List A) :
    weight (List.range xs.length) ≤ 4*(weight xs)^2+2*weight xs+1 := by
  have hh := weight_map_bound (as:=List.range xs.length) (f:=id) (N:=4*weight xs+1) (by
    intro n hn
    change weight n ≤ 4*weight xs+1
    have hl : n < xs.length := List.mem_range.mp hn
    have hw := weight_nat_numeric n
    have hs := list_length_le_weight xs
    omega)
  simp only [List.map_id,List.length_range] at hh
  have hs := list_length_le_weight xs
  nlinarith

lemma degree_rangeArgument : (4*X^2+3*X+2 : Polynomial ℕ).natDegree ≤ 2 := by
  simpa using degree_add
    (degree_add (degree_scale 4 (show (X^2 : Polynomial ℕ).natDegree ≤ 2 by simp))
      (degree_scale 3 (show (X : Polynomial ℕ).natDegree ≤ 1 by simp)))
    (show (2 : Polynomial ℕ).natDegree ≤ 0 by simp)

lemma columnArgument_output (z : CompletionData×ℕ) :
    weight (z,completionColumns z.1) ≤ (4*X^2+3*X+2 : Polynomial ℕ).eval (weight z) := by
  have hh := rangeLength_weight z.1.1.2
  have hs : weight z.1.1.2 ≤ weight z := (weight_snd _).trans ((weight_fst _).trans (weight_fst _))
  have hm := polynomial_eval_monotone (4*X^2+2*X+1 : Polynomial ℕ) hs
  simp only [eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one] at hm ⊢
  unfold completionColumns
  rw [weight_prod]
  omega

lemma rowArgument_output (z : CompletionData) :
    weight (z,completionRows z) ≤ (4*X^2+3*X+2 : Polynomial ℕ).eval (weight z) := by
  have hh := rangeLength_weight z.1.1
  have hs : weight z.1.1 ≤ weight z := (weight_fst _).trans (weight_fst _)
  have hm := polynomial_eval_monotone (4*X^2+2*X+1 : Polynomial ℕ) hs
  simp only [eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one] at hm ⊢
  unfold completionRows
  rw [weight_prod]
  omega

lemma typed_completedRowEntry : Typed completedRowEntryRealizer 78 := by
  unfold completedRowEntryRealizer
  exact typed_composition
    (typed_pair (typed_composition typed_first typed_first)
      (typed_pair (typed_composition typed_first typed_second) typed_second)) typed_completedEntry

lemma typed_completedRowMap : Typed (mapWith completedRowEntryRealizer) 157 := by
  simpa using Math115.AffineMapWithNext.typed_mapWith_affine typed_completedRowEntry (by decide) completedRowEntry_affine

/-- Exact original row builder, including every completed entry and every
map accumulator; no rectangularity or acceptance premise. -/
lemma typed_completedRow : Typed completedRowRealizer 314 := by
  have hprep : Typed (pair (identity (A:=CompletionData×ℕ)) (composition first completionColumnsRealizer)) 3 :=
    typed_pair_same (typed_weaken typed_identity (by decide))
      (typed_composition_pos typed_first typed_completionColumns (by decide)) (by decide)
  unfold completedRowRealizer
  obtain ⟨p,hp,hpb⟩ := Math115.ScalarOutputDegree.typed_composition_from_output_size hprep typed_completedRowMap
    (4*X^2+3*X+2) degree_rangeArgument columnArgument_output
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [completedRow,Function.comp_apply,id_eq] using hpb z

lemma completedRow_weight (z : CompletionData) (i : ℕ) :
    weight (completedRow (z,i)) ≤ weight z*(80*weight z+62)+1 := by
  have hh := weight_map_bound (as:=completionColumns z) (f:=fun j => completedRowEntry ((z,i),j))
    (N:=80*weight z+61) (fun j hj => completedRowEntry_weight _)
  have hl : (completionColumns z).length ≤ weight z := by
    simpa only [completionColumns,List.length_range] using
      (list_length_le_weight z.1.2).trans ((weight_snd _).trans (weight_fst _))
  unfold completedRow
  exact hh.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) 1)

lemma degree_matrixOutput : (80*X^3+62*X^2+2*X+1 : Polynomial ℕ).natDegree ≤ 3 := by
  simpa using degree_add
    (degree_add
      (degree_add (degree_scale 80 (show (X^3 : Polynomial ℕ).natDegree ≤ 3 by simp))
        (degree_scale 62 (show (X^2 : Polynomial ℕ).natDegree ≤ 2 by simp)))
      (degree_scale 2 (show (X : Polynomial ℕ).natDegree ≤ 1 by simp)))
    (show (1 : Polynomial ℕ).natDegree ≤ 0 by simp)

lemma completedRows_output : Math115.AffineMapWithNext.OutputBound
    (fun z : CompletionData×List ℕ => z.2.map (fun i => completedRow (z.1,i))) 3 := by
  refine ⟨80*X^3+62*X^2+2*X+1,degree_matrixOutput,fun z => ?_⟩
  change weight (z.2.map (fun i => completedRow (z.1,i))) ≤
    (80*X^3+62*X^2+2*X+1 : Polynomial ℕ).eval (weight z)
  have hm := polynomial_eval_monotone (80*X^2+62*X+1 : Polynomial ℕ) (weight_fst z)
  simp only [eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one] at hm
  have hh := weight_map_bound (as:=z.2) (f:=fun i => completedRow (z.1,i))
    (N:=80*(weight z)^2+62*weight z+1) (fun i hi => by
      have hw := completedRow_weight z.1 i
      nlinarith)
  have hl := (list_length_le_weight z.2).trans (weight_snd z)
  have hp := Nat.mul_le_mul_right (80*(weight z)^2+62*weight z+2) hl
  simp only [eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
  nlinarith

lemma typed_completedMatrixMap : Typed (mapWith completedRowRealizer) 943 := by
  simpa using Math115.AffineMapWithNext.typed_mapWith_output (s:=3) typed_completedRow (by decide) (by decide) completedRows_output

/-- Original completed-matrix program: all generated rows and entries,
intermediate eager accumulators, final output and every raw input are charged. -/
theorem typed_completedMatrix : Typed completedMatrixRealizer 1886 := by
  have hprep : Typed (pair (identity (A:=CompletionData)) completionRowsRealizer) 3 :=
    typed_pair_same (typed_weaken typed_identity (by decide)) typed_completionRows (by decide)
  unfold completedMatrixRealizer
  obtain ⟨p,hp,hpb⟩ := Math115.ScalarOutputDegree.typed_composition_from_output_size hprep typed_completedMatrixMap
    (4*X^2+3*X+2) degree_rangeArgument rowArgument_output
  refine ⟨p,(by simpa using hp),fun z => ?_⟩
  simpa only [completedMatrix,Function.comp_apply,id_eq] using hpb z

/-- Independent cubic output bound, unconditional even for invalid completions. -/
lemma completedMatrix_output (z : CompletionData) :
    weight (completedMatrix z) ≤ (80*X^3+62*X^2+2*X+1 : Polynomial ℕ).eval (weight z) := by
  have hh := weight_map_bound (as:=completionRows z) (f:=fun i => completedRow (z,i))
    (N:=weight z*(80*weight z+62)+1) (fun i hi => completedRow_weight z i)
  have hl : (completionRows z).length ≤ weight z := by
    simpa only [completionRows,List.length_range] using
      (list_length_le_weight z.1.1).trans ((weight_fst _).trans (weight_fst _))
  have hp := Nat.mul_le_mul_right (weight z*(80*weight z+62)+2) hl
  unfold completedMatrix
  simp only [eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
  nlinarith

#check typed_completedMatrix
#print axioms typed_completedMatrix
#check completedMatrix_output
#print axioms completedMatrix_output
end
end Math115.CompletionRuntimeNext
