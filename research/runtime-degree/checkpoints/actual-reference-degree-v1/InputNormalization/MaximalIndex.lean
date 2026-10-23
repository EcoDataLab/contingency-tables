import InitialRuntime.GreedyDegree
import DrawRuntime.BranchDegree
import OAI.Combinatorics.ContingencyTables.Machines.MaximalListProgram

namespace Math115.InputNormalization
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open DensePrograms Math115.DegreeBounds Math115.DrawDegree Math115.InitialRuntimeNext
open Math115.ListRepeatDegreeV1
noncomputable section

lemma typed_maximum : Typed maximum 1 := by
  unfold maximum
  apply typed_congr
  exact Math115.DegreeBounds.typed_choose typed_less_actual typed_second typed_first

lemma typed_listMaximum : Typed listMaximumRealizer 2 := by
  unfold listMaximumRealizer
  apply typed_fold (e:=1) (s:=1) typed_maximum (4*X+1)
    (by simpa using degree_affine 4 1) (by decide) (by decide)
  intro xs a pre post he
  let S := weight (xs,a)
  have ha : a.size ≤ S := (size_le_weight a).trans (weight_snd (xs,a))
  have hb : ∀ b ∈ pre,b.size ≤ S := by
    intro b hb
    exact (size_le_weight b).trans ((weight_mem (as:=xs) (by simp [he,hb])).trans (weight_fst (xs,a)))
  have hs := foldMaximum_size pre a S ha hb
  have hw := weight_nat_le (pre.foldl (fun a b => max b a) a)
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  change _ ≤ 4*S+1
  omega

lemma typed_indexStep : Typed (indexStepRealizer (A:=ℕ) natEqual) 1 := by
  unfold indexStepRealizer
  apply typed_congr
  exact typed_pair_same (typed_composition_pos typed_second typed_first (by decide))
    (typed_choose_same
      (typed_composition_pos
        (typed_pair_same (typed_composition_pos typed_second typed_first (by decide)) typed_first (by decide))
        typed_natEqual (by decide))
      (typed_constant 0)
      (typed_composition_pos (typed_composition_pos typed_second typed_second (by decide))
        (typed_composition_pos (typed_pair_same typed_identity (typed_constant 1) (by decide)) typed_add (by decide))
        (by decide)) (by decide)) (by decide)

lemma indexFold_intermediate (xs : List ℕ) (a i : ℕ) (pre post : List ℕ) (he : xs=pre++post) :
    weight (pre.foldl (fun z x => indexStep (x,z)) (a,i)) ≤
      (10*X+20 : Polynomial ℕ).eval (weight (xs,(a,i))) := by
  have hp := (list_length_le_weight pre).trans (weight_prefix he)
  have hb := indexStep_fold_le pre a i
  have hi := Nat.size_le_size hb
  have hs := nat_size_add i pre.length
  have hn : pre.length.size ≤ pre.length := Nat.size_le.mpr Nat.lt_two_pow_self
  rw [←Prod.eta (pre.foldl _ (a,i)),weight_prod,indexStep_fold_first]
  have hw := weight_nat_le (pre.foldl (fun z x => indexStep (x,z)) (a,i)).2
  have hn' := size_le_weight i
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  omega

lemma typed_indexFold : Typed (fold (indexStepRealizer (A:=ℕ) natEqual)) 2 := by
  apply typed_fold (e:=1) (s:=1) typed_indexStep (10*X+20)
    (by simpa using degree_affine 10 20) (by decide) (by decide)
  rintro xs ⟨a,i⟩ pre post he
  exact indexFold_intermediate xs a i pre post he

lemma typed_indexOf : Typed (indexOf (A:=ℕ) natEqual) 2 := by
  have hp : Typed (pair (composition (second (A:=ℕ) (B:=List ℕ)) reverse)
      (pair first (constant 0))) 2 :=
    typed_pair_same (typed_composition_pos typed_second Math115.DegreeBounds.typed_reverse (by decide))
      (typed_weaken (typed_pair_same typed_first (typed_constant 0) (by decide)) (by decide)) (by decide)
  have ha : Math115.PrinterRuntimeNext.AffineOutput (fun z : ℕ×List ℕ => (z.2.reverse,(z.1,0))) := by
    refine ⟨1,3,?_⟩
    rintro ⟨a,xs⟩
    simp only [one_mul,weight_prod,weight_reverse]
    have hz : weight (0:ℕ)=1 := by decide
    rw [hz]
    omega
  have hb := Math115.PrinterRuntimeNext.typed_comp_affine hp typed_indexFold ha
  unfold indexOf
  apply typed_congr
  simpa using typed_composition_pos hb typed_second (by decide)

lemma maximumIndex_argument_affine : Math115.PrinterRuntimeNext.AffineOutput
    (fun xs : List ℕ => (listMaximum (xs,0),xs)) := by
  refine ⟨2,2,fun xs => ?_⟩
  have hh : weight (listMaximum (xs,0)) ≤ weight xs+1 := by
    rcases listMaximum_mem_or_default xs 0 with he | hm
    · rw [he]
      have hz : weight (0:ℕ)=1 := by decide
      rw [hz]
      omega
    · exact (weight_mem hm).trans (by omega)
  rw [weight_prod]
  omega

/-- Actual two-pass maximum/first-index selection over every natural list,
including empty inputs and zeros; intermediate counters and output retained. -/
theorem typed_maximumIndex : Typed maximumIndexRealizer 2 := by
  have hstart : Typed (pair (identity (A:=List ℕ)) (constant (A:=List ℕ) (0:ℕ))) 1 :=
    typed_pair_same typed_identity (typed_constant 0) (by decide)
  have hf : Typed (composition (pair (identity (A:=List ℕ)) (constant 0)) listMaximumRealizer) 2 :=
    typed_composition_pos hstart typed_listMaximum (by decide)
  have hp : Typed (pair (composition (pair (identity (A:=List ℕ)) (constant 0)) listMaximumRealizer)
      (identity (A:=List ℕ))) 2 :=
    typed_pair_same hf (typed_weaken typed_identity (by decide)) (by decide)
  unfold maximumIndexRealizer
  obtain ⟨p,hp,hpb⟩ := Math115.PrinterRuntimeNext.typed_comp_affine hp typed_indexOf maximumIndex_argument_affine
  refine ⟨p,(by simpa using hp),fun xs => ?_⟩
  simpa only [maximumIndex,listMaximum,Function.comp_apply,id_eq] using hpb xs

end
end Math115.InputNormalization
