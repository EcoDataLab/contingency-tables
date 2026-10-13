import UnitRuntime.RefinedExchangeDegree
import ReferenceRuntime.DecoderDegree
import OAI.Combinatorics.ContingencyTables.Sampling.OuterTrialProgram
import DrawRuntime.BranchDegree
namespace Math115.UnitRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds ProfilePrograms DensePrograms
noncomputable section

lemma typed_indexStep {A : Type} [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A]
    {E : Realizer (fun x : A×A=>decide (x.1=x.2))} {e : ℕ}
    (hE : Typed E e) (he : 1≤e) : Typed (indexStepRealizer E) e := by
  unfold indexStepRealizer Realizer.fst Realizer.snd
  apply typed_congr
  exact Math115.DrawDegree.typed_weaken
    (typed_pair (typed_composition typed_second typed_first)
      (Math115.DrawDegree.typed_choose
        (typed_composition (typed_pair (typed_composition typed_second typed_first) typed_first) hE)
        (typed_constant 0)
        (typed_composition (typed_composition typed_second typed_second) Math115.ReferenceRuntimeNext.typed_successor)))
    (by simp; omega)

lemma typed_indexFold {A : Type} [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A]
    {E : Realizer (fun x : A×A=>decide (x.1=x.2))} {e : ℕ}
    (hE : Typed E e) (he : 1≤e) : Typed (fold (indexStepRealizer E)) (1+e) := by
  suffices h : Typed (fold (indexStepRealizer E)) (1+e*1) by
    simpa only [Nat.mul_one] using h
  apply typed_fold (e:=e) (s:=1) (typed_indexStep hE he) (10*X+20)
    (by simpa using degree_affine 10 20) he (by decide)
  rintro xs ⟨a,i⟩ pre post hsplit
  have hp := (list_length_le_weight pre).trans (weight_prefix hsplit)
  have hb := indexStep_fold_le pre a i
  have hi := Nat.size_le_size hb
  have hs := nat_size_add i pre.length
  have hn : pre.length.size≤pre.length := Nat.size_le.mpr Nat.lt_two_pow_self
  rw [←Prod.eta (pre.foldl _ (a,i)),weight_prod,indexStep_fold_first]
  have hw := weight_nat_le (pre.foldl (fun z x=>indexStep (x,z)) (a,i)).2
  have ha := weight_pos a
  have hn' := size_le_weight i
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  omega

lemma typed_indexOf {A : Type} [Codec A] [DecidableEq A] [BEq A] [LawfulBEq A]
    {E : Realizer (fun x : A×A=>decide (x.1=x.2))} {e : ℕ}
    (hE : Typed E e) (he : 1≤e) : Typed (indexOf E) (2*(1+e)) := by
  unfold indexOf
  apply typed_congr
  exact Math115.DrawDegree.typed_weaken
    (typed_composition (typed_composition
      (typed_pair (typed_composition typed_second Math115.DegreeBounds.typed_reverse)
        (typed_pair typed_first (typed_constant 0))) (typed_indexFold hE he)) typed_second)
    (by simp; omega)

lemma typed_pairNatEqual : Typed (pairEqual natEqual natEqual) 1 := by
  unfold pairEqual Realizer.fst Realizer.snd
  apply typed_congr
  exact typed_composition
    (typed_pair
      (typed_composition (typed_pair (typed_composition typed_first typed_first)
        (typed_composition typed_second typed_first)) Math115.RetryRuntimeNext.typed_natEqual)
      (typed_composition (typed_pair (typed_composition typed_first typed_second)
        (typed_composition typed_second typed_second)) Math115.RetryRuntimeNext.typed_natEqual)) typed_boolAnd

lemma typed_cellLookup : Typed cellLookupRealizer 4 := by
  unfold cellLookupRealizer
  exact typed_indexOf typed_pairNatEqual (by decide)

lemma typed_terminalMatrixEntry : Typed DensePrograms.matrixEntryRealizer 4 := by
  unfold DensePrograms.matrixEntryRealizer
  exact typed_composition
    (typed_pair
      (typed_composition (typed_pair typed_first (typed_composition typed_second typed_first))
        (Math115.RetryRuntimeNext.typed_getDFast ([] : List ℕ)))
      (typed_composition typed_second typed_second)) (Math115.RetryRuntimeNext.typed_getDFast 0)

lemma typed_patternIndices : Typed patternIndices 3 := by
  unfold patternIndices
  apply Math115.RetryRuntimeNext.typed_boundedRange (d:=1)
    (typed_composition (typed_composition typed_first typed_first) Math115.RetryRuntimeNext.typed_listLength_seed)
    X (by simp)
  intro z
  simp only [Function.comp_apply,eval_X]
  exact (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

lemma typed_pairSum : Typed pairSumRealizer 2 := by
  unfold pairSumRealizer
  exact typed_composition
    (typed_pair
      (typed_composition (typed_pair (typed_composition (typed_composition typed_first typed_first) typed_first)
        typed_second) (Math115.RetryRuntimeNext.typed_getDFast 0))
      (typed_composition (typed_pair (typed_composition (typed_composition typed_first typed_first) typed_second)
        typed_second) (Math115.RetryRuntimeNext.typed_getDFast 0))) typed_add

lemma typed_balancedAt : Typed balancedAtRealizer 2 := by
  unfold balancedAtRealizer
  exact typed_composition (typed_pair typed_pairSum (typed_composition typed_first typed_second))
    Math115.RetryRuntimeNext.typed_natEqual

lemma typed_balancedTest : Typed balancedTestRealizer 504 := by
  unfold balancedTestRealizer
  apply typed_congr
  exact typed_composition
    (typed_composition (typed_pair typed_identity typed_patternIndices)
      (Math115.RetryRuntimeNext.typed_mapWith typed_balancedAt (by decide))) Math115.ReferenceRuntimeNext.typed_all

lemma typed_completionRows : Typed completionRowsRealizer 3 := by
  unfold completionRowsRealizer
  apply Math115.RetryRuntimeNext.typed_boundedRange (d:=1)
    (typed_composition (typed_composition typed_first typed_first) Math115.RetryRuntimeNext.typed_listLength_seed)
    X (by simp)
  intro z
  simp only [Function.comp_apply,eval_X]
  exact (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))

lemma typed_completionColumns : Typed completionColumnsRealizer 3 := by
  unfold completionColumnsRealizer
  apply Math115.RetryRuntimeNext.typed_boundedRange (d:=1)
    (typed_composition (typed_composition typed_first typed_second) Math115.RetryRuntimeNext.typed_listLength_seed)
    X (by simp)
  intro z
  simp only [Function.comp_apply,eval_X]
  exact (list_length_le_weight z.1.2).trans ((weight_snd z.1).trans (weight_fst z))

end
end Math115.UnitRuntimeNext
