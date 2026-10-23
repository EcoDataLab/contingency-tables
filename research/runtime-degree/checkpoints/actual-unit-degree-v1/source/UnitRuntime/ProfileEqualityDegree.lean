/- Exact profile equality and duplicate removal used by codeNeighbors and
inverse-label verification. Arbitrary literal lists and all accumulator weights
are charged; no physical-state premise is needed. -/
import UnitRuntime.TerminalDegree
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileCodeEquality
namespace Math115.UnitRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds ProfilePrograms
noncomputable section

lemma typed_profileIndices : Typed profileIndices 3 := by
  unfold profileIndices
  apply Math115.RetryRuntimeNext.typed_boundedRange (d:=1)
    Math115.RetryRuntimeNext.typed_listLength_seed X (by simp)
  intro xs
  simp only [eval_X]
  exact list_length_le_weight xs

lemma typed_listEntryEqual : Typed listEntryEqualRealizer 2 := by
  unfold listEntryEqualRealizer
  exact typed_composition
    (typed_pair
      (typed_composition (typed_pair (typed_composition typed_first typed_first) typed_second)
        (Math115.RetryRuntimeNext.typed_getDFast 0))
      (typed_composition (typed_pair (typed_composition typed_first typed_second) typed_second)
        (Math115.RetryRuntimeNext.typed_getDFast 0))) Math115.RetryRuntimeNext.typed_natEqual

lemma typed_equalityIndices : Typed equalityIndices 3 := by
  unfold equalityIndices
  exact typed_composition typed_first typed_profileIndices

lemma typed_listNatTest : Typed listNatTestRealizer 504 := by
  unfold listNatTestRealizer
  apply typed_congr
  exact typed_composition
    (typed_pair
      (typed_composition (typed_pair
        (typed_composition typed_first Math115.RetryRuntimeNext.typed_listLength_seed)
        (typed_composition typed_second Math115.RetryRuntimeNext.typed_listLength_seed))
        Math115.RetryRuntimeNext.typed_natEqual)
      (typed_composition
        (typed_composition (typed_pair typed_identity typed_equalityIndices)
          (Math115.RetryRuntimeNext.typed_mapWith typed_listEntryEqual (by decide)))
        Math115.ReferenceRuntimeNext.typed_all)) typed_boolAnd

lemma typed_listNatEqual : Typed listNatEqual 504 := by
  unfold listNatEqual
  exact typed_congr _ typed_listNatTest

lemma typed_profileCodeEqual : Typed profileCodeEqual 504 := by
  unfold profileCodeEqual pairEqual Realizer.fst Realizer.snd
  apply typed_congr
  exact typed_composition
    (typed_pair
      (typed_composition (typed_pair (typed_composition typed_first typed_first)
        (typed_composition typed_second typed_first)) typed_listNatEqual)
      (typed_composition (typed_pair (typed_composition typed_first typed_second)
        (typed_composition typed_second typed_second)) typed_listNatEqual)) typed_boolAnd

lemma typed_contains {A : Type} [Codec A] [DecidableEq A]
    {E : Realizer (fun x : A×A=>decide (x.1=x.2))} {e : ℕ}
    (hE : Typed E e) (he : 1≤e) : Typed (contains E) (4*(1+e*(e+1))) := by
  unfold contains
  apply typed_congr
  exact Math115.DrawDegree.typed_weaken
    (typed_composition (Math115.RetryRuntimeNext.typed_mapWith hE he)
      Math115.ReferenceRuntimeNext.typed_any) (by simp; omega)

lemma typed_profileDedupStep : Typed (dedupStepRealizer profileCodeEqual) 1018084 := by
  unfold dedupStepRealizer
  apply typed_congr
  exact Math115.DrawDegree.typed_choose
    (typed_contains typed_profileCodeEqual (by decide)) typed_second typed_listCons_arithmetic

lemma typed_profileDedupFold : Typed (fold (dedupStepRealizer profileCodeEqual)) 1018085 := by
  apply typed_fold (e:=1018084) (s:=1) typed_profileDedupStep (2*X+1)
    (by simpa using degree_affine 2 1) (by decide) (by decide)
  intro as bs pre post hsplit
  have hfold := weight_dedupFold pre bs
  have hprefix := weight_prefix hsplit
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  omega

/-- Exact canonical duplicate-removal program, retaining arbitrary input-list
and starting-accumulator encoding costs in the fold certificate. -/
theorem typed_profileCodeDedup : Typed profileCodeDedup 2036170 := by
  unfold profileCodeDedup dedup
  apply typed_congr
  exact typed_composition
    (typed_pair Math115.DegreeBounds.typed_reverse (typed_constant ([] : List (List ℕ×List ℕ))))
    typed_profileDedupFold

lemma profileCodeDedup_output_weight (xs : List (List ℕ×List ℕ)) :
    weight xs.dedup≤weight xs := weight_sublist (List.dedup_sublist xs)

end
end Math115.UnitRuntimeNext
