/- Literal original profile-validator DAGs with numerical Typed annotations.
Lean verifies every bound; no work inequality is assumed. -/
import UnitRuntime.ProfilePatternDegree
namespace Math115.UnitRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds ProfilePrograms
noncomputable section

lemma typed_lineIndices : Typed lineIndices 3 := by
  unfold lineIndices
  apply Math115.RetryRuntimeNext.typed_boundedRange (d:=1)
    (typed_composition (typed_composition typed_first typed_second) Math115.RetryRuntimeNext.typed_listLength_seed)
    X (by simp)
  intro z
  simp only [Function.comp_apply,eval_X]
  exact (list_length_le_weight z.1.2).trans ((weight_snd z.1).trans (weight_fst z))

lemma typed_marginIndices (row : Bool) : Typed (marginIndices row) 3 := by
  unfold marginIndices
  have hm : Typed (marginListRealizer row) 1 := by
    unfold marginListRealizer
    exact Math115.DrawDegree.typed_choose (typed_constant row)
      (typed_composition (typed_composition typed_first typed_second) typed_first)
      (typed_composition (typed_composition typed_first typed_second) typed_second)
  apply Math115.RetryRuntimeNext.typed_boundedRange (d:=1)
    (typed_composition hm Math115.RetryRuntimeNext.typed_listLength_seed) X (by simp)
  intro z
  have hw : weight (marginList row z)≤weight z := by
    rcases z with ⟨⟨lookupData,⟨r,c⟩⟩,U⟩
    cases row <;> simp only [marginList,Bool.false_eq_true,ite_false,ite_true,weight_prod] <;> omega
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight (marginList row z)).trans hw

lemma typed_lookupView  : Typed lookupViewRealizer 8 :=
  typed_composition (typed_pair (typed_composition typed_first typed_second)
    (typed_composition (typed_pair typed_second
      (typed_composition typed_first typed_first)) typed_cellLookup))
    (Math115.RetryRuntimeNext.typed_getDFast 0)


lemma typed_lineEntry (row : Bool) : Typed (lineEntryRealizer row) 8 :=
  typed_composition (typed_pair
    (typed_composition (typed_composition typed_first typed_first) typed_first)
    (Math115.DrawDegree.typed_choose (typed_constant row)
      (typed_pair (typed_composition typed_first typed_second) typed_second)
      (typed_pair typed_second (typed_composition typed_first typed_second))))
    typed_lookupView


lemma typed_lineSum (row : Bool) : Typed (lineSumRealizer row) 1314 :=
  typed_composition (typed_composition
    (typed_pair typed_identity typed_lineIndices)
    (Math115.RetryRuntimeNext.typed_mapWith (typed_lineEntry row) (by decide))) Math115.WordCountSeedDegrees.typed_listSum_seed


lemma typed_marginList (row : Bool) : Typed (marginListRealizer row) 1 :=
  Math115.DrawDegree.typed_choose (typed_constant row)
    (typed_composition (typed_composition typed_first typed_second) typed_first)
    (typed_composition (typed_composition typed_first typed_second) typed_second)


lemma typed_lineArgument (row : Bool) : Typed (lineArgumentRealizer row) 1 :=
  typed_pair (typed_pair
    (typed_composition (typed_composition typed_first typed_first) typed_first)
    (typed_composition typed_first (typed_marginList (!row)))) typed_second


lemma typed_marginValue (row : Bool) : Typed (marginValueRealizer row) 2 :=
  typed_composition (typed_pair
    (typed_composition typed_first (typed_marginList row)) typed_second)
    (Math115.RetryRuntimeNext.typed_getDFast 0)


lemma typed_lineValue (row : Bool) : Typed (lineValueRealizer row) 1314 :=
  typed_composition (typed_lineArgument row) (typed_lineSum row)


lemma typed_validMarginAt (row : Bool) : Typed (validMarginAtRealizer row) 1314 :=
by
  unfold validMarginAtRealizer
  exact typed_congr _ (typed_composition (typed_pair
    (typed_composition (typed_pair (typed_lineValue row)
      (typed_marginValue row)) Math115.RetryRuntimeNext.typed_leNat)
    (Math115.DrawDegree.typed_choose (typed_composition (typed_pair (typed_marginValue row)
      (typed_composition typed_first typed_second)) Math115.RetryRuntimeNext.typed_less)
      (typed_composition (typed_pair (typed_lineValue row)
        (typed_marginValue row)) Math115.RetryRuntimeNext.typed_natEqual) (typed_constant true))) typed_boolAnd)


lemma typed_validMargins (row : Bool) : Typed (validMarginsRealizer row) 124409592 :=
by
  unfold validMarginsRealizer
  exact typed_congr _ (typed_composition (typed_composition
    (typed_pair typed_identity (typed_marginIndices row))
    (Math115.RetryRuntimeNext.typed_mapWith (typed_validMarginAt row) (by decide))) Math115.ReferenceRuntimeNext.typed_all)


end
end Math115.UnitRuntimeNext
