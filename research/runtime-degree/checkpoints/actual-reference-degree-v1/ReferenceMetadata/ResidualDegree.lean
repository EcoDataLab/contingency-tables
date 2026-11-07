import InputNormalization.MaximalIndex
import RepairRuntime.OutputHelpers
import ResearchBounds.SmallCellCatalogueDegree
import OAI.Combinatorics.ContingencyTables.Machines.ResidualDenseProgram

namespace Math115.ReferenceMetadata
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds Math115.DrawDegree Math115.CatalogueDegreeV1
open Math115.WordCountSeedDegrees Math115.ListRepeatDegreeV1 Math115.InitialRuntimeNext
open ProfilePrograms
set_option maxHeartbeats 1800000
noncomputable section

lemma typed_cellEqual : Typed (pairEqual natEqual natEqual) 1 := by
  unfold pairEqual Realizer.fst Realizer.snd
  apply typed_congr
  exact typed_composition
    (typed_pair
      (typed_composition (typed_pair (typed_composition typed_first typed_first)
        (typed_composition typed_second typed_first)) typed_natEqual)
      (typed_composition (typed_pair (typed_composition typed_first typed_second)
        (typed_composition typed_second typed_second)) typed_natEqual))
    Math115.DrawRuntimeNext.typed_boolAnd

lemma typed_cellIndexStep : Typed (indexStepRealizer (pairEqual natEqual natEqual)) 1 := by
  unfold indexStepRealizer
  apply typed_congr
  exact typed_pair_same (typed_composition_pos typed_second typed_first (by decide))
    (typed_choose_same
      (typed_composition_pos
        (typed_pair_same (typed_composition_pos typed_second typed_first (by decide)) typed_first (by decide))
        typed_cellEqual (by decide))
      (typed_constant 0)
      (typed_composition_pos (typed_composition_pos typed_second typed_second (by decide))
        (typed_composition_pos (typed_pair_same typed_identity (typed_constant 1) (by decide)) typed_add (by decide))
        (by decide)) (by decide)) (by decide)

lemma typed_cellIndexFold : Typed (fold (indexStepRealizer (pairEqual natEqual natEqual))) 2 := by
  apply typed_fold (e:=1) (s:=1) typed_cellIndexStep (10*X+20)
    (by simpa using degree_affine 10 20) (by decide) (by decide)
  rintro xs ⟨a,i⟩ pre post he
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

lemma typed_cellLookup : Typed cellLookupRealizer 2 := by
  have hp : Typed (pair (composition (second (A:=ℕ×ℕ) (B:=List (ℕ×ℕ))) reverse)
      (pair first (constant 0))) 2 :=
    typed_pair_same (typed_composition_pos typed_second Math115.DegreeBounds.typed_reverse (by decide))
      (typed_weaken (typed_pair_same typed_first (typed_constant 0) (by decide)) (by decide)) (by decide)
  have ha : Math115.PrinterRuntimeNext.AffineOutput
      (fun z : (ℕ×ℕ)×List (ℕ×ℕ) => (z.2.reverse,(z.1,0))) := by
    refine ⟨1,3,?_⟩
    rintro ⟨a,xs⟩
    simp only [one_mul,weight_prod,weight_reverse]
    have hz : weight (0:ℕ)=1 := by decide
    rw [hz]
    omega
  have hb := Math115.PrinterRuntimeNext.typed_comp_affine hp typed_cellIndexFold ha
  unfold cellLookupRealizer indexOf
  apply typed_congr
  simpa using typed_composition_pos hb typed_second (by decide)

lemma typed_lookupView : Typed lookupViewRealizer 4 := by
  unfold lookupViewRealizer
  exact typed_composition
    (typed_pair (typed_composition typed_first typed_second)
      (typed_composition (typed_pair typed_second (typed_composition typed_first typed_first)) typed_cellLookup))
    (typed_getDFast 0)

lemma typed_lineEntry (row : Bool) : Typed (lineEntryRealizer row) 4 := by
  unfold lineEntryRealizer
  exact typed_composition
    (typed_pair (typed_composition (typed_composition typed_first typed_first) typed_first)
      (Math115.DrawDegree.typed_choose (typed_constant row) (typed_pair (typed_composition typed_first typed_second) typed_second)
        (typed_pair typed_second (typed_composition typed_first typed_second)))) typed_lookupView

lemma typed_lineIndices : Typed lineIndices 3 := by
  unfold lineIndices
  apply typed_boundedRange (d:=1)
    (typed_composition (typed_composition typed_first typed_second) typed_listLength_seed) X (by simp)
  intro z
  have h := (list_length_le_weight z.1.2).trans ((weight_snd _).trans (weight_fst _))
  simpa only [Function.comp_apply,eval_X] using h

lemma typed_lineSum (row : Bool) : Typed (lineSumRealizer row) 378 := by
  unfold lineSumRealizer
  exact typed_composition
    (typed_composition (typed_pair typed_identity typed_lineIndices)
      (typed_mapWith (typed_lineEntry row) (by decide))) typed_listSum_seed

lemma typed_marginList (row : Bool) : Typed (marginListRealizer row) 1 := by
  unfold marginListRealizer
  exact Math115.DrawDegree.typed_choose (typed_constant row)
    (typed_composition (typed_composition typed_first typed_second) typed_first)
    (typed_composition (typed_composition typed_first typed_second) typed_second)

lemma typed_lineArgument (row : Bool) : Typed (lineArgumentRealizer row) 1 := by
  unfold lineArgumentRealizer
  exact typed_pair (typed_pair (typed_composition (typed_composition typed_first typed_first) typed_first)
    (typed_composition typed_first (typed_marginList (!row)))) typed_second

lemma typed_marginValue (row : Bool) : Typed (marginValueRealizer row) 2 := by
  unfold marginValueRealizer
  exact typed_composition (typed_pair (typed_composition typed_first (typed_marginList row)) typed_second)
    (typed_getDFast 0)

lemma typed_lineValue (row : Bool) : Typed (lineValueRealizer row) 378 := by
  unfold lineValueRealizer
  exact typed_composition (typed_lineArgument row) (typed_lineSum row)

lemma typed_marginIndices (row : Bool) : Typed (ProfilePrograms.marginIndices row) 3 := by
  unfold ProfilePrograms.marginIndices
  apply typed_boundedRange (d:=1) (typed_composition (typed_marginList row) typed_listLength_seed) X (by simp)
  intro z
  have hw : weight (marginList row z) ≤ weight z := by
    rcases z with ⟨⟨lookupData,⟨r,c⟩⟩,U⟩
    cases row <;> simp only [marginList,Bool.false_eq_true,ite_false,ite_true,weight_prod] <;> omega
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight _).trans hw

lemma typed_largeFlag : Typed largeFlagRealizer 1 := by
  unfold largeFlagRealizer
  apply typed_congr
  exact Math115.DrawDegree.typed_choose typed_leNat (typed_constant 1) (typed_constant 0)

lemma typed_largeCount : Typed largeCountRealizer 18 := by
  unfold largeCountRealizer
  exact typed_composition (typed_mapWith typed_largeFlag (by decide)) typed_listSum_seed

lemma typed_paddedMarginAt (row : Bool) : Typed (paddedMarginAtRealizer row) 648 := by
  have ha : Typed (pair (composition (first (A:=PaddingData) (B:=ℕ)) first) second) 1 :=
    typed_pair (typed_composition typed_first typed_first) typed_second
  have ht : Typed (composition (composition (first (A:=PaddingData) (B:=ℕ)) first) second) 1 :=
    typed_composition (typed_composition typed_first typed_first) typed_second
  unfold paddedMarginAtRealizer
  exact typed_composition (typed_pair
    (typed_composition (typed_pair (typed_composition ha (typed_marginValue row))
      (typed_composition ha (typed_lineValue row))) typed_subtract_actual)
    (typed_composition (typed_pair
      (typed_composition (typed_pair
        (typed_composition (typed_pair ht (typed_composition ha (typed_marginValue row))) typed_largeFlag)
        (typed_composition (typed_pair ht
          (typed_composition (typed_composition typed_first typed_first) (typed_marginList (!row)))) typed_largeCount)) typed_multiply)
      (typed_composition typed_first typed_second)) typed_multiply)) typed_add

lemma typed_paddedMargins (row : Bool) : Typed (paddedMarginsRealizer row) 2523318 := by
  unfold paddedMarginsRealizer
  exact typed_composition (typed_pair typed_identity (typed_composition typed_first (typed_marginIndices row)))
    (typed_mapWith (typed_paddedMarginAt row) (by decide))

lemma typed_largeIndexTest : Typed largeIndexTestRealizer 2 := by
  unfold largeIndexTestRealizer
  exact typed_composition (typed_pair (typed_composition typed_first typed_first)
    (typed_composition (typed_pair (typed_composition typed_first typed_second) typed_second) (typed_getDFast 0))) typed_leNat

lemma typed_largeIndices : Typed largeIndicesRealizer 12 := by
  have hr : Typed (composition (composition (second (A:=ℕ) (B:=List ℕ)) listLength) range) 3 := by
    apply typed_boundedRange (d:=1) (typed_composition typed_second typed_listLength_seed) X (by simp)
    intro z
    simpa only [Function.comp_apply,eval_X] using (list_length_le_weight z.2).trans (weight_snd z)
  unfold largeIndicesRealizer
  exact typed_composition (typed_pair typed_identity hr)
    (Math115.RepairRuntimeNext.typed_filterWith_output typed_largeIndexTest (by decide))

lemma typed_selectList : Typed (selectListRealizer (0:ℕ)) 14 := by
  unfold selectListRealizer
  exact typed_composition (typed_pair typed_second typed_first) (typed_mapWith (typed_getDFast 0) (by decide))

lemma typed_largePaddedMargins (row : Bool) : Typed (largePaddedMarginsRealizer row) 35326452 := by
  unfold largePaddedMarginsRealizer
  exact typed_composition (typed_pair
    (typed_composition (typed_pair (typed_composition typed_first typed_second)
      (typed_composition typed_first (typed_marginList row))) typed_largeIndices)
    (typed_paddedMargins row)) typed_selectList

lemma typed_complementValues : Typed complementValuesRealizer 6 := by
  unfold complementValuesRealizer
  exact typed_mapWith typed_subtract_actual (by decide)

lemma typed_profileViews : Typed profileViews 1 := by
  unfold profileViews
  exact typed_composition (typed_composition typed_first typed_first) typed_second

lemma typed_profileCatalog : Typed profileCatalog 1 := by
  unfold profileCatalog
  exact typed_composition (typed_composition typed_first typed_first) typed_first

lemma typed_profileMargins : Typed profileMargins 1 := by
  unfold profileMargins
  exact typed_composition typed_first typed_second

lemma typed_profileView (row : Bool) : Typed (profileView row) 1 := by
  unfold profileView
  exact Math115.DrawDegree.typed_choose (typed_constant row) (typed_composition typed_profileViews typed_first)
    (typed_composition typed_profileViews typed_second)

lemma typed_profileColumnView : Typed profileColumnView 6 := by
  unfold profileColumnView
  exact typed_composition (typed_pair typed_second (typed_composition typed_profileViews typed_second)) typed_complementValues

lemma typed_profileLineData (row : Bool) : Typed (profileLineData row) 6 := by
  unfold profileLineData
  exact typed_pair (typed_pair (typed_pair typed_profileCatalog
    (Math115.DrawDegree.typed_choose (typed_constant row) (typed_profileView true) typed_profileColumnView)) typed_profileMargins) typed_second

lemma typed_profilePaddedMargins (row : Bool) : Typed (profilePaddedMarginsRealizer row) 211958712 := by
  unfold profilePaddedMarginsRealizer
  exact typed_composition (typed_pair (typed_composition typed_first (typed_profileLineData row)) typed_second)
    (typed_largePaddedMargins row)

/-- Exact original residual preparation for every raw tuple, including
unvalidated profiles, duplicate/missing cells, empty lists and underflows. -/
theorem typed_residualParameters : Typed residualParametersRealizer 211958712 := by
  unfold residualParametersRealizer
  exact typed_pair (typed_pair
    (typed_composition typed_first (typed_profilePaddedMargins true))
    (typed_composition typed_first (typed_profilePaddedMargins false))) typed_second

#check typed_residualParameters
#print axioms typed_residualParameters
end
end Math115.ReferenceMetadata
