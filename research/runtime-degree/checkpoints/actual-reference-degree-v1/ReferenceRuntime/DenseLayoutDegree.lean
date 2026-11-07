import ReferenceRuntime.CompletionPrepareDegree
import ResearchBounds.SmallCellCatalogueDegree

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds DensePrograms
set_option maxHeartbeats 1200000
noncomputable section

lemma typed_sliceRow : Typed sliceRowRealizer 96 := by
  unfold sliceRowRealizer
  exact typed_composition
    (typed_pair
      (typed_composition
        (typed_pair (typed_composition typed_first typed_second)
          (typed_composition (typed_pair typed_second (typed_composition typed_first typed_first)) typed_multiply))
        Math115.ListRepeatDegreeV1.typed_dropFast)
      (typed_composition typed_first typed_first)) Math115.ListRepeatDegreeV1.typed_takeFast

lemma typed_layoutRows : Typed layoutRowsRealizer 3 := by
  unfold layoutRowsRealizer
  apply Math115.DrawRuntimeNext.typed_boundedRange (e:=2) (d:=1)
    (typed_composition (typed_composition (typed_composition typed_first typed_first)
      Math115.ListRepeatDegreeV1.typed_tail) Math115.WordCountSeedDegrees.typed_listLength_seed) X (by simp)
  intro z
  simp only [Function.comp_apply,eval_X,List.length_tail]
  exact (Nat.sub_le _ _).trans ((list_length_le_weight z.1.1).trans
    ((weight_fst z.1).trans (weight_fst z)))

lemma typed_layoutRow : Typed layoutRowRealizer 192 := by
  unfold layoutRowRealizer
  exact typed_composition
    (typed_pair
      (typed_pair
        (typed_composition
          (typed_composition
            (typed_composition (typed_composition typed_first typed_first) typed_second)
            Math115.ListRepeatDegreeV1.typed_tail) Math115.WordCountSeedDegrees.typed_listLength_seed)
        (typed_composition typed_first typed_second)) typed_second) typed_sliceRow

lemma typed_unflattenGrid : Typed unflattenGridRealizer 222342 := by
  unfold unflattenGridRealizer
  exact typed_composition (typed_pair typed_identity typed_layoutRows)
    (Math115.DrawDegree.typed_mapWith typed_layoutRow (by decide))

/-- The original conversion charges all slices and all constructed rows,
including malformed dimensions and an arbitrary supplied flat list. -/
theorem typed_flatToGridData : Typed flatToGridDataRealizer 222342 := by
  unfold flatToGridDataRealizer
  exact typed_pair
    (typed_pair (typed_composition typed_first typed_first)
      (typed_composition typed_first typed_unflattenGrid)) typed_second

#check typed_unflattenGrid
#print axioms typed_unflattenGrid
#check typed_flatToGridData
#print axioms typed_flatToGridData
end
end Math115.ReferenceRuntimeNext
