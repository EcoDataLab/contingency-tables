import ReferenceRuntime.DenseLayoutDegree

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds DensePrograms ProfilePrograms
set_option maxHeartbeats 1200000
noncomputable section

lemma typed_denseMinimum : Typed minimum 1 := by
  unfold minimum
  exact typed_congr _ (typed_choose Math115.DivisionRuntimeNext.typed_less_actual typed_first typed_second)

lemma typed_denseColumnRead : Typed columnReadRealizer 2 := by
  unfold columnReadRealizer
  exact typed_composition (typed_pair typed_second typed_first) (Math115.DrawRuntimeNext.typed_getDFast 0)

lemma typed_denseColumnTotal : Typed columnTotalRealizer 42 := by
  unfold columnTotalRealizer
  exact typed_composition
    (typed_composition (typed_pair typed_second typed_first)
      (Math115.DrawDegree.typed_mapWith typed_denseColumnRead (by decide)))
    Math115.WordCountSeedDegrees.typed_listSum_seed

lemma typed_denseRowTotal : Typed rowTotalRealizer 6 := by
  unfold rowTotalRealizer
  exact typed_composition (Math115.DrawRuntimeNext.typed_getDFast []) Math115.WordCountSeedDegrees.typed_listSum_seed

lemma typed_denseMatrixTotal : Typed matrixTotalRealizer 78 := by
  unfold matrixTotalRealizer
  exact typed_composition (Math115.DrawDegree.typed_map Math115.WordCountSeedDegrees.typed_listSum_seed (by decide))
    Math115.WordCountSeedDegrees.typed_listSum_seed

lemma typed_denseMatrixEntry : Typed matrixEntryRealizer 4 := by
  unfold matrixEntryRealizer
  exact typed_composition
    (typed_pair
      (typed_composition (typed_pair typed_first (typed_composition typed_second typed_first))
        (Math115.DrawRuntimeNext.typed_getDFast []))
      (typed_composition typed_second typed_second)) (Math115.DrawRuntimeNext.typed_getDFast 0)

lemma typed_completionParts : Typed completionPartsRealizer 78 := by
  have hR : Typed (composition
      (composition (first (A:=CompletionData) (B:=ℕ×ℕ)) first) first) 1 :=
    typed_composition (typed_composition typed_first typed_first) typed_first
  have hC : Typed (composition
      (composition (first (A:=CompletionData) (B:=ℕ×ℕ)) first) second) 1 :=
    typed_composition (typed_composition typed_first typed_first) typed_second
  have hZ : Typed (composition (first (A:=CompletionData) (B:=ℕ×ℕ)) second) 1 :=
    typed_composition typed_first typed_second
  have hI : Typed (composition (second (A:=CompletionData) (B:=ℕ×ℕ)) first) 1 :=
    typed_composition typed_second typed_first
  have hJ : Typed (composition (second (A:=CompletionData) (B:=ℕ×ℕ)) second) 1 :=
    typed_composition typed_second typed_second
  have hi := typed_composition (typed_pair hI (typed_constant 0)) Math115.ListRepeatDegreeV1.typed_natEqual
  have hj := typed_composition (typed_pair hJ (typed_constant 0)) Math115.ListRepeatDegreeV1.typed_natEqual
  have him := typed_composition (typed_pair hI (typed_constant 1)) Math115.DivisionRuntimeNext.typed_subtract_actual
  have hjm := typed_composition (typed_pair hJ (typed_constant 1)) Math115.DivisionRuntimeNext.typed_subtract_actual
  have hr := typed_composition (typed_pair hR hI) (Math115.DrawRuntimeNext.typed_getDFast 0)
  have hc := typed_composition (typed_pair hC hJ) (Math115.DrawRuntimeNext.typed_getDFast 0)
  have hrs := typed_composition (typed_pair hZ him) typed_denseRowTotal
  have hcs := typed_composition (typed_pair hZ hjm) typed_denseColumnTotal
  have ht := typed_pair
    (typed_composition (typed_pair (typed_composition hR (Math115.ListRepeatDegreeV1.typed_head 0))
      (typed_composition hZ typed_denseMatrixTotal)) typed_add)
    (typed_composition (typed_composition hC Math115.ListRepeatDegreeV1.typed_tail) Math115.WordCountSeedDegrees.typed_listSum_seed)
  have he := typed_pair
    (typed_composition (typed_pair hZ (typed_pair him hjm)) typed_denseMatrixEntry) (typed_constant 0)
  unfold completionPartsRealizer
  exact typed_congr _ (typed_choose hi (typed_choose hj ht (typed_pair hc hcs))
    (typed_choose hj (typed_pair hr hrs) he))

lemma typed_exponentCellData : Typed exponentCellDataRealizer 78 := by
  unfold exponentCellDataRealizer
  exact typed_pair
    (typed_pair (typed_composition typed_first typed_second)
      (typed_composition
        (typed_pair
          (typed_composition
            (typed_pair (typed_composition (typed_composition (typed_composition typed_first typed_first) typed_first) typed_first)
              (typed_composition typed_second typed_first)) (Math115.DrawRuntimeNext.typed_getDFast 0))
          (typed_composition
            (typed_pair (typed_composition (typed_composition (typed_composition typed_first typed_first) typed_first) typed_second)
              (typed_composition typed_second typed_second)) (Math115.DrawRuntimeNext.typed_getDFast 0)))
        typed_denseMinimum))
    (typed_composition (typed_pair (typed_composition typed_first typed_first) typed_second) typed_completionParts)

lemma typed_denseEighthPower : Typed eighthPower 216 := by
  unfold eighthPower
  exact typed_congr _ (typed_composition typed_completionFourthPower typed_completionSquare)

lemma typed_shiftedCell : Typed shiftedCellRealizer 1 := by
  unfold shiftedCellRealizer
  exact typed_pair typed_first (typed_pair
    (typed_composition (typed_composition typed_second typed_first) typed_successor)
    (typed_composition (typed_composition typed_second typed_second) typed_successor))

/-- Eager exponent-cell preparation is retained although only its width
projection is used. The quotient is the original binary division program. -/
theorem typed_gridCellWidth : Typed gridCellWidthRealizer 864 := by
  unfold gridCellWidthRealizer
  exact typed_composition
    (typed_pair
      (typed_composition (typed_composition (typed_composition typed_shiftedCell typed_exponentCellData) typed_first) typed_second)
      (typed_composition (typed_composition typed_first typed_second) typed_denseEighthPower))
    Math115.DivisionRuntimeNext.typed_quotient

lemma typed_offsetLength : Typed offsetLengthRealizer 1728 := by
  unfold offsetLengthRealizer
  exact typed_composition
    (typed_pair
      (typed_composition
        (typed_composition
          (typed_composition (typed_pair (typed_composition typed_first typed_first) typed_second) typed_gridCellWidth)
          typed_successor) Math115.WordCountSeedDegrees.typed_ceilLogTwo_seed)
      (typed_composition
        (typed_pair (typed_constant 4)
          (typed_composition (typed_pair (typed_composition typed_first typed_second)
            (typed_composition (typed_composition typed_first typed_first) typed_second)) typed_add)) typed_multiply)) typed_add

lemma typed_freeCells : Typed freeCellsRealizer 504 := by
  unfold freeCellsRealizer
  exact typed_composition
    (typed_pair
      (typed_composition (typed_composition (typed_composition (typed_composition typed_first typed_first) typed_first) typed_first)
        Math115.ListRepeatDegreeV1.typed_tail)
      (typed_composition (typed_composition (typed_composition (typed_composition typed_first typed_first) typed_first) typed_second)
        Math115.ListRepeatDegreeV1.typed_tail)) Math115.CatalogueDegreeV1.typed_cellPairs

theorem typed_offsetLengths : Typed offsetLengthsRealizer 3011614704 := by
  unfold offsetLengthsRealizer
  exact typed_composition (typed_pair typed_identity typed_freeCells)
    (Math115.DrawDegree.typed_mapWith typed_offsetLength (by decide))

#check typed_gridCellWidth
#print axioms typed_gridCellWidth
#check typed_offsetLengths
#print axioms typed_offsetLengths
end
end Math115.ReferenceRuntimeNext
