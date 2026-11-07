import ReferenceRuntime.DenseAcceptanceDegree
import ReferenceRuntime.DenseExponentDegree

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds DensePrograms ProfilePrograms
set_option maxHeartbeats 1200000
noncomputable section

lemma typed_scaledWord : Typed scaledWordRealizer 144 := by
  unfold scaledWordRealizer
  exact typed_congr _ (typed_composition
    (typed_pair
      (typed_composition (typed_pair typed_first (typed_composition typed_second Math115.UnitRuntimeNext.typed_bitValue)) typed_multiply)
      (typed_composition typed_second typed_bitDenominator)) Math115.DivisionRuntimeNext.typed_quotient)

lemma typed_offsetBits : Typed offsetBitsRealizer 24 := by
  unfold offsetBitsRealizer
  exact typed_composition
    (typed_pair (typed_composition typed_first typed_second)
      (typed_composition
        (typed_pair
          (typed_composition
            (typed_pair (typed_composition typed_second typed_first)
              (typed_composition
                (typed_composition
                  (typed_composition
                    (typed_composition
                      (typed_composition (typed_composition typed_first typed_first) typed_first) typed_first) typed_second)
                  Math115.ListRepeatDegreeV1.typed_tail) Math115.WordCountSeedDegrees.typed_listLength_seed)) typed_multiply)
          (typed_composition typed_second typed_second)) typed_add)) (Math115.DrawRuntimeNext.typed_getDFast [])

lemma typed_offsetFreeEntry : Typed offsetFreeEntryRealizer 124416 := by
  unfold offsetFreeEntryRealizer
  exact typed_composition
    (typed_pair
      (typed_composition (typed_pair (typed_composition typed_first typed_first) typed_second) typed_gridCellValue)
      (typed_composition
        (typed_pair
          (typed_composition (typed_pair (typed_composition typed_first typed_first) typed_second) typed_gridCellWidth)
          typed_offsetBits) typed_scaledWord)) typed_add

lemma typed_offsetRowEntry : Typed offsetRowEntryRealizer 124416 := by
  unfold offsetRowEntryRealizer
  exact typed_composition
    (typed_pair (typed_composition typed_first typed_first)
      (typed_pair (typed_composition typed_first typed_second) typed_second)) typed_offsetFreeEntry

lemma typed_offsetRow : Typed offsetRowRealizer 92876792838 := by
  unfold offsetRowRealizer
  exact typed_composition
    (typed_pair typed_identity (typed_composition (typed_composition typed_first typed_first) typed_scaleColumns))
    (Math115.DrawDegree.typed_mapWith typed_offsetRowEntry (by decide))

/-- Original scaled binary offsets and complete free-matrix construction.
Rows and columns come from stored margin lists; lookup indices are never
substituted for iteration counts, and all invalid inputs remain included. -/
theorem typed_offsetMatrix : Typed offsetMatrixRealizer 51756591887793869322498 := by
  unfold offsetMatrixRealizer
  exact typed_composition (typed_pair typed_identity (typed_composition typed_first typed_scaleRows))
    (Math115.DrawDegree.typed_mapWith typed_offsetRow (by decide))

#check typed_scaledWord
#print axioms typed_scaledWord
#check typed_offsetMatrix
#print axioms typed_offsetMatrix
end
end Math115.ReferenceRuntimeNext
