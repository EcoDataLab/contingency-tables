/- Typed proofs follow the literal original terminal program DAG. All generated numerical annotations are compiler-checked. -/
import UnitRuntime.TerminalIndexDegree
namespace Math115.UnitRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds ProfilePrograms DensePrograms
noncomputable section

lemma typed_outputCellPosition : Typed outputCellPositionRealizer 4 :=
  typed_composition (typed_pair typed_second
    (typed_composition (typed_composition
      (typed_composition typed_first typed_first) typed_first) typed_first))
    typed_cellLookup


lemma typed_outputSmallEntry : Typed outputSmallEntryRealizer 8 :=
  typed_composition (typed_pair
    (typed_composition (typed_composition (typed_composition
      (typed_composition typed_first typed_first) typed_first) typed_second)
      typed_first) typed_outputCellPosition) (Math115.RetryRuntimeNext.typed_getDFast 0)


lemma typed_outputDensePosition : Typed outputDensePositionRealizer 4 :=
  typed_pair
    (typed_composition (typed_pair (typed_composition typed_second typed_first)
      (typed_composition (typed_composition
        (typed_composition typed_first typed_first) typed_second) typed_first))
      (typed_indexOf Math115.RetryRuntimeNext.typed_natEqual (by decide)))
    (typed_composition (typed_pair (typed_composition typed_second typed_second)
      (typed_composition (typed_composition
        (typed_composition typed_first typed_first) typed_second) typed_second))
      (typed_indexOf Math115.RetryRuntimeNext.typed_natEqual (by decide)))


lemma typed_outputLargeEntry : Typed outputLargeEntryRealizer 16 :=
  typed_composition (typed_pair
    (typed_composition (typed_pair
      (typed_composition (typed_composition typed_first typed_second) typed_second)
      typed_outputDensePosition) typed_terminalMatrixEntry)
    (typed_composition (typed_composition
      (typed_composition typed_first typed_second) typed_first) typed_second))
    Math115.RetryRuntimeNext.typed_subtract_seed


lemma typed_outputEntry : Typed outputEntryRealizer 16 :=
  typed_congr _ (Math115.DrawDegree.typed_choose
    (typed_composition (typed_pair typed_outputCellPosition
      (typed_composition (typed_composition (typed_composition
        (typed_composition typed_first typed_first) typed_first) typed_first)
        Math115.RetryRuntimeNext.typed_listLength_seed)) Math115.RetryRuntimeNext.typed_less)
    typed_outputSmallEntry typed_outputLargeEntry)


lemma typed_paddingTest : Typed paddingTestRealizer 126168 :=
  typed_congr _ (typed_composition
    (Math115.RetryRuntimeNext.typed_mapWith (typed_composition (Math115.RetryRuntimeNext.typed_mapWith Math115.RetryRuntimeNext.typed_leNat (by decide)) Math115.ReferenceRuntimeNext.typed_all) (by decide))
    Math115.ReferenceRuntimeNext.typed_all)


lemma typed_outerSuccess : Typed outerSuccessRealizer 126168 :=
  typed_composition (typed_pair
    (typed_composition (typed_pair
      (typed_composition (typed_composition typed_first typed_first) typed_second)
      (typed_composition (typed_composition typed_second typed_first) typed_first))
      typed_balancedTest)
    (typed_composition (typed_pair
      (typed_composition (typed_composition typed_second typed_first) typed_second)
      (typed_composition typed_second typed_second)) typed_paddingTest)) typed_boolAnd


lemma typed_outputShape : Typed outputShapeRealizer 1 :=
  typed_pair typed_first (typed_constant [])


lemma typed_outputRows : Typed outputRowsRealizer 3 :=
  typed_composition typed_outputShape typed_completionRows

lemma typed_outputColumns : Typed outputColumnsRealizer 3 :=
  typed_composition typed_outputShape typed_completionColumns


lemma typed_outputRowEntry : Typed outputRowEntryRealizer 16 :=
  typed_composition (typed_pair
    (typed_composition (typed_composition typed_first typed_first) typed_second)
    (typed_pair (typed_composition typed_first typed_second) typed_second))
    typed_outputEntry


lemma typed_outputRow : Typed outputRowRealizer 1638 :=
  typed_composition (typed_pair typed_identity
    (typed_composition typed_first typed_outputColumns))
    (Math115.RetryRuntimeNext.typed_mapWith typed_outputRowEntry (by decide))


lemma typed_outputMatrix : Typed outputMatrixRealizer 16108098 :=
  typed_composition (typed_pair typed_identity typed_outputRows)
    (Math115.RetryRuntimeNext.typed_mapWith typed_outputRow (by decide))


lemma typed_acceptedTable : Typed acceptedTableRealizer 16108098 :=
  Math115.DrawDegree.typed_choose (typed_composition typed_second typed_outerSuccess)
    (typed_composition typed_outputMatrix typed_some) (typed_constant none)


lemma typed_outputLargeRows : Typed outputLargeRowsRealizer 1008 :=
  typed_composition (typed_pair
    (typed_composition (typed_composition typed_first typed_first) typed_second)
    (typed_composition (typed_composition (typed_composition
      (typed_composition typed_first typed_first) typed_first) typed_second)
      typed_first)) Math115.DrawRuntimeNext.typed_largeIndices

lemma typed_outputLargeColumns : Typed outputLargeColumnsRealizer 1008 :=
  typed_composition (typed_pair
    (typed_composition (typed_composition typed_first typed_first) typed_second)
    (typed_composition (typed_composition (typed_composition
      (typed_composition typed_first typed_first) typed_first) typed_second)
      typed_second)) Math115.DrawRuntimeNext.typed_largeIndices


lemma typed_outputData : Typed outputDataRealizer 1008 :=
  typed_pair (typed_pair
    (typed_composition (typed_composition
      (typed_composition typed_first typed_first) typed_first) typed_first)
    (typed_pair typed_outputLargeRows typed_outputLargeColumns))
    (typed_pair (typed_pair
      (typed_composition (typed_composition typed_first typed_first) typed_second)
      (typed_composition typed_first typed_second)) typed_second)


lemma typed_prepareOutput : Typed prepareOutputRealizer 1008 :=
  typed_pair (typed_composition (typed_composition
    (typed_composition typed_first typed_first) typed_first) typed_second)
    typed_outputData


lemma typed_outerTrial : Typed outerTrialRealizer 16236962784 :=
  typed_composition typed_prepareOutput typed_acceptedTable


end
end Math115.UnitRuntimeNext
