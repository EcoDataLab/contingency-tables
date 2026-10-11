/- Numerical certificates for exact pinned unit-neighbor helpers.
All literal inputs, realizer costs and encoded output weights are charged. -/
import UnitRuntime.WordChoiceDegree
import UnitRuntime.ExchangeDegree
import ResearchBounds.SmallCellCatalogueDegree
import OAI.Combinatorics.ContingencyTables.Sampling.SmallExchangeListProgram

namespace Math115.UnitRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open ProfilePrograms Math115.DegreeBounds
open Math115.RetryRuntimeNext Math115.PrinterRuntimeNext
noncomputable section

lemma typed_flattenViews : Typed flattenViewsRealizer 2 := Math115.PrinterRuntimeNext.typed_append

lemma typed_splitViews : Typed splitViewsRealizer 8 := by
  unfold splitViewsRealizer
  exact typed_pair
    (typed_composition (typed_pair typed_second typed_first) Math115.RetryRuntimeNext.typed_takeFast)
    (typed_composition (typed_pair typed_second typed_first) Math115.RetryRuntimeNext.typed_dropFast)

lemma typed_codeExchange : Typed codeExchangeRealizer 672 := by
  unfold codeExchangeRealizer
  exact typed_composition
    (typed_pair
      (typed_composition (typed_composition typed_first typed_first) Math115.RetryRuntimeNext.typed_listLength_seed)
      (typed_composition (typed_pair (typed_composition typed_first typed_flattenViews) typed_second)
        typed_listExchange)) typed_splitViews

lemma typed_boolAnd : Typed boolAnd 1 := by
  unfold boolAnd
  apply typed_congr
  exact Math115.DrawDegree.typed_choose typed_first typed_second (typed_constant false)

lemma typed_positiveExchangeTest : Typed positiveExchangeTestRealizer 2 := by
  unfold positiveExchangeTestRealizer
  apply typed_congr
  exact typed_composition
    (typed_pair
      (typed_composition (typed_composition typed_second Math115.RetryRuntimeNext.typed_natEqual)
        Math115.RetryRuntimeNext.typed_boolNot)
      (typed_composition (typed_pair (typed_constant 0)
        (typed_composition (typed_pair typed_first (typed_composition typed_second typed_second))
          (Math115.RetryRuntimeNext.typed_getDFast 0))) Math115.RetryRuntimeNext.typed_less))
    typed_boolAnd

lemma typed_positiveExchangeIndices : Typed positiveExchangeIndicesRealizer 169344 := by
  unfold positiveExchangeIndicesRealizer
  exact typed_composition
    (typed_pair typed_identity
      (typed_composition (typed_pair typed_identity typed_identity) Math115.CatalogueDegreeV1.typed_cellPairs))
    (Math115.DrawDegree.typed_filterWith typed_positiveExchangeTest (by decide))

/-- Actual exchange-neighbor enumeration on arbitrary unequal or malformed views.
The nested mapping builds all listed output profiles and charges their accumulator. -/
theorem typed_codeExchangeList : Typed codeExchangeListRealizer 306348037632 := by
  unfold codeExchangeListRealizer
  exact typed_composition
    (typed_pair typed_identity (typed_composition typed_flattenViews typed_positiveExchangeIndices))
    (Math115.RetryRuntimeNext.typed_mapWith typed_codeExchange (by decide))

end
end Math115.UnitRuntimeNext
