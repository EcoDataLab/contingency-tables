/- Literal original profile-validator DAGs with numerical Typed annotations.
Lean verifies every bound; no work inequality is assumed. -/
import UnitRuntime.ProfileMarginsDegree
namespace Math115.UnitRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds ProfilePrograms
noncomputable section


lemma typed_profileViews  : Typed profileViews 1 :=
  typed_composition (typed_composition typed_first typed_first) typed_second


lemma typed_profileCatalog  : Typed profileCatalog 1 :=
  typed_composition (typed_composition typed_first typed_first) typed_first


lemma typed_profileMargins  : Typed profileMargins 1 :=
  typed_composition typed_first typed_second


lemma typed_profileView s : Typed profileViews 1 :=
  typed_composition (typed_composition typed_first typed_first) typed_second


lemma typed_profileBound (row : Bool) : Typed (profileBound row) 72 :=
  typed_composition (typed_pair typed_second (typed_profileView row))
    typed_boundedValues


lemma typed_profileShape (row : Bool) : Typed (profileShape row) 2 :=
  typed_composition (typed_pair
    (typed_composition (typed_profileView row) Math115.RetryRuntimeNext.typed_listLength_seed)
    (typed_composition typed_profileCatalog Math115.RetryRuntimeNext.typed_listLength_seed)) Math115.RetryRuntimeNext.typed_natEqual


lemma typed_profilePattern  : Typed profilePattern 513114336 :=
  typed_composition (typed_pair typed_profileViews typed_second)
    typed_patternTest


lemma typed_profileColumnView  : Typed profileColumnView 6 :=
  typed_composition (typed_pair typed_second
    (typed_composition typed_profileViews typed_second)) typed_complementValues


lemma typed_profileLineData (row : Bool) : Typed (profileLineData row) 6 :=
  typed_pair (typed_pair (typed_pair typed_profileCatalog
    (Math115.DrawDegree.typed_choose (typed_constant row) (typed_profileView true)
      typed_profileColumnView)) typed_profileMargins) typed_second


lemma typed_profileLineTest (row : Bool) : Typed (profileLineTest row) 746457552 :=
  typed_composition (typed_profileLineData row) (typed_validMargins row)


lemma typed_profileTest  : Typed profileTestRealizer 746457552 :=
  typed_composition (typed_pair (typed_profileShape true)
    (typed_composition (typed_pair (typed_profileShape false)
    (typed_composition (typed_pair (typed_profileBound true)
    (typed_composition (typed_pair (typed_profileBound false)
    (typed_composition (typed_pair typed_profilePattern
    (typed_composition (typed_pair (typed_profileLineTest true)
      (typed_profileLineTest false)) typed_boolAnd)) typed_boolAnd))
      typed_boolAnd)) typed_boolAnd)) typed_boolAnd)) typed_boolAnd


end
end Math115.UnitRuntimeNext
