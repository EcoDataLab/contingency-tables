/- Literal original profile-validator DAGs with numerical Typed annotations.
Lean verifies every bound; no work inequality is assumed. -/
import UnitRuntime.TerminalDegree
namespace Math115.UnitRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds ProfilePrograms
noncomputable section

lemma typed_boolOr : Typed boolOr 1 := by
  unfold boolOr
  apply typed_congr
  exact Math115.DrawDegree.typed_choose typed_first (typed_constant true) typed_second

lemma typed_indexIndicator  : Typed indexIndicator 1 :=
by
  unfold indexIndicator
  exact typed_congr _ (Math115.DrawDegree.typed_choose Math115.RetryRuntimeNext.typed_natEqual
    (typed_constant 1) (typed_constant 0))


lemma typed_defectAt  : Typed defectAtRealizer 2 :=
by
  unfold defectAtRealizer
  exact typed_composition (typed_pair
    (typed_composition (typed_pair
      (typed_composition (typed_pair
        (typed_composition typed_first typed_first) typed_second) typed_pairSum)
      (typed_composition (typed_pair typed_second
        (typed_composition (typed_composition typed_first typed_second) typed_first))
        typed_indexIndicator)) typed_add)
    (typed_composition (typed_pair
      (typed_composition (typed_composition typed_first typed_first) typed_second)
      (typed_composition (typed_pair typed_second
        (typed_composition (typed_composition typed_first typed_second) typed_second))
        typed_indexIndicator)) typed_add)) Math115.RetryRuntimeNext.typed_natEqual


lemma typed_defectTest  : Typed defectTestRealizer 504 :=
by
  unfold defectTestRealizer
  exact typed_congr _ (typed_composition (typed_pair
    (typed_composition (typed_composition typed_second Math115.RetryRuntimeNext.typed_natEqual) Math115.RetryRuntimeNext.typed_boolNot)
    (typed_composition (typed_composition
      (typed_pair typed_identity (typed_composition typed_first typed_patternIndices))
      (Math115.RetryRuntimeNext.typed_mapWith typed_defectAt (by decide))) Math115.ReferenceRuntimeNext.typed_all)) typed_boolAnd)


lemma typed_patternTest  : Typed patternTestRealizer 513114336 :=
by
  unfold patternTestRealizer
  exact typed_congr _ (typed_composition (typed_pair typed_balancedTest
    (typed_composition (typed_composition (typed_pair typed_identity
      (typed_composition (typed_pair
        (typed_composition typed_first typed_first)
        (typed_composition typed_first typed_first)) Math115.CatalogueDegreeV1.typed_cellPairs))
      (Math115.RetryRuntimeNext.typed_mapWith typed_defectTest (by decide))) Math115.ReferenceRuntimeNext.typed_any)) typed_boolOr)


lemma typed_boundedValues  : Typed boundedValuesRealizer 72 :=
  typed_congr _ (typed_composition
    (Math115.RetryRuntimeNext.typed_mapWith (typed_composition
      (typed_pair typed_second typed_first) Math115.RetryRuntimeNext.typed_leNat) (by decide)) Math115.ReferenceRuntimeNext.typed_all)


lemma typed_complementValues  : Typed complementValuesRealizer 6 :=
  Math115.RetryRuntimeNext.typed_mapWith Math115.RetryRuntimeNext.typed_subtract_seed (by decide)


end
end Math115.UnitRuntimeNext
