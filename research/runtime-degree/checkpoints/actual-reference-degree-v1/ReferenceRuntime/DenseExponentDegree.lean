import ReferenceRuntime.DenseTrialWidthDegree
import InputNormalization.MaximalIndex

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds DensePrograms ProfilePrograms
set_option maxHeartbeats 1200000
noncomputable section

lemma typed_denseComponent : Typed componentRealizer 31104 := by
  have hD : Typed (composition (first (A:=ℕ×ℕ) (B:=ℕ×ℕ)) first) 1 := typed_composition typed_first typed_first
  have hS : Typed (composition (first (A:=ℕ×ℕ) (B:=ℕ×ℕ)) second) 1 := typed_composition typed_first typed_second
  have hP : Typed (composition (second (A:=ℕ×ℕ) (B:=ℕ×ℕ)) first) 1 := typed_composition typed_second typed_first
  have hN : Typed (composition (second (A:=ℕ×ℕ) (B:=ℕ×ℕ)) second) 1 := typed_composition typed_second typed_second
  have h4 := typed_composition hD typed_completionFourthPower
  have h8 := typed_composition hD typed_denseEighthPower
  have hp := typed_composition
    (typed_pair h4
      (typed_composition
        (typed_pair (typed_composition (typed_pair h8 hP) typed_multiply)
          (typed_composition (typed_pair hD hS) typed_multiply)) typed_add)) typed_multiply
  have hn := typed_composition (typed_pair (typed_composition (typed_pair h4 h8) typed_multiply) hN) typed_multiply
  have hd := typed_composition (typed_pair hS h8) typed_multiply
  unfold componentRealizer
  exact typed_congr _ (typed_composition
    (typed_pair (typed_composition (typed_pair hn hp) Math115.DivisionRuntimeNext.typed_subtract_actual) hd)
    Math115.DivisionRuntimeNext.typed_quotient)

lemma typed_exponentCell : Typed exponentCellRealizer 2426112 := by
  unfold exponentCellRealizer
  exact typed_composition typed_exponentCellData typed_denseComponent

lemma typed_exponentCells : Typed exponentCellsRealizer 504 := by
  unfold exponentCellsRealizer
  exact typed_composition (typed_composition typed_first typed_first) Math115.CatalogueDegreeV1.typed_cellPairs

lemma typed_exponentValues : Typed exponentValuesRealizer 5933110037558256 := by
  unfold exponentValuesRealizer
  exact typed_composition (typed_pair typed_identity typed_exponentCells)
    (Math115.DrawDegree.typed_mapWith typed_exponentCell (by decide))

lemma typed_fullExponent : Typed fullExponentRealizer 11866220075116512 := by
  unfold fullExponentRealizer
  exact typed_composition (typed_pair typed_exponentValues (typed_constant 0)) Math115.InputNormalization.typed_listMaximum

lemma typed_gridCellValue : Typed gridCellValueRealizer 5184 := by
  unfold gridCellValueRealizer
  exact typed_composition
    (typed_pair typed_gridCellWidth
      (typed_composition
        (typed_pair (typed_composition (typed_composition typed_first typed_first) typed_second) typed_second)
        typed_denseMatrixEntry)) typed_multiply

lemma typed_scaleRows : Typed scaleRowsRealizer 3 := by
  unfold scaleRowsRealizer
  apply Math115.DrawRuntimeNext.typed_boundedRange (e:=2) (d:=1)
    (typed_composition
      (typed_composition (typed_composition (typed_composition typed_first typed_first) typed_first)
        Math115.ListRepeatDegreeV1.typed_tail) Math115.WordCountSeedDegrees.typed_listLength_seed) X (by simp)
  intro z
  have h := list_length_le_weight z.1.1.1
  simp only [Function.comp_apply,eval_X,List.length_tail]
  exact (Nat.sub_le _ _).trans (h.trans ((weight_fst z.1.1).trans
    ((weight_fst z.1).trans (weight_fst z))))

lemma typed_scaleColumns : Typed scaleColumnsRealizer 3 := by
  unfold scaleColumnsRealizer
  apply Math115.DrawRuntimeNext.typed_boundedRange (e:=2) (d:=1)
    (typed_composition
      (typed_composition (typed_composition (typed_composition typed_first typed_first) typed_second)
        Math115.ListRepeatDegreeV1.typed_tail) Math115.WordCountSeedDegrees.typed_listLength_seed) X (by simp)
  intro z
  have h := list_length_le_weight z.1.1.2
  simp only [Function.comp_apply,eval_X,List.length_tail]
  exact (Nat.sub_le _ _).trans (h.trans ((weight_snd z.1.1).trans
    ((weight_fst z.1).trans (weight_fst z))))

lemma typed_scaleRowEntry : Typed scaleRowEntryRealizer 5184 := by
  unfold scaleRowEntryRealizer
  exact typed_composition
    (typed_pair (typed_composition typed_first typed_first)
      (typed_pair (typed_composition typed_first typed_second) typed_second)) typed_gridCellValue

lemma typed_scaleRow : Typed scaleRowRealizer 161274246 := by
  unfold scaleRowRealizer
  exact typed_composition (typed_pair typed_identity (typed_composition typed_first typed_scaleColumns))
    (Math115.DrawDegree.typed_mapWith typed_scaleRowEntry (by decide))

lemma typed_scaleMatrix : Typed scaleMatrixRealizer 156056295504856578 := by
  unfold scaleMatrixRealizer
  exact typed_composition (typed_pair typed_identity typed_scaleRows)
    (Math115.DrawDegree.typed_mapWith typed_scaleRow (by decide))

lemma typed_scaledData : Typed scaledDataRealizer 156056295504856578 := by
  unfold scaledDataRealizer
  exact typed_pair (typed_pair (typed_composition typed_first typed_first) typed_scaleMatrix) typed_second

lemma typed_gridExponent : Typed gridExponentRealizer 1851798346568043816961265199615936 := by
  unfold gridExponentRealizer
  exact typed_composition typed_scaledData typed_fullExponent

/-- Actual flat-to-grid conversion, corner scaling, all exponent components,
and the full maximum fold, including their encoded output on invalid inputs. -/
theorem typed_flatExponent : Typed flatExponentRealizer 411732547972631998350801627013006442112 := by
  unfold flatExponentRealizer
  exact typed_composition typed_flatToGridData typed_gridExponent

#check typed_denseComponent
#print axioms typed_denseComponent
#check typed_flatExponent
#print axioms typed_flatExponent
end
end Math115.ReferenceRuntimeNext
