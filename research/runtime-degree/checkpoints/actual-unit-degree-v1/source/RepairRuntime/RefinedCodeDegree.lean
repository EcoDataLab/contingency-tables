import RepairRuntime.CodeOutput
namespace Math115.RepairRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open ProfilePrograms Math115.DegreeBounds Math115.PrinterRuntimeNext Math115.AffineMapWithNext
open Math115.UnitRuntimeNext
noncomputable section
lemma typed_repairedViews_refined : Typed repairedViewsRealizer 42 := by
  unfold repairedViewsRealizer
  exact typed_pair typed_repairRows (typed_comp_output
    (typed_pair (typed_composition typed_second typed_first) typed_repairRows) typed_listDifference
    (output_pair
      (output_of_typed (typed_composition (typed_second (A:=List ℕ) (B:=List ℕ×(ℕ×ℕ))) typed_first))
      output_repairRows))
lemma typed_backwardColumns_refined : Typed backwardColumnsRealizer 84 := by
  unfold backwardColumnsRealizer
  exact typed_comp_output (typed_pair typed_backwardRows (typed_pair
    (typed_composition (typed_composition typed_second typed_second) typed_first)
    (typed_composition (typed_composition (typed_composition typed_second typed_second) typed_second) typed_first)))
    typed_listExchange (output_pair output_backwardRows
      (output_of_typed (typed_pair
        (typed_composition (typed_composition (typed_second (A:=List ℕ) (B:=List ℕ×(ℕ×(ℕ×ℕ)))) typed_second) typed_first)
        (typed_composition (typed_composition (typed_composition typed_second typed_second) typed_second) typed_first))))
lemma typed_backwardViews_refined : Typed backwardViewsRealizer 84 := by
  unfold backwardViewsRealizer
  exact typed_pair typed_backwardRows (typed_comp_output
    (typed_pair (typed_composition typed_second typed_first) typed_backwardColumns_refined) typed_listDifference
    (output_pair
      (output_of_typed (typed_composition (typed_second (A:=List ℕ) (B:=List ℕ×(ℕ×(ℕ×ℕ)))) typed_first))
      output_backwardColumns))
lemma typed_forwardRepairCode_refined : Typed forwardRepairCodeRealizer 84 := by
  unfold forwardRepairCodeRealizer
  exact typed_comp_output (typed_pair typed_repairDataRows (typed_pair typed_repairDataCaps
    (typed_pair (typed_composition typed_second typed_second) typed_repairDataCross))) typed_repairedViews_refined
    (output_pair (output_of_typed typed_repairDataRows) (output_pair output_repairDataCaps
      (output_pair
        (output_of_typed (typed_composition (typed_second (A:=RepairData) (B:=ℕ×ℕ)) typed_second))
        output_repairDataCross)))
lemma typed_inverseRepairCode_refined : Typed inverseRepairCodeRealizer 168 := by
  unfold inverseRepairCodeRealizer
  exact typed_comp_output (typed_pair typed_repairDataRows (typed_pair typed_repairDataCaps
    (typed_pair (typed_composition typed_second typed_first) (typed_pair
      (typed_composition typed_second typed_second) typed_repairDataCross)))) typed_backwardViews_refined
    (output_pair (output_of_typed typed_repairDataRows) (output_pair output_repairDataCaps
      (output_pair
        (output_of_typed (typed_composition (typed_second (A:=RepairData) (B:=ℕ×ℕ)) typed_first))
        (output_pair
          (output_of_typed (typed_composition (typed_second (A:=RepairData) (B:=ℕ×ℕ)) typed_second))
          output_repairDataCross))))
end
end Math115.RepairRuntimeNext
