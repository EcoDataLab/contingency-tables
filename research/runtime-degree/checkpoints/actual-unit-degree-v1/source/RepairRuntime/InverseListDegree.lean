import RepairRuntime.ListDegree
import UnitRuntime.ProfileEqualityDegree
import OAI.Combinatorics.ContingencyTables.Sampling.SmallInverseRepairList
namespace Math115.RepairRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open ProfilePrograms Math115.DegreeBounds Math115.PrinterRuntimeNext Math115.AffineMapWithNext
open Math115.UnitRuntimeNext
noncomputable section
lemma typed_inverseLabelInput : Typed inverseLabelInputRealizer 168 := by
  unfold inverseLabelInputRealizer
  exact typed_pair (typed_pair (typed_pair typed_repairDataCatalog typed_inverseRepairCode_refined)
    (typed_composition typed_first typed_second)) typed_second
lemma output_inverseLabelInput : OutputBound inverseLabelInput 16 := by
  exact output_pair (output_pair (output_pair (output_of_typed typed_repairDataCatalog) output_inverseRepairCode)
    (output_of_typed (typed_composition (typed_first (A:=RepairData) (B:=ℕ×ℕ)) typed_second)))
    (output_of_typed (typed_second (A:=RepairData) (B:=ℕ×ℕ)))
lemma typed_inverseLabelTest : Typed inverseLabelTestRealizer 64512 := by
  unfold inverseLabelTestRealizer
  exact typed_composition (typed_pair
    (typed_comp_output typed_inverseLabelInput typed_repairLabelTest output_inverseLabelInput)
    (typed_comp_output
      (typed_pair (typed_comp_output typed_inverseLabelInput typed_forwardRepairCode_refined output_inverseLabelInput)
        (typed_composition (typed_composition typed_first typed_first) typed_second)) typed_profileCodeEqual
      (output_pair (output_composition output_inverseLabelInput output_forwardRepairCode)
        (output_of_typed (typed_composition (typed_composition (typed_first (A:=RepairData) (B:=ℕ×ℕ)) typed_first) typed_second)))))
    typed_boolAnd
lemma output_inverseRepairLabels : OutputBound inverseRepairLabels 3 := by
  obtain ⟨p,hp,hpb⟩ := output_repairPairs
  exact ⟨p,hp,fun z => (weight_sublist List.filter_sublist).trans (hpb z)⟩
lemma typed_inverseRepairLabels : Typed inverseRepairLabelsRealizer 193539 := by
  unfold inverseRepairLabelsRealizer
  exact typed_comp_output (typed_pair typed_identity typed_repairPairs)
    (typed_filterWith_output typed_inverseLabelTest (by decide))
    (output_pair (output_of_typed (typed_identity (A:=RepairData))) output_repairPairs)
/-- Exact inverse candidate generation, forward-image check, eager filtering
and output construction, with arbitrary literal repair data. -/
theorem typed_checkedInverseRepairList : Typed checkedInverseRepairListRealizer 193539 := by
  unfold checkedInverseRepairListRealizer
  exact typed_comp_output (typed_pair typed_identity typed_inverseRepairLabels)
    (typed_mapWith_poly_output typed_inverseRepairCode_refined (by decide) output_inverseRepairCode)
    (output_pair (output_of_typed (typed_identity (A:=RepairData))) output_inverseRepairLabels)
end
end Math115.RepairRuntimeNext
