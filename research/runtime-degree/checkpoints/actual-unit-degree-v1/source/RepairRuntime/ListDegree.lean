import RepairRuntime.RefinedCodeDegree
import UnitRuntime.ProfilePatternDegree
namespace Math115.RepairRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open ProfilePrograms Math115.DegreeBounds Math115.PrinterRuntimeNext Math115.AffineMapWithNext
open Math115.UnitRuntimeNext
noncomputable section
lemma typed_repairLabelTest : Typed repairLabelTestRealizer 504 := by
  unfold repairLabelTestRealizer
  exact typed_composition (typed_pair (typed_pair
    (typed_composition (typed_composition typed_first typed_first) typed_second)
    (typed_composition typed_first typed_second)) typed_second) typed_defectTest
lemma typed_repairRowsData : Typed repairRows 1 := by
  unfold repairRows
  exact typed_composition (typed_composition typed_first typed_second) typed_first
lemma typed_repairPairs : Typed repairPairsRealizer 504 := by
  unfold repairPairsRealizer
  exact typed_composition (typed_pair typed_repairRowsData typed_repairRowsData)
    Math115.CatalogueDegreeV1.typed_cellPairs
lemma output_cellPairs : OutputBound cellPairs 3 := by
  refine ⟨8*X^3+4*X^2+1,?_,fun z => ?_⟩
  · have h3 : (8*X^3 : Polynomial ℕ).natDegree≤3 := by
      simpa using degree_scale 8 (show (X^3 : Polynomial ℕ).natDegree≤3 by simp)
    have h2 : (4*X^2 : Polynomial ℕ).natDegree≤2 := by
      simpa using degree_scale 4 (show (X^2 : Polynomial ℕ).natDegree≤2 by simp)
    exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le h3 (h2.trans (by decide))) (by simp)
  · simpa only [eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one] using
      Math115.CatalogueDegreeV1.weight_cellPairs_output z
lemma output_repairPairs : OutputBound repairPairs 3 :=
  output_composition (output_of_typed (typed_pair typed_repairRowsData typed_repairRowsData)) output_cellPairs
lemma output_forwardRepairLabels : OutputBound forwardRepairLabels 3 := by
  obtain ⟨p,hp,hpb⟩ := output_repairPairs
  exact ⟨p,hp,fun z => (weight_sublist List.filter_sublist).trans (hpb z)⟩
lemma typed_forwardRepairLabels : Typed forwardRepairLabelsRealizer 1515 := by
  unfold forwardRepairLabelsRealizer
  exact typed_comp_output (typed_pair typed_identity typed_repairPairs)
    (typed_filterWith_output typed_repairLabelTest (by decide))
    (output_pair (output_of_typed (typed_identity (A:=RepairData))) output_repairPairs)
/-- Exact eager forward-repair enumeration, including malformed catalogs,
unrelated views, arbitrary capacities and all out-of-range labels. -/
theorem typed_forwardRepairList : Typed forwardRepairListRealizer 2271 := by
  unfold forwardRepairListRealizer
  exact typed_comp_output (typed_pair typed_identity typed_forwardRepairLabels)
    (typed_mapWith_poly_output typed_forwardRepairCode_refined (by decide) output_forwardRepairCode)
    (output_pair (output_of_typed (typed_identity (A:=RepairData))) output_forwardRepairLabels)
end
end Math115.RepairRuntimeNext
