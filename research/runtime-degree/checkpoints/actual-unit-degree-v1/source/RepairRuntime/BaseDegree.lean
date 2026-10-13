import RepairRuntime.OutputHelpers
import UnitRuntime.TerminalIndexDegree
import OAI.Combinatorics.ContingencyTables.Sampling.SmallRepairListProgram
namespace Math115.RepairRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open ProfilePrograms Math115.DegreeBounds Math115.PrinterRuntimeNext Math115.AffineMapWithNext
open Math115.UnitRuntimeNext
noncomputable section
lemma typed_sourceCell : Typed sourceCell 2 := by
  unfold sourceCell
  exact typed_composition (typed_pair typed_first (typed_composition typed_second typed_first))
    (Math115.RetryRuntimeNext.typed_getDFast (0,0))
lemma typed_targetCell : Typed targetCell 2 := by
  unfold targetCell
  exact typed_composition (typed_pair typed_first (typed_composition typed_second typed_second))
    (Math115.RetryRuntimeNext.typed_getDFast (0,0))
lemma typed_crossingIndex : Typed crossingIndexRealizer 8 := by
  unfold crossingIndexRealizer
  exact typed_composition (typed_pair (typed_pair
    (typed_composition typed_targetCell typed_first) (typed_composition typed_sourceCell typed_second)) typed_first)
    typed_cellLookup
lemma typed_capacityList : Typed capacityListRealizer 4 := by
  unfold capacityListRealizer
  exact typed_mapWith_affine typed_first (by decide)
    ⟨1,0,fun z => by simpa only [one_mul,add_zero] using weight_fst z⟩
lemma capacityList_output : OutputBound capacityList 2 := by
  exact mapWith_affine_output (f:=fun z : ℕ×ℕ => z.1) ⟨1,0,fun z => by simpa only [one_mul,add_zero] using weight_fst z⟩
lemma typed_differenceEntry : Typed differenceEntryRealizer 2 := by
  unfold differenceEntryRealizer
  exact typed_composition (typed_pair
    (typed_composition (typed_pair (typed_composition typed_first typed_first) typed_second)
      (Math115.RetryRuntimeNext.typed_getDFast 0))
    (typed_composition (typed_pair (typed_composition typed_first typed_second) typed_second)
      (Math115.RetryRuntimeNext.typed_getDFast 0))) Math115.RetryRuntimeNext.typed_subtract_seed
lemma getD_zero_weight (xs : List ℕ) (i : ℕ) : weight (xs.getD i 0) ≤ weight xs+1 := by
  by_cases hi : i<xs.length
  · rw [List.getD_eq_getElem xs 0 hi]
    have hm : xs[i]∈xs := List.mem_iff_getElem.mpr ⟨i,hi,rfl⟩
    exact (weight_mem hm).trans (by omega)
  · rw [List.getD_eq_default xs 0 (by omega)]
    have hz : weight (0:ℕ)=1 := by simp [weight_nat]
    omega
lemma differenceEntry_affine : AffineOutput differenceEntry := by
  refine ⟨4,5,fun z => ?_⟩
  have hsub := weight_nat_small (Nat.sub_le (z.1.1.getD z.2 0) (z.1.2.getD z.2 0))
  have hget := getD_zero_weight z.1.1 z.2
  have hlist := (weight_fst z.1).trans (weight_fst z)
  change weight (z.1.1.getD z.2 0-z.1.2.getD z.2 0) ≤ _
  omega
lemma typed_listDifference : Typed listDifferenceRealizer 15 := by
  have hr : Typed (composition (composition (second (A:=List ℕ) (B:=List ℕ)) listLength) range) 3 := by
    apply Math115.RetryRuntimeNext.typed_boundedRange (d:=1)
      (typed_composition typed_second Math115.RetryRuntimeNext.typed_listLength_seed) X (by simp)
    intro z
    simp only [Function.comp_apply,eval_X]
    exact (list_length_le_weight z.2).trans (weight_snd z)
  unfold listDifferenceRealizer
  exact typed_composition (typed_pair typed_identity hr)
    (typed_mapWith_affine typed_differenceEntry (by decide) differenceEntry_affine)
lemma typed_repairRows : Typed repairRowsRealizer 42 := by
  unfold repairRowsRealizer
  exact typed_composition (typed_pair typed_first (typed_pair
    (typed_composition (typed_composition typed_second typed_second) typed_second)
    (typed_composition (typed_composition typed_second typed_second) typed_first))) typed_listExchange
lemma typed_repairedViews : Typed repairedViewsRealizer 630 := by
  unfold repairedViewsRealizer
  exact typed_pair typed_repairRows (typed_composition
    (typed_pair (typed_composition typed_second typed_first) typed_repairRows) typed_listDifference)
lemma typed_backwardRows : Typed backwardRowsRealizer 42 := by
  unfold backwardRowsRealizer
  exact typed_composition (typed_pair typed_first
    (typed_composition (typed_composition typed_second typed_second) typed_second)) typed_listExchange
lemma typed_backwardColumns : Typed backwardColumnsRealizer 1764 := by
  unfold backwardColumnsRealizer
  exact typed_composition (typed_pair typed_backwardRows (typed_pair
    (typed_composition (typed_composition typed_second typed_second) typed_first)
    (typed_composition (typed_composition (typed_composition typed_second typed_second) typed_second) typed_first))) typed_listExchange
lemma typed_backwardViews : Typed backwardViewsRealizer 26460 := by
  unfold backwardViewsRealizer
  exact typed_pair typed_backwardRows (typed_composition
    (typed_pair (typed_composition typed_second typed_first) typed_backwardColumns) typed_listDifference)
lemma typed_repairDataCatalog : Typed repairDataCatalog 1 := by
  unfold repairDataCatalog
  exact typed_composition (typed_composition typed_first typed_first) typed_first
lemma typed_repairDataRows : Typed repairDataRows 1 := by
  unfold repairDataRows
  exact typed_composition (typed_composition (typed_composition typed_first typed_first) typed_second) typed_first
lemma typed_repairDataCaps : Typed repairDataCaps 4 := by
  unfold repairDataCaps
  exact typed_composition (typed_pair (typed_composition typed_first typed_second) typed_repairDataRows) typed_capacityList
lemma typed_repairDataCross : Typed repairDataCross 8 := by
  unfold repairDataCross
  exact typed_composition (typed_pair typed_repairDataCatalog typed_second) typed_crossingIndex
/-- Exact forward repair on arbitrary literal catalog, views, capacity and labels. -/
lemma typed_forwardRepairCode : Typed forwardRepairCodeRealizer 5040 := by
  unfold forwardRepairCodeRealizer
  exact typed_composition (typed_pair typed_repairDataRows (typed_pair typed_repairDataCaps
    (typed_pair (typed_composition typed_second typed_second) typed_repairDataCross))) typed_repairedViews
lemma typed_inverseRepairCode : Typed inverseRepairCodeRealizer 211680 := by
  unfold inverseRepairCodeRealizer
  exact typed_composition (typed_pair typed_repairDataRows (typed_pair typed_repairDataCaps
    (typed_pair (typed_composition typed_second typed_first) (typed_pair
      (typed_composition typed_second typed_second) typed_repairDataCross)))) typed_backwardViews
end
end Math115.RepairRuntimeNext
