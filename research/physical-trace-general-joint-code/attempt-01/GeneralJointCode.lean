/-
SPDX-License-Identifier: Apache-2.0
Reconstruct the full retained source row view from the catalog-ordered state
code and the actual residual completion matrix. Output padding is deliberately
zero during source reconstruction; terminal repair/unpadding happens later.
Ordered defect labels remain explicit inputs in this first joint-code seam.
-/
import ResearchPhysicalTraceJoin.GeneralCorrectionCode
import Math115.LatticeSamplerPreparation

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open SmallContextFibres PaddedCompletions FirstSuccess ResidualMixture
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalComputedProposal Math115.LegacyPhysicalCompletion
open Math115.LatticeSamplerPreparation
open scoped BigOperators

/-- Existing reconstruction data, but without subtracting any dense padding.
The residual matrix is retained exactly, including entries below L. -/
def jointSourceData (rs cs : List ℕ) (U : ℕ) (state : List ℕ × List ℕ)
    (residual : MatrixCode) : OuterTableData :=
  (((smallCellCatalog ((rs,cs),U),state), (largeIndices (U,rs),largeIndices (U,cs))),
    ((U,0),residual))

def jointSourceMatrixCode (rs cs : List ℕ) (U : ℕ) (state : List ℕ × List ℕ)
    (residual : MatrixCode) : MatrixCode :=
  outputMatrix ((rs,cs),jointSourceData rs cs U state residual)

/-- A computational corrected terminal operation with source reconstruction.
The raw ordered defect labels are still supplied separately. -/
def jointTerminalCorrectionCode (rs cs : List ℕ) (U L k : ℕ)
    (state : List ℕ × List ℕ) (residual : MatrixCode) (s t : ℕ × ℕ)
    (bits : List Bool) : Option MatrixCode :=
  terminalCorrectionCode rs cs U L k (jointSourceMatrixCode rs cs U state residual) s t bits

noncomputable section
open scoped Classical
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)
local notation "small" => firstPaperSmall r c U
local notation "B" => capacity r c U L
local notation "e" => computedCellEquiv r c U

/-- The actual residual block in the existing computed large-line order. -/
def jointResidualMatrixCode (a : DefectJoint r c U L) : MatrixCode :=
  tableOutput (listedTable r c U L hr hc a.1.val a.2)

lemma jointSourceData_code (a : DefectJoint r c U L) :
    jointSourceData (List.ofFn r) (List.ofFn c) U (computedStateCode r c U L a.1.val)
      (jointResidualMatrixCode r c U L hr hc a) =
      (((cellCatalog small e,computedStateCode r c U L a.1.val),
        (largeIndices (U,List.ofFn r),largeIndices (U,List.ofFn c))),
        ((U,0),tableOutput (listedTable r c U L hr hc a.1.val a.2))) := by
  simp only [jointSourceData, jointResidualMatrixCode, computedCellEquiv_catalog, computedCatalog]

lemma jointSourceEntry_small (a : DefectJoint r c U L) (i : Fin m) (j : Fin n)
    (hs : small i j = true) :
    outputEntry (jointSourceData (List.ofFn r) (List.ofFn c) U
      (computedStateCode r c U L a.1.val) (jointResidualMatrixCode r c U L hr hc a),
        (i.val,j.val)) = a.2.val.val.1 i j := by
  rw [jointSourceData_code]
  have he := outputEntry_small small e (physicalProfile small B r c L a.1.val)
    (largeIndices (U,List.ofFn r)) (largeIndices (U,List.ofFn c)) U 0
    (tableOutput (listedTable r c U L hr hc a.1.val a.2)) i j hs
  exact he.trans (by
    simpa only [smallView, hs, dite_eq_left] using (a.2.property.2.2.1 i j hs).1.symm)

lemma jointSourceEntry_large (a : DefectJoint r c U L)
    (i : Option (Fin (tailCount r U))) (j : Option (Fin (tailCount c U))) :
    outputEntry (jointSourceData (List.ofFn r) (List.ofFn c) U
      (computedStateCode r c U L a.1.val) (jointResidualMatrixCode r c U L hr hc a),
        ((largeOptionEquiv r U hr i).val.val,(largeOptionEquiv c U hc j).val.val)) =
      a.2.val.val.1 (largeOptionEquiv r U hr i).val (largeOptionEquiv c U hc j).val := by
  rw [jointSourceData_code]
  have hs : small (largeOptionEquiv r U hr i).val (largeOptionEquiv c U hc j).val = false :=
    (firstPaperSmall_false_iff r c U _ _).mpr
      ⟨(largeOptionEquiv r U hr i).property,(largeOptionEquiv c U hc j).property⟩
  have hnot := (mem_cellCatalog small e
    ((largeOptionEquiv r U hr i).val,(largeOptionEquiv c U hc j).val)).not.mpr
      (by simp only [hs, Bool.false_eq_true, not_false_eq_true])
  have hpos := List.idxOf_eq_length hnot
  have hbad : ¬ (cellCatalog small e).idxOf
      ((largeOptionEquiv r U hr i).val.val,(largeOptionEquiv c U hc j).val.val) <
        (cellCatalog small e).length := by
    rw [hpos]
    exact Nat.lt_irrefl _
  rw [outputEntry, if_neg hbad]
  change matrixEntry (tableOutput (listedTable r c U L hr hc a.1.val a.2),
    ((largeIndices (U,List.ofFn r)).idxOf (largeOptionEquiv r U hr i).val.val,
      (largeIndices (U,List.ofFn c)).idxOf (largeOptionEquiv c U hc j).val.val)) - 0 = _
  rw [largeOption_index, largeOption_index, tableOutput_entry, listedTable_entry, Nat.sub_zero]

/-- Exact full source-view reconstruction, before repair or unpadding. -/
theorem jointSourceMatrixCode_eq (a : DefectJoint r c U L) :
    jointSourceMatrixCode (List.ofFn r) (List.ofFn c) U
      (computedStateCode r c U L a.1.val) (jointResidualMatrixCode r c U L hr hc a) =
      terminalSourceMatrixCode r c U L a := by
  unfold jointSourceMatrixCode terminalSourceMatrixCode
  rw [outputMatrix_code]
  apply congrArg matrixCode
  funext i j
  cases hs : small i j with
  | true => exact jointSourceEntry_small r c U L hr hc a i j hs
  | false =>
    obtain ⟨hi,hj⟩ := (firstPaperSmall_false_iff r c U i j).mp hs
    obtain ⟨ii,hii⟩ := (largeOptionEquiv r U hr).surjective ⟨i,hi⟩
    obtain ⟨jj,hjj⟩ := (largeOptionEquiv c U hc).surjective ⟨j,hj⟩
    simpa only [hii,hjj] using jointSourceEntry_large r c U L hr hc a ii jj

/-- The residual encoder is the same finSucc-ordered matrix code that the
frozen completion adapter already identifies with the executable old draw. -/
lemma jointResidualMatrixCode_eq (a : DefectJoint r c U L) :
    jointResidualMatrixCode r c U L hr hc a =
      matrixCode (finiteFibreEquiv r c U L hr hc a.1.val a.2).val := by
  rfl

/-- The source reconstruction accepts the actual executable residual draw
code, without a chosen full-matrix input. -/
theorem jointSourceMatrixCode_draw (d : DefectVertices r c U L) (h : ℕ)
    (word : Fin (bits r c U L hr hc d.val h) → Bool) :
    jointSourceMatrixCode (List.ofFn r) (List.ofFn c) U
      (computedStateCode r c U L d.val)
      (Math115.LatticeSampler.draw
        (((List.ofFn (coarseRows r c U L hr d.val),List.ofFn (coarseColumns r c U L hc d.val)),h),
          List.ofFn word)) =
      terminalSourceMatrixCode r c U L ⟨d,completionDraw r c U L hr hc d.val h word⟩ := by
  rw [completionDraw_code]
  rw [← jointResidualMatrixCode_eq r c U L hr hc ⟨d,completionDraw r c U L hr hc d.val h word⟩]
  exact jointSourceMatrixCode_eq r c U L hr hc _

/-- The old explicit full-source input is removed. Ordered labels remain
supplied by their semantic encoder; this is not yet label extraction. -/
theorem jointTerminalCorrectionCode_eq (a : DefectJoint r c U L) (k : ℕ) (word : Fin k → Bool) :
    jointTerminalCorrectionCode (List.ofFn r) (List.ofFn c) U L k
      (computedStateCode r c U L a.1.val) (jointResidualMatrixCode r c U L hr hc a)
      (terminalOrderedLabelCode r c U L a).1 (terminalOrderedLabelCode r c U L a).2
      (List.ofFn word) =
      (terminalBitCorrection r c U L k a word).map (fun X => matrixCode X.val) := by
  unfold jointTerminalCorrectionCode
  rw [jointSourceMatrixCode_eq]
  exact terminalCorrectionCode_eq r c U L a k word

end
end Math115.PhysicalTraceJoin
