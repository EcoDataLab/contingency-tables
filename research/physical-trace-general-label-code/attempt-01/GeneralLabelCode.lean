/-
SPDX-License-Identifier: Apache-2.0
Ordinary ordered defect-label extraction from the two catalog-ordered state
view lists, followed by the exact retained-source reconstruction/correction.
The runtime path uses the existing repairLabelTest and a first-match list
search; it never decodes a semantic state or chooses abstract labels.
-/
import ResearchPhysicalTraceJoin.GeneralJointCode

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open SmallContextFibres PaddedCompletions FirstSuccess ResidualMixture
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalComputedProposal
open scoped BigOperators

/-- All ordered catalog-index pairs, in the original catalog order. -/
def orderedLabelIndexPairs (q : ℕ) : List (ℕ × ℕ) :=
  (List.range q).product (List.range q)

/-- The test uses both stored profile lists, including the original
capacity-complement second view. It is the existing executable test. -/
def orderedDefectLabelIndices (rs cs : List ℕ) (U : ℕ) (state : List ℕ × List ℕ) :
    Option (ℕ × ℕ) :=
  let catalog := smallCellCatalog ((rs,cs),U)
  (orderedLabelIndexPairs catalog.length).find? (fun st => repairLabelTest (((catalog,state),U),st))

/-- Return literal row/column positions, preserving the s/t order of the
unique defect. Raw state data with no matching pair yields none. -/
def orderedDefectLabelCode (rs cs : List ℕ) (U : ℕ) (state : List ℕ × List ℕ) :
    Option ((ℕ × ℕ) × (ℕ × ℕ)) :=
  let catalog := smallCellCatalog ((rs,cs),U)
  (orderedDefectLabelIndices rs cs U state).map (fun st =>
    (catalog.getD st.1 (0,0),catalog.getD st.2 (0,0)))

/-- No full matrix or labels are supplied: the raw state views and residual
matrix determine reconstruction, ordered-label extraction and correction. -/
def jointAutoCorrectionCode (rs cs : List ℕ) (U L k : ℕ)
    (state : List ℕ × List ℕ) (residual : MatrixCode) (bits : List Bool) : Option MatrixCode :=
  match orderedDefectLabelCode rs cs U state with
  | none => none
  | some st => jointTerminalCorrectionCode rs cs U L k state residual st.1 st.2 bits

noncomputable section
open scoped Classical

private lemma find_eq_some_of_unique {A : Type*} (xs : List A) (p : A → Bool) (a : A)
    (ha : a ∈ xs) (hp : p a = true) (hu : ∀ x ∈ xs, p x = true → x = a) :
    xs.find? p = some a := by
  have hs : (xs.find? p).isSome := List.find?_isSome.mpr ⟨a,ha,hp⟩
  have hr := Option.eq_some_of_isSome hs
  have he : (xs.find? p).get hs = a :=
    hu _ (List.get_find?_mem hs) (List.find?_some hr)
  rw [he] at hr
  exact hr

lemma mem_orderedLabelIndexPairs (q s t : ℕ) :
    (s,t) ∈ orderedLabelIndexPairs q ↔ s < q ∧ t < q := by
  simp only [orderedLabelIndexPairs, List.mem_product, List.mem_range]

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
local notation "small" => firstPaperSmall r c U
local notation "B" => capacity r c U L
local notation "e" => Math115.PhysicalComputedProposal.computedCellEquiv r c U

lemma orderedDefectTest_actual (d : DefectVertices r c U L) (s t : Cells small) :
    repairLabelTest (((smallCellCatalog ((List.ofFn r,List.ofFn c),U),
      computedStateCode r c U L d.val),U),((e.symm s).val,(e.symm t).val)) = true ↔
      IsDefect (smallView small (physicalProfile small B r c L d.val) false)
        (smallQ small B (physicalProfile small B r c L d.val)) s.val t.val := by
  have hcat : smallCellCatalog ((List.ofFn r,List.ofFn c),U) = cellCatalog small e :=
    (Math115.PhysicalComputedProposal.computedCellEquiv_catalog r c U).symm
  have he := congrArg (fun K : List (ℕ × ℕ) =>
    repairLabelTest (((K,computedStateCode r c U L d.val),U),((e.symm s).val,(e.symm t).val))) hcat
  rw [he]
  exact SmallGraphProfiles.repairLabelTest_iff small e B U
    (fun a => capacity_small r c U L _ _ a.property)
    (physicalProfile small B r c L d.val)
    (fun a => (physicalProfile_feasible r c U L d.val).bounded (a,true)) s t

/-- Every passing ordered pair is the actual uniquely ordered defect pair.
This includes distinct labels in a shared row or a shared column. -/
theorem orderedDefectLabelIndices_eq (d : DefectVertices r c U L) :
    orderedDefectLabelIndices (List.ofFn r) (List.ofFn c) U (computedStateCode r c U L d.val) =
      some ((e.symm (terminalRepairLabels r c U L d).1).val,
        (e.symm (terminalRepairLabels r c U L d).2).val) := by
  unfold orderedDefectLabelIndices
  apply find_eq_some_of_unique
  · exact (mem_orderedLabelIndexPairs _ _ _).mpr
      ⟨(e.symm (terminalRepairLabels r c U L d).1).isLt,
        (e.symm (terminalRepairLabels r c U L d).2).isLt⟩
  · exact (orderedDefectTest_actual r c U L d _ _).mpr (terminalRepairLabels_spec r c U L d)
  · intro st hmem hp
    have hb := (mem_orderedLabelIndexPairs _ _ _).mp hmem
    let s : Fin (smallCellCatalog ((List.ofFn r,List.ofFn c),U)).length := ⟨st.1,hb.1⟩
    let t : Fin (smallCellCatalog ((List.ofFn r,List.ofFn c),U)).length := ⟨st.2,hb.2⟩
    have hd : IsDefect (smallView small (physicalProfile small B r c L d.val) false)
        (smallQ small B (physicalProfile small B r c L d.val)) (e s).val (e t).val :=
      (orderedDefectTest_actual r c U L d (e s) (e t)).mp (by
        simpa only [Equiv.symm_apply_apply] using hp)
    have hl : terminalRepairLabels r c U L d = (e s,e t) :=
      defectLabels_eq_of_spec small B r c L (terminalPositiveDefect r c U L d) (e s,e t) hd
    have hi := congrArg (fun uv : Cells small × Cells small =>
      ((e.symm uv.1).val,(e.symm uv.2).val)) hl
    simpa only [Equiv.symm_apply_apply] using hi.symm

lemma catalog_getD_actual (s : Cells small) :
    (smallCellCatalog ((List.ofFn r,List.ofFn c),U)).getD (e.symm s).val (0,0) =
      (s.val.1.val,s.val.2.val) := by
  have hcat : smallCellCatalog ((List.ofFn r,List.ofFn c),U) =
      List.ofFn (fun i => ((e i).val.1.val,(e i).val.2.val)) := by
    simpa only [Math115.PhysicalComputedProposal.computedCatalog, cellCatalog] using
      (Math115.PhysicalComputedProposal.computedCellEquiv_catalog r c U).symm
  rw [hcat]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, (e.symm s).isLt,
    dite_true, Option.getD_some, Equiv.apply_symm_apply]

/-- The raw search returns the actual ordered natural-coordinate labels;
no semantic label input or arbitrary choice is needed by the program. -/
theorem orderedDefectLabelCode_eq (a : DefectJoint r c U L) :
    orderedDefectLabelCode (List.ofFn r) (List.ofFn c) U (computedStateCode r c U L a.1.val) =
      some (terminalOrderedLabelCode r c U L a) := by
  unfold orderedDefectLabelCode
  rw [orderedDefectLabelIndices_eq, Option.map_some]
  simp only [catalog_getD_actual, terminalOrderedLabelCode]

variable (hr : 0 < (largeIndices (U,List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U,List.ofFn c)).length)

/-- Full terminal corrected output from raw state views and the actual
residual code. Only the actual state/residual encoding hypotheses remain;
there is no supplied full source matrix, labels, or desired-law premise. -/
theorem jointAutoCorrectionCode_eq (a : DefectJoint r c U L) (k : ℕ) (word : Fin k → Bool) :
    jointAutoCorrectionCode (List.ofFn r) (List.ofFn c) U L k
      (computedStateCode r c U L a.1.val) (jointResidualMatrixCode r c U L hr hc a)
      (List.ofFn word) =
      (terminalBitCorrection r c U L k a word).map (fun X => matrixCode X.val) := by
  unfold jointAutoCorrectionCode
  rw [orderedDefectLabelCode_eq]
  exact jointTerminalCorrectionCode_eq r c U L hr hc a k word

end
end Math115.PhysicalTraceJoin
