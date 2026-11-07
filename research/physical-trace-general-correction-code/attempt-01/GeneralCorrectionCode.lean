/-
SPDX-License-Identifier: Apache-2.0
Computational corrected output on a full retained source-matrix code and
explicit ordered defect labels. The pointwise theorem relates those supplied
codes to the actual typed joint. Encoding a joint from its residual draw and
extracting its labels remain semantic interfaces; no encoded cost is proved.
-/
import ResearchPhysicalTraceJoin.GeneralFiniteCorrection

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open SmallContextFibres PaddedCompletions FirstSuccess ResidualMixture
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.RepairAcceptanceCoin
open scoped BigOperators

/-- The row-view repair subtracts at t and adds at (t.row,s.column).
Natural truncation makes the code total even on malformed supplied data. -/
def correctionRepairEntry (A : MatrixCode) (s t : ℕ × ℕ) (i j : ℕ) : ℕ :=
  (matrixEntry (A,(i,j)) + if i = t.1 ∧ j = s.2 then 1 else 0) -
    (if i = t.1 ∧ j = t.2 then 1 else 0)

def correctionRepairCode (rs cs : List ℕ) (A : MatrixCode) (s t : ℕ × ℕ) : MatrixCode :=
  matrixCode (fun i : Fin rs.length => fun j : Fin cs.length =>
    correctionRepairEntry A s t i.val j.val)

/-- Inspect all full repaired large-cell entries, including the crossing. -/
def correctionPaddingTest (rs cs : List ℕ) (U L : ℕ) (A : MatrixCode) : Bool :=
  decide (∀ i : Fin rs.length, ∀ j : Fin cs.length,
    smallCellTest (((rs,cs),U),(i.val,j.val)) = false → L ≤ matrixEntry (A,(i.val,j.val)))

def correctionUnpadCode (rs cs : List ℕ) (U L : ℕ) (A : MatrixCode) : MatrixCode :=
  matrixCode (fun i : Fin rs.length => fun j : Fin cs.length =>
    matrixEntry (A,(i.val,j.val)) -
      (if smallCellTest (((rs,cs),U),(i.val,j.val)) then 0 else L))

def correctionPartialRepairCode (rs cs : List ℕ) (U L : ℕ)
    (A : MatrixCode) (s t : ℕ × ℕ) : Option MatrixCode :=
  let B := correctionRepairCode rs cs A s t
  if correctionPaddingTest rs cs U L B then some (correctionUnpadCode rs cs U L B) else none

/-- Count small rows/columns from the actual margin lists. -/
def correctionSmallCount (rs : List ℕ) (U : ℕ) : ℕ :=
  (rs.map (fun a => if a < U then 1 else 0)).sum

def correctionAllowanceCode (rs cs : List ℕ) (U : ℕ) : ℕ :=
  let a := correctionSmallCount rs U
  let b := correctionSmallCount cs U
  max (a * (cs.length * a - 1)) (b * (rs.length * b - 1))

/-- Total list/natural/Boolean program. A failed padding test ignores the
reserved suffix; successful outputs use the existing integer threshold and
little-endian bit decoder with the literal ordinary inverse count. -/
def terminalCorrectionCode (rs cs : List ℕ) (U L k : ℕ)
    (A : MatrixCode) (s t : ℕ × ℕ) (bits : List Bool) : Option MatrixCode :=
  partialBitTerminal (correctionPartialRepairCode rs cs U L A s t)
    (listedInverseCount rs cs U) k (correctionAllowanceCode rs cs U)
    (fun i => bits.getD i.val false)

noncomputable section
open scoped Classical
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)

/-- These are proof-side encoders, not a program extracting labels from an
encoded residual draw. The full retained source row view is still supplied. -/
def terminalSourceMatrixCode (a : DefectJoint r c U L) : MatrixCode := matrixCode a.2.val.val.1

def terminalOrderedLabelCode (a : DefectJoint r c U L) : (ℕ × ℕ) × (ℕ × ℕ) :=
  let st := terminalRepairLabels r c U L a.1
  ((st.1.val.1.val,st.1.val.2.val),(st.2.val.1.val,st.2.val.2.val))

lemma correctionRepairCode_eq (a : DefectJoint r c U L) :
    correctionRepairCode (List.ofFn r) (List.ofFn c) (terminalSourceMatrixCode r c U L a)
      (terminalOrderedLabelCode r c U L a).1 (terminalOrderedLabelCode r c U L a).2 =
      matrixCode (terminalRepairedTable r c U L a).val.val := by
  unfold correctionRepairCode
  simp only [List.length_ofFn]
  apply congrArg matrixCode
  funext i j
  have h := (terminalRepairedTable_views_recover r c U L a i j).1
  dsimp only at h
  simp only [Fin.ext_iff] at h
  simp only [correctionRepairEntry, terminalSourceMatrixCode, terminalOrderedLabelCode,
    matrixEntry_code]
  split_ifs at h ⊢ <;> omega

lemma correctionPaddingTest_code (Y : Fin m → Fin n → ℕ) :
    correctionPaddingTest (List.ofFn r) (List.ofFn c) U L (matrixCode Y) = true ↔
      ∀ i j, firstPaperSmall r c U i j = false → L ≤ Y i j := by
  simp only [correctionPaddingTest, List.length_ofFn, decide_eq_true_eq,
    listedSmallCellTest_code, matrixEntry_code]

lemma correctionUnpadCode_eq (a : SuccessfulTerminalRepair r c U L) :
    correctionUnpadCode (List.ofFn r) (List.ofFn c) U L
      (matrixCode (terminalRepairedTable r c U L a.val).val.val) =
      matrixCode (terminalRepairOutput r c U L a).val := by
  unfold correctionUnpadCode
  simp only [List.length_ofFn]
  apply congrArg matrixCode
  funext i j
  rw [matrixEntry_code, listedSmallCellTest_code, terminalRepairOutput_entry]

/-- Exact failure/output correspondence before the correction coin. -/
theorem correctionPartialRepairCode_eq (a : DefectJoint r c U L) :
    correctionPartialRepairCode (List.ofFn r) (List.ofFn c) U L
      (terminalSourceMatrixCode r c U L a)
      (terminalOrderedLabelCode r c U L a).1 (terminalOrderedLabelCode r c U L a).2 =
      (terminalPartialRepair r c U L a).map (fun X => matrixCode X.val) := by
  unfold correctionPartialRepairCode
  rw [correctionRepairCode_eq]
  have ht := correctionPaddingTest_code r c U L (terminalRepairedTable r c U L a).val.val
  change _ ↔ TerminalRepairSuccess r c U L a at ht
  by_cases h : TerminalRepairSuccess r c U L a
  · have hp := ht.mpr h
    simp only [hp, ite_true, terminalPartialRepair, dif_pos h, Option.map_some]
    exact congrArg some (correctionUnpadCode_eq r c U L ⟨a,h⟩)
  · have hp : correctionPaddingTest (List.ofFn r) (List.ofFn c) U L
        (matrixCode (terminalRepairedTable r c U L a).val.val) ≠ true :=
      fun hh => h (ht.mp hh)
    simp only [hp, Bool.false_eq_true, ite_false, terminalPartialRepair, dif_neg h, Option.map_none]

lemma correctionSmallCount_eq {q : ℕ} (rs : Fin q → ℕ) (U : ℕ) :
    correctionSmallCount (List.ofFn rs) U = Fintype.card {i : Fin q // rs i < U} := by
  simp only [correctionSmallCount, List.map_ofFn, List.sum_ofFn, Function.comp_apply,
    Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]

lemma correctionAllowanceCode_eq :
    correctionAllowanceCode (List.ofFn r) (List.ofFn c) U = inverseSupportAllowance r c U := by
  simp only [correctionAllowanceCode, correctionSmallCount_eq, List.length_ofFn,
    inverseSupportAllowance, RepairSmallRows, RepairSmallColumns]

private lemma partialBitTerminal_map {A B : Type*} (f : A → B) (out : Option A)
    (count : B → ℕ) (k c0 : ℕ) (bits : Fin k → Bool) :
    partialBitTerminal (out.map f) count k c0 bits =
      (partialBitTerminal out (fun a => count (f a)) k c0 bits).map f := by
  cases out with
  | none => rfl
  | some a =>
    simp only [Option.map_some, partialBitTerminal]
    unfold bitTerminal integerTerminal
    split_ifs <;> rfl

/-- Pointwise equality on the actual retained source matrix and its actual
ordered defect labels. This supplies a literal terminal output program;
it does not yet encode the upstream joint draw or label extraction. -/
theorem terminalCorrectionCode_eq (a : DefectJoint r c U L) (k : ℕ) (bits : Fin k → Bool) :
    terminalCorrectionCode (List.ofFn r) (List.ofFn c) U L k
      (terminalSourceMatrixCode r c U L a)
      (terminalOrderedLabelCode r c U L a).1 (terminalOrderedLabelCode r c U L a).2
      (List.ofFn bits) =
      (terminalBitCorrection r c U L k a bits).map (fun X => matrixCode X.val) := by
  unfold terminalCorrectionCode
  rw [correctionPartialRepairCode_eq, correctionAllowanceCode_eq]
  have hbits : (fun i : Fin k => (List.ofFn bits).getD i.val false) = bits := by
    funext i
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]
  rw [hbits, partialBitTerminal_map]
  rfl

end
end Math115.PhysicalTraceJoin
