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
  (List.range rs.length).map (fun i => (List.range cs.length).map (fun j =>
    correctionRepairEntry A s t i j))

/-- Inspect all full repaired large-cell entries, including the crossing. -/
def correctionPaddingTest (rs cs : List ℕ) (U L : ℕ) (A : MatrixCode) : Bool :=
  (List.range rs.length).all (fun i => (List.range cs.length).all (fun j =>
    decide (smallCellTest (((rs,cs),U),(i,j)) = false → L ≤ matrixEntry (A,(i,j)))))

def correctionUnpadCode (rs cs : List ℕ) (U L : ℕ) (A : MatrixCode) : MatrixCode :=
  (List.range rs.length).map (fun i => (List.range cs.length).map (fun j =>
    matrixEntry (A,(i,j)) - (if smallCellTest (((rs,cs),U),(i,j)) then 0 else L)))

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

private lemma correction_map_range {A : Type} (N : ℕ) (f : ℕ → A) :
    (List.range N).map f = List.ofFn (fun i : Fin N => f i.val) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_ofFn]
  · intro k hk hk'
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]

private lemma correction_nat_transfer (x y a b : ℕ)
    (h : (x : ℤ) = (y : ℤ) + (b : ℤ) - (a : ℤ)) : (x + a) - b = y := by
  omega

lemma correctionRepairCode_eq (a : DefectJoint r c U L) :
    correctionRepairCode (List.ofFn r) (List.ofFn c) (terminalSourceMatrixCode r c U L a)
      (terminalOrderedLabelCode r c U L a).1 (terminalOrderedLabelCode r c U L a).2 =
      matrixCode (terminalRepairedTable r c U L a).val.val := by
  unfold correctionRepairCode
  rw [List.length_ofFn, List.length_ofFn, correction_map_range]
  change List.ofFn _ = List.ofFn _
  apply congrArg List.ofFn
  funext i
  rw [correction_map_range]
  apply congrArg List.ofFn
  funext j
  have h := (terminalRepairedTable_views_recover r c U L a i j).1
  dsimp only at h
  simp only [Fin.ext_iff] at h
  simp only [correctionRepairEntry, terminalSourceMatrixCode, terminalOrderedLabelCode,
    matrixEntry_code]
  have h' : (a.2.val.val.1 i j : ℤ) =
      ((terminalRepairedTable r c U L a).val.val i j : ℤ) +
        ((if i.val = (terminalRepairLabels r c U L a.1).2.val.1.val ∧
          j.val = (terminalRepairLabels r c U L a.1).2.val.2.val then 1 else 0 : ℕ) : ℤ) -
        ((if i.val = (terminalRepairLabels r c U L a.1).2.val.1.val ∧
          j.val = (terminalRepairLabels r c U L a.1).1.val.2.val then 1 else 0 : ℕ) : ℤ) := by
    simpa only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero] using h
  exact correction_nat_transfer _ _ _ _ h'

lemma correctionPaddingTest_code (Y : Fin m → Fin n → ℕ) :
    correctionPaddingTest (List.ofFn r) (List.ofFn c) U L (matrixCode Y) = true ↔
      ∀ i j, firstPaperSmall r c U i j = false → L ≤ Y i j := by
  simp only [correctionPaddingTest, List.all_eq_true, List.mem_range,
    List.length_ofFn, decide_eq_true_eq]
  constructor
  · intro h i j
    have hz := h i.val i.isLt j.val j.isLt
    simpa only [listedSmallCellTest_code, matrixEntry_code] using hz
  · intro h i hi j hj
    let ii : Fin m := ⟨i,hi⟩
    let jj : Fin n := ⟨j,hj⟩
    change smallCellTest (((List.ofFn r,List.ofFn c),U),(ii.val,jj.val)) = false →
      L ≤ matrixEntry (matrixCode Y,(ii.val,jj.val))
    rw [listedSmallCellTest_code, matrixEntry_code]
    exact h ii jj

lemma correctionUnpadCode_eq (a : SuccessfulTerminalRepair r c U L) :
    correctionUnpadCode (List.ofFn r) (List.ofFn c) U L
      (matrixCode (terminalRepairedTable r c U L a.val).val.val) =
      matrixCode (terminalRepairOutput r c U L a).val := by
  unfold correctionUnpadCode
  rw [List.length_ofFn, List.length_ofFn, correction_map_range]
  change List.ofFn _ = List.ofFn _
  apply congrArg List.ofFn
  funext i
  rw [correction_map_range]
  apply congrArg List.ofFn
  funext j
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
    simp only [hp, ite_true, terminalPartialRepair, dite_eq_left h, Option.map_some]
    exact congrArg some (correctionUnpadCode_eq r c U L ⟨a,h⟩)
  · have hp : correctionPaddingTest (List.ofFn r) (List.ofFn c) U L
        (matrixCode (terminalRepairedTable r c U L a).val.val) ≠ true :=
      fun hh => h (ht.mp hh)
    simp only [hp, Bool.false_eq_true, ite_false, terminalPartialRepair, dite_eq_right h, Option.map_none]

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
