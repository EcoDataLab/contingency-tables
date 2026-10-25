/-
SPDX-License-Identifier: Apache-2.0
A literal ordered-list inverse counter on the existing margin and matrix
codes. Ordinary small-row/column slacks are retained in the Boolean test.
The code is total; semantic equalities require an actual ordinary table code.
-/
import ResearchPhysicalTraceJoin.GeneralTerminalLaw

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles FirstPaperProfiles
open CompletionCounts PhysicalCompletionFibres SmallContextCoordinates
open SmallContextFibres PaddedCompletions
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalStationarySuccess
open scoped BigOperators

/-- Sum the ordinary entries on small cells of one row, using the source
mask test and the existing total matrix decoder. -/
def listedSmallRow (rs cs : List ℕ) (U : ℕ) (A : MatrixCode) (i : ℕ) : ℕ :=
  ((List.range cs.length).map (fun j =>
    if smallCellTest (((rs,cs),U),(i,j)) then matrixEntry (A,(i,j)) else 0)).sum

/-- Ordinary small-column sum; no padded residual is substituted. -/
def listedSmallColumn (rs cs : List ℕ) (U : ℕ) (A : MatrixCode) (j : ℕ) : ℕ :=
  ((List.range rs.length).map (fun i =>
    if smallCellTest (((rs,cs),U),(i,j)) then matrixEntry (A,(i,j)) else 0)).sum

/-- Distinct ordered labels, then positive ordinary small support or BOTH
strict ordinary residual-slack inequalities at a large crossing. -/
def listedInverseLabelTest (rs cs : List ℕ) (U : ℕ) (A : MatrixCode)
    (s t : ℕ × ℕ) : Bool :=
  decide (s ≠ t) &&
    if smallCellTest (((rs,cs),U),(t.1,s.2)) then
      decide (0 < matrixEntry (A,(t.1,s.2))) else
      decide (listedSmallRow rs cs U A t.1 < rs.getD t.1 0 ∧
        listedSmallColumn rs cs U A s.2 < cs.getD s.2 0)

/-- The catalog's literal order is traversed twice. Each ordered pair is
counted once if its Boolean test succeeds; repeated values are not merged. -/
def listedInverseCount (rs cs : List ℕ) (U : ℕ) (A : MatrixCode) : ℕ :=
  let catalog := smallCellCatalog ((rs,cs),U)
  (catalog.map (fun s => (catalog.map (fun t =>
    if listedInverseLabelTest rs cs U A s t then 1 else 0)).sum)).sum

open scoped Classical
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U : ℕ)
local notation "small" => firstPaperSmall r c U

private lemma listed_map_range {A : Type} (N : ℕ) (f : ℕ → A) :
    (List.range N).map f = List.ofFn (fun i : Fin N => f i.val) := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, List.length_ofFn]
  · intro k hk hk'
    simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]

lemma listedSmallCellTest_code (i : Fin m) (j : Fin n) :
    smallCellTest (((List.ofFn r,List.ofFn c),U),(i.val,j.val)) = small i j := by
  simp only [smallCellTest, firstPaperSmall, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, i.isLt, j.isLt, dite_true, Option.getD_some, Fin.eta]

lemma listedSmallRow_code (X : Table r c) (i : Fin m) :
    listedSmallRow (List.ofFn r) (List.ofFn c) U (matrixCode X.val) i.val =
      smallRow small X.val i := by
  unfold listedSmallRow
  rw [List.length_ofFn, listed_map_range, List.sum_ofFn]
  unfold smallRow
  apply Finset.sum_congr rfl
  intro j _
  rw [listedSmallCellTest_code, matrixEntry_code]

lemma listedSmallColumn_code (X : Table r c) (j : Fin n) :
    listedSmallColumn (List.ofFn r) (List.ofFn c) U (matrixCode X.val) j.val =
      smallColumnView small X.val j := by
  unfold listedSmallColumn
  rw [List.length_ofFn, listed_map_range, List.sum_ofFn]
  unfold smallColumnView
  apply Finset.sum_congr rfl
  intro i _
  rw [listedSmallCellTest_code, matrixEntry_code]

lemma listedInverseLabelTest_code (X : Table r c) (s t : Cells small) :
    listedInverseLabelTest (List.ofFn r) (List.ofFn c) U (matrixCode X.val)
      (s.val.1.val,s.val.2.val) (t.val.1.val,t.val.2.val) =
      decide (InverseSupportTest r c U X (s,t)) := by
  have hcoords :
      ((s.val.1.val,s.val.2.val) : ℕ × ℕ) ≠ (t.val.1.val,t.val.2.val) ↔ s ≠ t := by
    constructor
    · intro h he
      subst t
      exact h rfl
    · intro h he
      apply h
      apply Subtype.ext
      exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, listedInverseLabelTest, Bool.and_eq_true,
    listedSmallCellTest_code, hcoords, InverseSupportTest]
  cases hv : small t.val.1 s.val.2 <;>
    simp only [hv, Bool.false_eq_true, ite_false, ite_true, decide_eq_true_eq,
      matrixEntry_code, listedSmallRow_code, listedSmallColumn_code,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, t.val.1.isLt, s.val.2.isLt,
      dite_true, Option.getD_some, Fin.eta]

/-- Literal list enumeration equals the exact support/slack count for an
actual ordinary table code, in the source's computed catalog order. -/
theorem listedInverseCount_eq_supportCount (X : Table r c) :
    listedInverseCount (List.ofFn r) (List.ofFn c) U (matrixCode X.val) =
      inverseSupportCount r c U X := by
  let E := Math115.PhysicalComputedProposal.computedCellEquiv r c U
  have hcat : smallCellCatalog ((List.ofFn r,List.ofFn c),U) =
      List.ofFn (fun i => ((E i).val.1.val,(E i).val.2.val)) := by
    simpa only [Math115.PhysicalComputedProposal.computedCatalog, cellCatalog] using
      (Math115.PhysicalComputedProposal.computedCellEquiv_catalog r c U).symm
  unfold listedInverseCount
  rw [hcat]
  simp only [List.map_ofFn, List.sum_ofFn, listedInverseLabelTest_code, decide_eq_true_eq]
  rw [inverseSupportCount, Fintype.sum_prod_type]
  calc
    _ = ∑ s : Cells small, ∑ j, if InverseSupportTest r c U X (s,E j) then 1 else 0 :=
      E.sum_comp (fun s => ∑ j, if InverseSupportTest r c U X (s,E j) then 1 else 0)
    _ = _ := Finset.sum_congr rfl (fun s _ =>
      E.sum_comp (fun t => if InverseSupportTest r c U X (s,t) then 1 else 0))

/-- Explicit code-premise form; no claim is made for malformed matrix lists. -/
theorem listedInverseCount_eq_supportCount_of_code (X : Table r c) (A : MatrixCode)
    (hA : A = matrixCode X.val) :
    listedInverseCount (List.ofFn r) (List.ofFn c) U A = inverseSupportCount r c U X := by
  subst A
  exact listedInverseCount_eq_supportCount r c U X

/-- The same executable list counter is the true inverse multiplicity of
the actual tested repair/output map. -/
theorem listedInverseCount_eq_terminalInverseCount (L : ℕ) (hL : 1 ≤ L) (X : Table r c) :
    listedInverseCount (List.ofFn r) (List.ofFn c) U (matrixCode X.val) =
      terminalInverseCount r c U L X := by
  rw [listedInverseCount_eq_supportCount, terminalInverseCount_eq_supportCount r c U L hL X]

end
end Math115.PhysicalTraceJoin
