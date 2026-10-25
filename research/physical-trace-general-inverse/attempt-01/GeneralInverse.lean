/-
SPDX-License-Identifier: Apache-2.0
Arithmetic inverse candidates for the literal completion-retaining repair.
The inverse keeps both full views and is certified on actual joint fibres.
-/
import ResearchPhysicalTraceJoin.GeneralRepair
import OAI.Combinatorics.ContingencyTables.Sampling.InverseSmallRepair
import OAI.Combinatorics.ContingencyTables.Sampling.SmallDefectLabels

set_option maxHeartbeats 1200000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open SmallContextFibres PaddedCompletions
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalStationarySuccess
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)

local notation "small" => firstPaperSmall r c U
local notation "B" => capacity r c U L
local notation "rbar" => (fun i => r i + rowLargeCount small i * L)
local notation "cbar" => (fun j => c j + columnLargeCount small j * L)

/-- Full padded target of an arbitrary ordinary table. -/
def inverseTarget (X : Table r c) : Table rbar cbar :=
  Math115.PhysicalStateNonempty.paddedTable small L X

def inverseRowView (Y : Fin m → Fin n → ℕ) (s t : Fin m × Fin n) : Fin m → Fin n → ℕ :=
  fun i j => (transferInt Y (t.1, s.2) t i j).toNat

def inverseColumnView (Y : Fin m → Fin n → ℕ) (s t : Fin m × Fin n) : Fin m → Fin n → ℕ :=
  fun i j => (transferInt Y (t.1, s.2) s i j).toNat

lemma inverseRowView_cast (Y : Fin m → Fin n → ℕ) (s t : Fin m × Fin n)
    (hpos : 0 < Y t.1 s.2) (i : Fin m) (j : Fin n) :
    (inverseRowView Y s t i j : ℤ) = transferInt Y (t.1, s.2) t i j :=
  Int.toNat_of_nonneg (transferInt_nonnegative Y (t.1, s.2) t hpos i j)

lemma inverseColumnView_cast (Y : Fin m → Fin n → ℕ) (s t : Fin m × Fin n)
    (hpos : 0 < Y t.1 s.2) (i : Fin m) (j : Fin n) :
    (inverseColumnView Y s t i j : ℤ) = transferInt Y (t.1, s.2) s i j :=
  Int.toNat_of_nonneg (transferInt_nonnegative Y (t.1, s.2) s hpos i j)

lemma inverseViews_defect (Y : Fin m → Fin n → ℕ) (s t : Fin m × Fin n)
    (hne : s ≠ t) (hpos : 0 < Y t.1 s.2) :
    IsDefect (inverseRowView Y s t) (inverseColumnView Y s t) s t := by
  refine ⟨hne, ?_⟩
  intro i j
  rw [inverseColumnView_cast Y s t hpos]
  simp only [transferInt]
  rw [inverseRowView_cast Y s t hpos]
  simp only [transferInt]
  omega

lemma inverseViews_repair (Y : Fin m → Fin n → ℕ) (s t : Fin m × Fin n)
    (hne : s ≠ t) (hpos : 0 < Y t.1 s.2) :
    repairMatrix (inverseRowView Y s t) s t = Y := by
  funext i j
  apply Int.natCast_inj.mp
  rw [repairMatrix_cast (inverseViews_defect Y s t hne hpos), transferInt,
    inverseRowView_cast Y s t hpos]
  simp only [transferInt]
  omega

lemma inverseViews_margins {r' : Fin m → ℕ} {c' : Fin n → ℕ}
    (Y : Table r' c') (s t : Fin m × Fin n) (hpos : 0 < Y.val t.1 s.2) :
    (∀ i, ∑ j, inverseRowView Y.val s t i j = r' i) ∧
      (∀ j, ∑ i, inverseColumnView Y.val s t i j = c' j) := by
  constructor
  · intro i
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [inverseRowView_cast Y.val s t hpos]
    rw [transferInt_row]
    simp [← Nat.cast_sum, Y.property.1]
  · intro j
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [inverseColumnView_cast Y.val s t hpos]
    rw [transferInt_column]
    simp [← Nat.cast_sum, Y.property.2]

lemma ordinary_small_lt (X : Table r c) (i : Fin m) (j : Fin n)
    (hij : small i j = true) : X.val i j < U := by
  have hr : X.val i j ≤ r i := by
    rw [← X.property.1 i]
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (X.val i k)) (Finset.mem_univ j)
  have hc : X.val i j ≤ c j := by
    rw [← X.property.2 j]
    exact Finset.single_le_sum (fun k _ => Nat.zero_le (X.val k j)) (Finset.mem_univ i)
  have hinc : r i < U ∨ c j < U := by
    simpa only [firstPaperSmall, decide_eq_true_eq] using hij
  rcases hinc with hinc | hinc
  · exact hr.trans_lt hinc
  · exact hc.trans_lt hinc

lemma inverseTarget_small_lt (X : Table r c) (i : Fin m) (j : Fin n)
    (hij : small i j = true) : (inverseTarget r c U L X).val i j < U := by
  simpa only [inverseTarget, Math115.PhysicalStateNonempty.paddedTable,
    hij, ite_true, Nat.add_zero] using ordinary_small_lt r c U X i j hij

lemma inverseViews_small_cap (X : Table r c) (s t : Cells small)
    (hpos : 0 < (inverseTarget r c U L X).val t.val.1 s.val.2)
    (i : Fin m) (j : Fin n) (hij : small i j = true) :
    inverseRowView (inverseTarget r c U L X).val s.val t.val i j ≤ B i j ∧
      inverseColumnView (inverseTarget r c U L X).val s.val t.val i j ≤ B i j := by
  rw [capacity_small r c U L i j hij]
  have hY := inverseTarget_small_lt r c U L X i j hij
  have hx := inverseRowView_cast (inverseTarget r c U L X).val s.val t.val hpos i j
  have hq := inverseColumnView_cast (inverseTarget r c U L X).val s.val t.val hpos i j
  simp only [transferInt] at hx hq
  constructor <;> split_ifs at hx hq <;> omega

/-- Dense source views agree and are no larger than the padded target. -/
lemma inverseViews_large (X : Table r c) (s t : Cells small)
    (hpos : 0 < (inverseTarget r c U L X).val t.val.1 s.val.2)
    (i : Fin m) (j : Fin n) (hij : small i j = false) :
    inverseRowView (inverseTarget r c U L X).val s.val t.val i j =
      inverseColumnView (inverseTarget r c U L X).val s.val t.val i j ∧
    inverseRowView (inverseTarget r c U L X).val s.val t.val i j ≤
      (inverseTarget r c U L X).val i j := by
  have hns : ¬(i = s.val.1 ∧ j = s.val.2) := by
    rintro ⟨rfl, rfl⟩
    rw [s.property] at hij
    contradiction
  have hnt : ¬(i = t.val.1 ∧ j = t.val.2) := by
    rintro ⟨rfl, rfl⟩
    rw [t.property] at hij
    contradiction
  have hx := inverseRowView_cast (inverseTarget r c U L X).val s.val t.val hpos i j
  have hq := inverseColumnView_cast (inverseTarget r c U L X).val s.val t.val hpos i j
  simp only [transferInt, hns, hnt, ite_false, add_zero] at hx hq
  constructor
  · omega
  · split_ifs at hx <;> omega

/-- A concrete arithmetic test on the two full inverse views. No fibre
cardinality or existence assertion is hidden in this predicate. -/
def InverseLocalTest (X : Table r c) (st : Cells small × Cells small) : Prop :=
  st.1 ≠ st.2 ∧ 0 < (inverseTarget r c U L X).val st.2.val.1 st.1.val.2 ∧
    (∀ i, smallRow small
      (inverseRowView (inverseTarget r c U L X).val st.1.val st.2.val) i ≤ r i) ∧
    (∀ j, smallColumnView small
      (inverseColumnView (inverseTarget r c U L X).val st.1.val st.2.val) j ≤ c j)

abbrev InverseLocalLabels (X : Table r c) :=
  {st : Cells small × Cells small // InverseLocalTest r c U L X st}

def inverseNaturalProfile (X : Table r c) (st : Cells small × Cells small) : SmallProfile small :=
  fun a => if a.2 then B a.1.val.1 a.1.val.2 -
    inverseColumnView (inverseTarget r c U L X).val st.1.val st.2.val a.1.val.1 a.1.val.2
    else inverseRowView (inverseTarget r c U L X).val st.1.val st.2.val a.1.val.1 a.1.val.2

lemma inverseNaturalProfile_bounded (X : Table r c) (st : InverseLocalLabels r c U L X) :
    ∀ a, inverseNaturalProfile r c U L X st.val a ≤ B a.1.val.1 a.1.val.2 := by
  rintro ⟨a,b⟩
  cases b
  · exact (inverseViews_small_cap r c U L X st.val.1 st.val.2 st.property.2.1
      a.val.1 a.val.2 a.property).1
  · exact Nat.sub_le _ _

lemma inverseNaturalProfile_small (X : Table r c) (st : InverseLocalLabels r c U L X)
    (i : Fin m) (j : Fin n) (hij : small i j = true) :
    smallView small (inverseNaturalProfile r c U L X st.val) false i j =
      inverseRowView (inverseTarget r c U L X).val st.val.1.val st.val.2.val i j ∧
    smallQ small B (inverseNaturalProfile r c U L X st.val) i j =
      inverseColumnView (inverseTarget r c U L X).val st.val.1.val st.val.2.val i j := by
  constructor
  · simp only [smallView, hij, dite_eq_left, inverseNaturalProfile, Bool.false_eq_true, ite_false]
  · simp only [smallQ, hij, dite_eq_left, inverseNaturalProfile, ite_true]
    exact Nat.sub_sub_self (inverseViews_small_cap r c U L X st.val.1 st.val.2
      st.property.2.1 i j hij).2

lemma inverseNaturalProfile_defect (X : Table r c) (st : InverseLocalLabels r c U L X) :
    IsDefect (smallView small (inverseNaturalProfile r c U L X st.val) false)
      (smallQ small B (inverseNaturalProfile r c U L X st.val)) st.val.1.val st.val.2.val := by
  have hne : st.val.1.val ≠ st.val.2.val := fun h => st.property.1 (Subtype.ext h)
  have hd := inverseViews_defect (inverseTarget r c U L X).val
    st.val.1.val st.val.2.val hne st.property.2.1
  refine ⟨hne, ?_⟩
  intro i j
  cases hij : small i j with
  | false =>
    have hns : ¬(i = st.val.1.val.1 ∧ j = st.val.1.val.2) := by
      rintro ⟨rfl, rfl⟩
      rw [st.val.1.property] at hij
      contradiction
    have hnt : ¬(i = st.val.2.val.1 ∧ j = st.val.2.val.2) := by
      rintro ⟨rfl, rfl⟩
      rw [st.val.2.property] at hij
      contradiction
    simp [smallView, smallQ, hij, transferInt, hns, hnt]
  | true =>
    rw [(inverseNaturalProfile_small r c U L X st i j hij).2]
    unfold transferInt
    rw [(inverseNaturalProfile_small r c U L X st i j hij).1]
    exact hd.2 i j

lemma inverseTarget_cap (X : Table r c) (i : Fin m) (j : Fin n) :
    (inverseTarget r c U L X).val i j ≤ B i j :=
  paper_residual_capacity r c (dimensionAllowance (I := Fin m) (J := Fin n))
    L U dimension_le_allowance
    ⟨inverseTarget r c U L X,
      paddedTable_small_rows small L X, paddedTable_small_columns small L X⟩ i j

/-- The entire particular inverse completion, including a possible dense
crossing subtraction, is an actual member of the source fibre. -/
def inverseCompletion (X : Table r c) (st : InverseLocalLabels r c U L X) :
    CompletionFibre small B r rbar c cbar (inverseNaturalProfile r c U L X st.val) := by
  let Y := inverseTarget r c U L X
  have hm := inverseViews_margins Y st.val.1.val st.val.2.val st.property.2.1
  refine ⟨⟨(inverseRowView Y.val st.val.1.val st.val.2.val,
    inverseColumnView Y.val st.val.1.val st.val.2.val),hm.1,hm.2⟩,
    st.property.2.2.1,st.property.2.2.2,?_,?_,?_⟩
  · intro i j hij
    constructor
    · rfl
    · exact (inverseNaturalProfile_small r c U L X st i j hij).2.symm
  · intro i j hij
    exact (inverseViews_large r c U L X st.val.1 st.val.2 st.property.2.1 i j hij).1
  · intro i j hij
    exact (inverseViews_large r c U L X st.val.1 st.val.2 st.property.2.1 i j hij).2.trans
      (inverseTarget_cap r c U L X i j)

/-- Positive weight is proved from the explicit completion, not postulated. -/
lemma inverseNaturalProfile_positive (X : Table r c) (st : InverseLocalLabels r c U L X) :
    0 < hardMarginal small B r c L (inverseNaturalProfile r c U L X st.val) := by
  rw [hardMarginal_eq_fibre_card small B r c L _
    (inverseNaturalProfile_bounded r c U L X st)]
  exact_mod_cast Fintype.card_pos_iff.mpr (⟨inverseCompletion r c U L X st⟩ : Nonempty _)

/-- The inverse candidate is an actual defect state of the terminal joint. -/
def inverseDefectState (X : Table r c) (st : InverseLocalLabels r c U L X) :
    DefectVertices r c U L := by
  let v := inverseNaturalProfile r c U L X st.val
  have hd := inverseNaturalProfile_defect r c U L X st
  have hp : SingleDefect small B v :=
    ⟨st.val.1.val, st.val.2.val, st.val.1.property, st.val.2.property, hd⟩
  let z : States r c U L :=
    ⟨⟨fun a => ⟨v a, Nat.lt_succ_of_le (inverseNaturalProfile_bounded r c U L X st a)⟩,
      Or.inr hp⟩, inverseNaturalProfile_positive r c U L X st⟩
  refine ⟨z, ?_⟩
  intro hb
  exact balanced_not_defect small B v hb hp

def inverseDefectJoint (X : Table r c) (st : InverseLocalLabels r c U L X) :
    DefectJoint r c U L :=
  ⟨inverseDefectState r c U L X st, inverseCompletion r c U L X st⟩

lemma inverseDefectJoint_views (X : Table r c) (st : InverseLocalLabels r c U L X) :
    (inverseDefectJoint r c U L X st).2.val.val =
      (inverseRowView (inverseTarget r c U L X).val st.val.1.val st.val.2.val,
        inverseColumnView (inverseTarget r c U L X).val st.val.1.val st.val.2.val) := rfl

lemma inverseDefectJoint_labels (X : Table r c) (st : InverseLocalLabels r c U L X) :
    terminalRepairLabels r c U L (inverseDefectJoint r c U L X st).1 = st.val := by
  apply defectLabels_eq_of_spec
  exact inverseNaturalProfile_defect r c U L X st

lemma inverseDefectJoint_repair (X : Table r c) (st : InverseLocalLabels r c U L X) :
    (terminalRepairedTable r c U L (inverseDefectJoint r c U L X st)).val =
      inverseTarget r c U L X := by
  apply Subtype.ext
  rw [terminalRepairedTable_matrix, inverseDefectJoint_labels]
  exact inverseViews_repair (inverseTarget r c U L X).val st.val.1.val st.val.2.val
    (fun h => st.property.1 (Subtype.ext h)) st.property.2.1

lemma repair_cross_positive {x q : Fin m → Fin n → ℕ} {s t : Fin m × Fin n}
    (hd : IsDefect x q s t) : 0 < repairMatrix x s t t.1 s.2 := by
  have hcast := repairMatrix_cast hd t.1 s.2
  have hpos := hd.positive_entry
  simp only [transferInt, and_self, ite_true, true_and] at hcast
  by_cases h : s.2 = t.2
  · simp only [h, ite_true] at hcast
    rw [h]
    omega
  · simp only [h, ite_false, sub_zero] at hcast
    omega

/-- On every actual preimage the arithmetic inverse recovers both complete
source views, including all dense entries. -/
lemma inverseViews_of_preimage (X : Table r c) (a : DefectJoint r c U L)
    (he : (terminalRepairedTable r c U L a).val = inverseTarget r c U L X) :
    let st := terminalRepairLabels r c U L a.1
    inverseRowView (inverseTarget r c U L X).val st.1.val st.2.val = a.2.val.val.1 ∧
    inverseColumnView (inverseTarget r c U L X).val st.1.val st.2.val = a.2.val.val.2 := by
  dsimp only
  have hd : IsDefect a.2.val.val.1 a.2.val.val.2
      (terminalRepairLabels r c U L a.1).1.val
      (terminalRepairLabels r c U L a.1).2.val :=
    (terminalJointDefect r c U L a).property.1
  have hp : 0 < (inverseTarget r c U L X).val
      (terminalRepairLabels r c U L a.1).2.val.1
      (terminalRepairLabels r c U L a.1).1.val.2 := by
    rw [← he, terminalRepairedTable_matrix]
    exact repair_cross_positive hd
  constructor
  · funext i j
    apply Int.natCast_inj.mp
    rw [inverseRowView_cast _ _ _ hp]
    have hr := (terminalRepairedTable_views_recover r c U L a i j).1
    dsimp only at hr
    rw [he] at hr
    simp only [transferInt]
    omega
  · funext i j
    apply Int.natCast_inj.mp
    rw [inverseColumnView_cast _ _ _ hp]
    have hr := (terminalRepairedTable_views_recover r c U L a i j).2
    dsimp only at hr
    rw [he] at hr
    simp only [transferInt]
    omega

lemma inverseLocalTest_of_preimage (X : Table r c) (a : DefectJoint r c U L)
    (he : (terminalRepairedTable r c U L a).val = inverseTarget r c U L X) :
    InverseLocalTest r c U L X (terminalRepairLabels r c U L a.1) := by
  have hd := terminalRepairLabels_spec r c U L a.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hl
    exact hd.1 (congrArg Subtype.val hl)
  · rw [← he, terminalRepairedTable_matrix]
    exact repair_cross_positive (terminalJointDefect r c U L a).property.1
  · rw [(inverseViews_of_preimage r c U L X a he).1]
    exact a.2.property.1
  · rw [(inverseViews_of_preimage r c U L X a he).2]
    exact a.2.property.2.1

/-- The actual joint fibre over the ordinary table's successful padded target. -/
abbrev TerminalRepairFibre (X : Table r c) :=
  {a : DefectJoint r c U L //
    (terminalRepairedTable r c U L a).val = inverseTarget r c U L X}

def inverseFibreMap (X : Table r c) (st : InverseLocalLabels r c U L X) :
    TerminalRepairFibre r c U L X :=
  ⟨inverseDefectJoint r c U L X st, inverseDefectJoint_repair r c U L X st⟩

lemma inverseFibreMap_bijective (X : Table r c) :
    Function.Bijective (inverseFibreMap r c U L X) := by
  constructor
  · intro st uv he
    apply Subtype.ext
    have hl := congrArg (fun a : TerminalRepairFibre r c U L X =>
      terminalRepairLabels r c U L a.val.1) he
    simpa only [inverseFibreMap, inverseDefectJoint_labels] using hl
  · intro a
    let st : InverseLocalLabels r c U L X :=
      ⟨terminalRepairLabels r c U L a.val.1, inverseLocalTest_of_preimage r c U L X a.val a.property⟩
    refine ⟨st, ?_⟩
    apply Subtype.ext
    apply terminalRepair_labels_table_injective r c U L
    apply Prod.ext
    · exact inverseDefectJoint_labels r c U L X st
    · apply Subtype.ext
      exact (inverseDefectJoint_repair r c U L X st).trans a.property.symm

/-- Exact, exhaustive inverse characterization by arithmetic label tests.
Every completion is represented once; no projected completion weights occur. -/
def inverseFibreEquiv (X : Table r c) :
    InverseLocalLabels r c U L X ≃ TerminalRepairFibre r c U L X :=
  Equiv.ofBijective (inverseFibreMap r c U L X) (inverseFibreMap_bijective r c U L X)

lemma inverseDefectJoint_success (X : Table r c) (st : InverseLocalLabels r c U L X) :
    TerminalRepairSuccess r c U L (inverseDefectJoint r c U L X st) := by
  intro i j hij
  rw [inverseDefectJoint_repair]
  change L ≤ X.val i j + if small i j then 0 else L
  simp only [hij, Bool.false_eq_true, ite_false]
  omega

def inverseSuccessfulRepair (X : Table r c) (st : InverseLocalLabels r c U L X) :
    SuccessfulTerminalRepair r c U L :=
  ⟨inverseDefectJoint r c U L X st, inverseDefectJoint_success r c U L X st⟩

lemma inverseSuccessfulRepair_output (X : Table r c) (st : InverseLocalLabels r c U L X) :
    terminalRepairOutput r c U L (inverseSuccessfulRepair r c U L X st) = X := by
  apply Subtype.ext
  funext i j
  rw [terminalRepairOutput_entry]
  change (terminalRepairedTable r c U L (inverseDefectJoint r c U L X st)).val.val i j - _ = _
  rw [inverseDefectJoint_repair]
  change (X.val i j + if small i j then 0 else L) - (if small i j then 0 else L) = _
  exact Nat.add_sub_cancel _ _

end
end Math115.PhysicalTraceJoin
