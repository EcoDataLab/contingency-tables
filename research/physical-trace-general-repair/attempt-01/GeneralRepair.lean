/-
SPDX-License-Identifier: Apache-2.0
Literal completion-retaining repair of the terminal defect joint.
Feasibility, entry formulas, recovery, and the padding-test output map only.
No inverse-fibre count or corrected acceptance law is assumed.
-/
import ResearchPhysicalTraceJoin.Terminal
import Math115.PhysicalStationarySuccess

set_option maxHeartbeats 800000

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

/-- The source's positive defect, on this exact physical state. -/
def terminalPositiveDefect (d : DefectVertices r c U L) :
    PositiveDefects small B r c L :=
  ⟨d.val.val.val, defect_isSingleDefect r c U L d, d.val.property⟩

def terminalRepairLabels (d : DefectVertices r c U L) : Cells small × Cells small :=
  defectLabels small B r c L (terminalPositiveDefect r c U L d)

lemma terminalRepairLabels_spec (d : DefectVertices r c U L) :
    IsDefect (smallView small (physicalProfile small B r c L d.val) false)
      (smallQ small B (physicalProfile small B r c L d.val))
      (terminalRepairLabels r c U L d).1.val (terminalRepairLabels r c U L d).2.val :=
  defectLabels_spec small B r c L (terminalPositiveDefect r c U L d)

/-- Both full source views retain the particular sampled dense completion. -/
def terminalJointDefect (a : DefectJoint r c U L) :
    JointDefect small r c rbar cbar
      (terminalRepairLabels r c U L a.1).1.val
      (terminalRepairLabels r c U L a.1).2.val :=
  completionJointDefect small B r rbar c cbar
    (physicalProfile small B r c L a.1.val)
    (terminalRepairLabels r c U L a.1).1.val
    (terminalRepairLabels r c U L a.1).2.val
    (terminalRepairLabels r c U L a.1).1.property
    (terminalRepairLabels r c U L a.1).2.property
    (terminalRepairLabels_spec r c U L a.1) a.2

/-- The actual source repair, with the sampled completion still present. -/
def terminalRepairedTable (a : DefectJoint r c U L) :
    ResidualTables small r c rbar cbar :=
  jointRepair (terminalRepairLabels r c U L a.1).1.property
    (terminalRepairLabels r c U L a.1).2.property (terminalJointDefect r c U L a)

lemma terminalRepairedTable_matrix (a : DefectJoint r c U L) :
    (terminalRepairedTable r c U L a).val.val =
      repairMatrix a.2.val.val.1
        (terminalRepairLabels r c U L a.1).1.val
        (terminalRepairLabels r c U L a.1).2.val := rfl

/-- Enlarged margins and both original small-line inequalities hold. -/
theorem terminalRepairedTable_feasible (a : DefectJoint r c U L) :
    HasMargins (terminalRepairedTable r c U L a).val.val rbar cbar ∧
      (∀ i, smallRow small (terminalRepairedTable r c U L a).val.val i ≤ r i) ∧
      (∀ j, smallColumnView small (terminalRepairedTable r c U L a).val.val j ≤ c j) :=
  ⟨(terminalRepairedTable r c U L a).val.property,
    (terminalRepairedTable r c U L a).property⟩

/-- The repaired full table and its ordered labels recover both source views.
This is recovery on the actual image, not inverse feasibility off the image. -/
theorem terminalRepairedTable_views_recover (a : DefectJoint r c U L) (i : Fin m) (j : Fin n) :
    let s := (terminalRepairLabels r c U L a.1).1.val
    let t := (terminalRepairLabels r c U L a.1).2.val
    (a.2.val.val.1 i j : ℤ) =
      ((terminalRepairedTable r c U L a).val.val i j : ℤ) +
        (if i = t.1 ∧ j = t.2 then 1 else 0) -
        (if i = t.1 ∧ j = s.2 then 1 else 0) ∧
    (a.2.val.val.2 i j : ℤ) =
      ((terminalRepairedTable r c U L a).val.val i j : ℤ) +
        (if i = s.1 ∧ j = s.2 then 1 else 0) -
        (if i = t.1 ∧ j = s.2 then 1 else 0) := by
  dsimp only
  have hd := (terminalJointDefect r c U L a).property.1
  have hx := repairMatrix_cast hd i j
  have hq := hd.2 i j
  change (repairMatrix a.2.val.val.1 _ _ i j : ℤ) = _ at hx
  change (a.2.val.val.2 i j : ℤ) = _ at hq
  rw [terminalRepairedTable_matrix]
  simp only [transferInt] at hx hq
  constructor <;> omega

/-- The literal source views determine the labelled physical state and its completion. -/
lemma terminalJointProjection_injective :
    Function.Injective (fun a : DefectJoint r c U L => a.2.val) :=
  fibre_projection_injective small B r rbar c cbar
    (fun d : DefectVertices r c U L => physicalProfile small B r c L d.val)
    (fun d e h => Subtype.ext (physicalProfile_injective small B r c L h))
    (fun d => naturalProfile_bounded d.val.val.val)

/-- Fixing the ordered labels makes the actual completion-retaining repair injective. -/
theorem terminalRepair_labels_table_injective :
    Function.Injective (fun a : DefectJoint r c U L =>
      (terminalRepairLabels r c U L a.1, terminalRepairedTable r c U L a)) := by
  intro a b h
  have hl := congrArg Prod.fst h
  have ht := congrArg Prod.snd h
  apply terminalJointProjection_injective r c U L
  apply Subtype.ext
  apply Prod.ext
  · funext i j
    apply Int.natCast_inj.mp
    have ha := (terminalRepairedTable_views_recover r c U L a i j).1
    have hb := (terminalRepairedTable_views_recover r c U L b i j).1
    dsimp only at ha hb
    rw [hl, ht] at ha
    omega
  · funext i j
    apply Int.natCast_inj.mp
    have ha := (terminalRepairedTable_views_recover r c U L a i j).2
    have hb := (terminalRepairedTable_views_recover r c U L b i j).2
    dsimp only at ha hb
    rw [hl, ht] at ha
    omega

/-- Every dense entry is retained, except that the crossing gains one. -/
theorem terminalRepairedTable_large_entry (a : DefectJoint r c U L)
    (i : Fin m) (j : Fin n) (hij : small i j = false) :
    (terminalRepairedTable r c U L a).val.val i j = a.2.val.val.1 i j +
      (if i = (terminalRepairLabels r c U L a.1).2.val.1 ∧
        j = (terminalRepairLabels r c U L a.1).1.val.2 then 1 else 0) := by
  have hnt : ¬(i = (terminalRepairLabels r c U L a.1).2.val.1 ∧
      j = (terminalRepairLabels r c U L a.1).2.val.2) := by
    rintro ⟨rfl, rfl⟩
    have ht := (terminalRepairLabels r c U L a.1).2.property
    rw [ht] at hij
    contradiction
  have hx := (terminalRepairedTable_views_recover r c U L a i j).1
  simp only [hnt, ite_false, add_zero] at hx
  split_ifs at hx ⊢ <;> omega

theorem terminalRepairedTable_large_crossing (a : DefectJoint r c U L)
    (hv : small (terminalRepairLabels r c U L a.1).2.val.1
      (terminalRepairLabels r c U L a.1).1.val.2 = false) :
    (terminalRepairedTable r c U L a).val.val
        (terminalRepairLabels r c U L a.1).2.val.1
        (terminalRepairLabels r c U L a.1).1.val.2 =
      a.2.val.val.1 (terminalRepairLabels r c U L a.1).2.val.1
        (terminalRepairLabels r c U L a.1).1.val.2 + 1 := by
  simpa only [and_self, ite_true] using terminalRepairedTable_large_entry r c U L a _ _ hv

/-- Residual feasibility forces the true strict small-entry bound. -/
theorem terminalRepairedTable_small_lt (a : DefectJoint r c U L)
    (i : Fin m) (j : Fin n) (hij : small i j = true) :
    (terminalRepairedTable r c U L a).val.val i j < U := by
  rw [terminalRepairedTable_matrix]
  exact repairMatrix_small_capacity r c U
    (terminalJointDefect r c U L a).property.1
    (terminalRepairLabels r c U L a.1).1.property
    (terminalRepairLabels r c U L a.1).2.property
    a.2.property.1 a.2.property.2.1 i j hij

/-- Canonical balanced-joint packaging of the very same repaired matrix. -/
def terminalRepairedJoint (a : DefectJoint r c U L) : Joint r c U L :=
  jointOfTable small B r c L U (capacity_small r c U L)
    (terminalRepairedTable r c U L a).val
    (fun i j hij => (terminalRepairedTable_small_lt r c U L a i j hij).le)
    (terminalRepairedTable r c U L a).property.1
    (terminalRepairedTable r c U L a).property.2
    (fun i j _ => paper_residual_capacity r c
      (dimensionAllowance (I := Fin m) (J := Fin n)) L U dimension_le_allowance
      (terminalRepairedTable r c U L a) i j)

lemma terminalRepairedJoint_table (a : DefectJoint r c U L) :
    jointTable r c U L (terminalRepairedJoint r c U L a) =
      (terminalRepairedTable r c U L a).val := by
  apply Subtype.ext
  rfl

/-- The actual repaired-matrix padding test, before an inverse-fibre coin. -/
def TerminalRepairSuccess (a : DefectJoint r c U L) : Prop :=
  ∀ i j, small i j = false → L ≤ (terminalRepairedTable r c U L a).val.val i j

abbrev SuccessfulTerminalRepair :=
  {a : DefectJoint r c U L // TerminalRepairSuccess r c U L a}

def terminalSuccessfulJoint (a : SuccessfulTerminalRepair r c U L) :
    SuccessfulJoint r c U L :=
  ⟨terminalRepairedJoint r c U L a.val, by
    intro i j hij
    rw [terminalRepairedJoint_table]
    exact a.property i j hij⟩

/-- Every actual repaired joint passing the padding test produces an
ordinary table with the original margins. No output law is postulated. -/
def terminalRepairOutput (a : SuccessfulTerminalRepair r c U L) : Table r c :=
  unpadSuccessfulJoint r c U L (terminalSuccessfulJoint r c U L a)

lemma terminalRepairOutput_entry (a : SuccessfulTerminalRepair r c U L)
    (i : Fin m) (j : Fin n) :
    (terminalRepairOutput r c U L a).val i j =
      (terminalRepairedTable r c U L a.val).val.val i j -
        (if small i j then 0 else L) := by
  rw [terminalRepairOutput, unpadSuccessfulJoint_val]
  change (jointTable r c U L (terminalRepairedJoint r c U L a.val)).val i j - _ = _
  rw [terminalRepairedJoint_table]
  cases hs : small i j <;> simp [large, largePadding, hs]

theorem terminalRepairOutput_hasMargins (a : SuccessfulTerminalRepair r c U L) :
    HasMargins (terminalRepairOutput r c U L a).val r c :=
  (terminalRepairOutput r c U L a).property

/-- Padding the returned ordinary table recovers the literal repaired full table. -/
theorem terminalRepairOutput_repad (a : SuccessfulTerminalRepair r c U L) :
    paddedTable small L (terminalRepairOutput r c U L a) =
      (terminalRepairedTable r c U L a.val).val := by
  apply Subtype.ext
  funext i j
  change (terminalRepairOutput r c U L a).val i j + (if small i j then 0 else L) = _
  rw [terminalRepairOutput_entry]
  cases hs : small i j with
  | false =>
    simp only [hs, Bool.false_eq_true, ite_false]
    exact Nat.sub_add_cancel (a.property i j hs)
  | true => simp [hs]

/-- The existing ordinary-table/successful-joint equivalence identifies
this concrete output with its actual repaired successful joint. -/
theorem terminalRepairOutput_successfulJoint (a : SuccessfulTerminalRepair r c U L) :
    originalSuccessfulJoint r c U L (terminalRepairOutput r c U L a) =
      terminalSuccessfulJoint r c U L a :=
  (successfulJointEquiv r c U L).apply_symm_apply (terminalSuccessfulJoint r c U L a)

end
end Math115.PhysicalTraceJoin
