/-
SPDX-License-Identifier: Apache-2.0
Computed scale and branch preparation for the sharper physical trace.
All dimensions, large indices and small cells are recomputed from the
supplied lists. This classifies an input; it does not initialize a defect,
transport physical states between shapes, or implement an outer sampler.
-/
import Research.AggregateShapeTrace
import Math115.PhysicalComputedProposal
import OAI.Combinatorics.ContingencyTables.Transport.FiniteDeterministicJoint

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles CompletionCounts SmallContextCoordinates
open FirstSuccess ResidualMixture
open Math115.RetainedChainSquare
open scoped BigOperators Classical

def traceCutoff (z : List ℕ × List ℕ) : ℕ :=
  11 * marginDimension z * (z.1.length + z.2.length - 2)

def traceLargeRows (z : List ℕ × List ℕ) : List ℕ :=
  largeIndices (traceCutoff z, z.1)

def traceLargeColumns (z : List ℕ × List ℕ) : List ℕ :=
  largeIndices (traceCutoff z, z.2)

def traceSmallCatalog (z : List ℕ × List ℕ) : List (ℕ × ℕ) :=
  smallCellCatalog (z, traceCutoff z)

def traceBothLarge (z : List ℕ × List ℕ) : Bool :=
  decide (0 < (traceLargeRows z).length) && decide (0 < (traceLargeColumns z).length)

inductive TraceInputBranch where
  | deterministic
  | noSmall
  | unit
  | reference
  deriving DecidableEq, Repr

/-- A preparation classifier. The reference tag does not assert that a
defect exists or select one. The no-small tag is a separate table branch. -/
def traceInputBranch (z : List ℕ × List ℕ) : TraceInputBranch :=
  if z.1.length ≤ 1 ∨ z.2.length ≤ 1 then .deterministic
  else if 2 ≤ (traceSmallCatalog z).length then
    if traceBothLarge z then .reference else .unit
  else .noSmall

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)

theorem traceCutoff_ofFn :
    traceCutoff (List.ofFn r, List.ofFn c) = squareCutoff (I := Fin m) (J := Fin n) := by
  simp only [traceCutoff, marginDimension, List.length_ofFn, squareCutoff,
    dimensionAllowance, Fintype.card_fin]

theorem traceSmallCatalog_ofFn :
    traceSmallCatalog (List.ofFn r, List.ofFn c) =
      Math115.PhysicalComputedProposal.computedCatalog r c
        (squareCutoff (I := Fin m) (J := Fin n)) := by
  unfold traceSmallCatalog Math115.PhysicalComputedProposal.computedCatalog
  rw [traceCutoff_ofFn]

theorem traceSmallCatalog_length :
    (traceSmallCatalog (List.ofFn r, List.ofFn c)).length =
      Fintype.card (Cells (firstPaperSmall r c (squareCutoff (I := Fin m) (J := Fin n)))) := by
  rw [traceSmallCatalog_ofFn]
  exact (Fintype.card_fin _).symm.trans
    (Fintype.card_congr (Math115.PhysicalComputedProposal.computedCellEquiv r c _))

theorem traceBothLarge_ofFn :
    traceBothLarge (List.ofFn r, List.ofFn c) = true ↔
      0 < (largeIndices (squareCutoff (I := Fin m) (J := Fin n), List.ofFn r)).length ∧
      0 < (largeIndices (squareCutoff (I := Fin m) (J := Fin n), List.ofFn c)).length := by
  simp only [traceBothLarge, traceLargeRows, traceLargeColumns, traceCutoff_ofFn,
    Bool.and_eq_true, decide_eq_true_eq]

/-- The first-paper mask is a union of full rows and columns. With both
dimensions at least two it cannot contain exactly one cell. -/
theorem smallCells_zero_or_two (U : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    Fintype.card (Cells (firstPaperSmall r c U)) = 0 ∨
      2 ≤ Fintype.card (Cells (firstPaperSmall r c U)) := by
  by_cases h0 : Fintype.card (Cells (firstPaperSmall r c U)) = 0
  · exact Or.inl h0
  right
  obtain ⟨a⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero h0)
  have ha : r a.val.1 < U ∨ c a.val.2 < U := of_decide_eq_true a.property
  rcases ha with hr | hc
  · let f : Fin n → Cells (firstPaperSmall r c U) :=
      fun j => ⟨(a.val.1, j), by simp [firstPaperSmall, hr]⟩
    have hf : Function.Injective f := by
      intro j k h
      exact congrArg (fun x : Cells (firstPaperSmall r c U) => x.val.2) h
    have hcard := Fintype.card_le_of_injective f hf
    exact hn.trans (by simpa using hcard)
  · let f : Fin m → Cells (firstPaperSmall r c U) :=
      fun i => ⟨(i, a.val.2), by simp [firstPaperSmall, hc]⟩
    have hf : Function.Injective f := by
      intro i k h
      exact congrArg (fun x : Cells (firstPaperSmall r c U) => x.val.1) h
    have hcard := Fintype.card_le_of_injective f hf
    exact hm.trans (by simpa using hcard)

theorem traceInputBranch_deterministic_iff :
    traceInputBranch (List.ofFn r, List.ofFn c) = .deterministic ↔ m ≤ 1 ∨ n ≤ 1 := by
  simp [traceInputBranch, List.length_ofFn]

theorem traceInputBranch_reference_iff :
    traceInputBranch (List.ofFn r, List.ofFn c) = .reference ↔
      2 ≤ m ∧ 2 ≤ n ∧
      2 ≤ Fintype.card (Cells (firstPaperSmall r c (squareCutoff (I := Fin m) (J := Fin n)))) ∧
      0 < (largeIndices (squareCutoff (I := Fin m) (J := Fin n), List.ofFn r)).length ∧
      0 < (largeIndices (squareCutoff (I := Fin m) (J := Fin n), List.ofFn c)).length := by
  simp [traceInputBranch, List.length_ofFn, traceSmallCatalog_length,
    traceBothLarge_ofFn, Nat.not_le, Nat.succ_le_iff, and_assoc]

theorem traceInputBranch_noSmall_iff :
    traceInputBranch (List.ofFn r, List.ofFn c) = .noSmall ↔
      2 ≤ m ∧ 2 ≤ n ∧
      Fintype.card (Cells (firstPaperSmall r c (squareCutoff (I := Fin m) (J := Fin n)))) = 0 := by
  by_cases hm : m ≤ 1
  · simp [traceInputBranch, List.length_ofFn, hm]; omega
  by_cases hn : n ≤ 1
  · simp [traceInputBranch, List.length_ofFn, hn]; omega
  have hm2 : 2 ≤ m := by omega
  have hn2 : 2 ≤ n := by omega
  rcases smallCells_zero_or_two r c (squareCutoff (I := Fin m) (J := Fin n)) hm2 hn2 with h0 | hp
  · simp [traceInputBranch, List.length_ofFn, hm, hn, traceSmallCatalog_length, h0, hm2, hn2]
  · have hne : Fintype.card (Cells (firstPaperSmall r c (squareCutoff (I := Fin m) (J := Fin n)))) ≠ 0 := by omega
    simp [traceInputBranch, List.length_ofFn, hm, hn, traceSmallCatalog_length, hp, hne]

/-- The dimension branch really has a unique table; feasibility supplies
the point, so no new probability or initialization assumption is hidden. -/
theorem deterministicBranch_pointLaw_uniform
    (htotal : (∑ i, r i) = ∑ j, c j)
    (hb : traceInputBranch (List.ofFn r, List.ofFn c) = .deterministic)
    (X : Table r c) :
    letI := table_nonempty r c htotal
    pointLaw X = uniformLaw (α := Table r c) := by
  letI := table_nonempty r c htotal
  have hdim := (traceInputBranch_deterministic_iff r c).mp hb
  have hs : Subsingleton (Table r c) := by
    refine ⟨fun X Y => ?_⟩
    apply Subtype.ext
    funext i j
    rcases hdim with hm | hn
    · have hm1 : m = 1 := by have := i.isLt; omega
      subst m
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      simpa using (X.property.2 j).trans (Y.property.2 j).symm
    · have hn1 : n = 1 := by have := j.isLt; omega
      subst n
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      simpa using (X.property.1 i).trans (Y.property.1 i).symm
  letI := hs
  exact pointLaw_eq_uniform X

/-- Fixed equal-total fixture: dimension-based retuning changes the branch.
This is ordinary kernel reduction by decide, not native_decide. -/
theorem traceBranch_retuning_fixture :
    traceCutoff ([0, 600, 600], [600, 600]) = 726 ∧
    traceCutoff ([600, 600], [600, 600]) = 418 ∧
    traceInputBranch ([0, 600, 600], [600, 600]) = .unit ∧
    traceInputBranch ([600, 600], [600, 600]) = .noSmall := by
  decide

end
end Math115.PhysicalTraceJoin
