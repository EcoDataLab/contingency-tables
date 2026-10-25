/-
SPDX-License-Identifier: Apache-2.0
Exact ordinary support/slack characterization and finite label count for the
actual completion-retaining repair. The base inverse construction is separate.
-/
import ResearchPhysicalTraceJoin.GeneralInverse

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

lemma sum_small_indicator_row (mask : Fin m → Fin n → Bool) (w : Fin m × Fin n) (i : Fin m) :
    (∑ j, if mask i j then (if i = w.1 ∧ j = w.2 then (1 : ℤ) else 0) else 0) =
      (if i = w.1 then (if mask w.1 w.2 then 1 else 0) else 0) := by
  by_cases hi : i = w.1
  · subst i
    simp only [true_and, ite_true]
    calc
      _ = ∑ j : Fin n, if j = w.2 then (if mask w.1 w.2 then (1 : ℤ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hj : j = w.2 <;> simp [hj]
      _ = _ := by simp
  · simp [hi]

lemma sum_small_indicator_column (mask : Fin m → Fin n → Bool) (w : Fin m × Fin n) (j : Fin n) :
    (∑ i, if mask i j then (if i = w.1 ∧ j = w.2 then (1 : ℤ) else 0) else 0) =
      (if j = w.2 then (if mask w.1 w.2 then 1 else 0) else 0) := by
  by_cases hj : j = w.2
  · subst j
    simp only [and_true, ite_true]
    calc
      _ = ∑ i : Fin m, if i = w.1 then (if mask w.1 w.2 then (1 : ℤ) else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = w.1 <;> simp [hi]
      _ = _ := by simp
  · simp [hj]

lemma inverseRowView_small_sum (mask : Fin m → Fin n → Bool)
    (Y : Fin m → Fin n → ℕ) (s t : Fin m × Fin n)
    (ht : mask t.1 t.2 = true) (hpos : 0 < Y t.1 s.2) (i : Fin m) :
    smallRow mask (inverseRowView Y s t) i = smallRow mask Y i +
      (if mask t.1 s.2 then 0 else if i = t.1 then 1 else 0) := by
  have he : (smallRow mask (inverseRowView Y s t) i : ℤ) =
      (smallRow mask Y i : ℤ) -
        (if i = t.1 then (if mask t.1 s.2 then 1 else 0) else 0) +
        (if i = t.1 then 1 else 0) := by
    calc
      _ = ∑ j, if mask i j then transferInt Y (t.1, s.2) t i j else (0 : ℤ) := by
        simp only [smallRow, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
        apply Finset.sum_congr rfl
        intro j _
        cases hij : mask i j <;> simp only [hij, Bool.false_eq_true, ite_false, ite_true]
        exact inverseRowView_cast Y s t hpos i j
      _ = (∑ j, if mask i j then (Y i j : ℤ) else 0) -
          (∑ j, if mask i j then (if i = t.1 ∧ j = s.2 then (1 : ℤ) else 0) else 0) +
          (∑ j, if mask i j then (if i = t.1 ∧ j = t.2 then (1 : ℤ) else 0) else 0) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        cases hij : mask i j <;> simp [hij, transferInt]
      _ = _ := by
        rw [sum_small_indicator_row mask (t.1,s.2) i, sum_small_indicator_row mask t i]
        simp only [smallRow, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, ht, ite_true]
  cases hv : mask t.1 s.2 <;> by_cases hi : i = t.1 <;> simp [hv,hi] at he ⊢ <;> omega

lemma inverseColumnView_small_sum (mask : Fin m → Fin n → Bool)
    (Y : Fin m → Fin n → ℕ) (s t : Fin m × Fin n)
    (hs : mask s.1 s.2 = true) (hpos : 0 < Y t.1 s.2) (j : Fin n) :
    smallColumnView mask (inverseColumnView Y s t) j = smallColumnView mask Y j +
      (if mask t.1 s.2 then 0 else if j = s.2 then 1 else 0) := by
  have he : (smallColumnView mask (inverseColumnView Y s t) j : ℤ) =
      (smallColumnView mask Y j : ℤ) -
        (if j = s.2 then (if mask t.1 s.2 then 1 else 0) else 0) +
        (if j = s.2 then 1 else 0) := by
    calc
      _ = ∑ i, if mask i j then transferInt Y (t.1, s.2) s i j else (0 : ℤ) := by
        simp only [smallColumnView, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero]
        apply Finset.sum_congr rfl
        intro i _
        cases hij : mask i j <;> simp only [hij, Bool.false_eq_true, ite_false, ite_true]
        exact inverseColumnView_cast Y s t hpos i j
      _ = (∑ i, if mask i j then (Y i j : ℤ) else 0) -
          (∑ i, if mask i j then (if i = t.1 ∧ j = s.2 then (1 : ℤ) else 0) else 0) +
          (∑ i, if mask i j then (if i = s.1 ∧ j = s.2 then (1 : ℤ) else 0) else 0) := by
        rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        cases hij : mask i j <;> simp [hij, transferInt]
      _ = _ := by
        rw [sum_small_indicator_column mask (t.1,s.2) j, sum_small_indicator_column mask s j]
        simp only [smallColumnView, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, hs, ite_true]
  cases hv : mask t.1 s.2 <;> by_cases hj : j = s.2 <;> simp [hv,hj] at he ⊢ <;> omega

lemma inverseTarget_small_row (X : Table r c) (i : Fin m) :
    smallRow small (inverseTarget r c U L X).val i = smallRow small X.val i := by
  unfold smallRow
  apply Finset.sum_congr rfl
  intro j _
  cases hij : small i j <;> simp [inverseTarget, Math115.PhysicalStateNonempty.paddedTable, hij]

lemma inverseTarget_small_column (X : Table r c) (j : Fin n) :
    smallColumnView small (inverseTarget r c U L X).val j = smallColumnView small X.val j := by
  unfold smallColumnView
  apply Finset.sum_congr rfl
  intro i _
  cases hij : small i j <;> simp [inverseTarget, Math115.PhysicalStateNonempty.paddedTable, hij]

/-- Ordinary, unpadded row/column slacks decide dense inverse feasibility. -/
def InverseSupportTest (X : Table r c) (st : Cells small × Cells small) : Prop :=
  st.1 ≠ st.2 ∧
    if small st.2.val.1 st.1.val.2 then 0 < X.val st.2.val.1 st.1.val.2 else
      smallRow small X.val st.2.val.1 < r st.2.val.1 ∧
      smallColumnView small X.val st.1.val.2 < c st.1.val.2

lemma inverseLocalTest_iff_support (hL : 1 ≤ L) (X : Table r c) (st : Cells small × Cells small) :
    InverseLocalTest r c U L X st ↔ InverseSupportTest r c U X st := by
  have hR (i : Fin m) : smallRow small X.val i ≤ r i := by
    have h := paddedTable_small_rows small L X i
    change smallRow small (inverseTarget r c U L X).val i ≤ r i at h
    rwa [inverseTarget_small_row] at h
  have hC (j : Fin n) : smallColumnView small X.val j ≤ c j := by
    have h := paddedTable_small_columns small L X j
    change smallColumnView small (inverseTarget r c U L X).val j ≤ c j at h
    rwa [inverseTarget_small_column] at h
  constructor
  · rintro ⟨hne,hpos,hrows,hcols⟩
    refine ⟨hne,?_⟩
    cases hv : small st.2.val.1 st.1.val.2 with
    | false =>
      simp only [hv, Bool.false_eq_true, ite_false]
      have hr := hrows st.2.val.1
      have hc := hcols st.1.val.2
      rw [inverseRowView_small_sum small _ _ _ st.2.property hpos,
        inverseTarget_small_row] at hr
      rw [inverseColumnView_small_sum small _ _ _ st.1.property hpos,
        inverseTarget_small_column] at hc
      simp only [hv, Bool.false_eq_true, ite_false, ite_true] at hr hc
      constructor <;> omega
    | true =>
      simp only [hv, ite_true]
      simpa only [inverseTarget, Math115.PhysicalStateNonempty.paddedTable,
        hv, ite_true, Nat.add_zero] using hpos
  · rintro ⟨hne,hsupport⟩
    have hpos : 0 < (inverseTarget r c U L X).val st.2.val.1 st.1.val.2 := by
      cases hv : small st.2.val.1 st.1.val.2 with
      | false =>
        change 0 < X.val st.2.val.1 st.1.val.2 + if small st.2.val.1 st.1.val.2 then 0 else L
        simp only [hv, Bool.false_eq_true, ite_false]
        omega
      | true =>
        simpa only [hv, ite_true, inverseTarget,
          Math115.PhysicalStateNonempty.paddedTable, Nat.add_zero] using hsupport
    refine ⟨hne,hpos,?_,?_⟩
    · intro i
      rw [inverseRowView_small_sum small _ _ _ st.2.property hpos, inverseTarget_small_row]
      cases hv : small st.2.val.1 st.1.val.2 with
      | false =>
        simp only [hv, Bool.false_eq_true, ite_false] at hsupport ⊢
        by_cases hi : i = st.2.val.1
        · subst i; simp only [ite_true]; omega
        · simp only [hi, ite_false, Nat.add_zero]; exact hR i
      | true => simp only [hv, ite_true, Nat.add_zero]; exact hR i
    · intro j
      rw [inverseColumnView_small_sum small _ _ _ st.1.property hpos, inverseTarget_small_column]
      cases hv : small st.2.val.1 st.1.val.2 with
      | false =>
        simp only [hv, Bool.false_eq_true, ite_false] at hsupport ⊢
        by_cases hj : j = st.1.val.2
        · subst j; simp only [ite_true]; omega
        · simp only [hj, ite_false, Nat.add_zero]; exact hC j
      | true => simp only [hv, ite_true, Nat.add_zero]; exact hC j

abbrev InverseSupportLabels (X : Table r c) :=
  {st : Cells small × Cells small // InverseSupportTest r c U X st}

def inverseSupportFibreEquiv (hL : 1 ≤ L) (X : Table r c) :
    InverseSupportLabels r c U X ≃ TerminalRepairFibre r c U L X :=
  (Equiv.subtypeEquivRight (fun st => (inverseLocalTest_iff_support r c U L hL X st).symm)).trans
    (inverseFibreEquiv r c U L X)

/-- Explicit finite label count, using only ordinary support and slacks. -/
def inverseSupportCount (X : Table r c) : ℕ :=
  ∑ st : Cells small × Cells small, if InverseSupportTest r c U X st then 1 else 0

/-- Exact fibre cardinality from an exhaustive actual inverse construction. -/
theorem terminalRepairFibre_card_eq_supportCount (hL : 1 ≤ L) (X : Table r c) :
    Fintype.card (TerminalRepairFibre r c U L X) = inverseSupportCount r c U X := by
  rw [← Fintype.card_congr (inverseSupportFibreEquiv r c U L hL X)]
  simp only [InverseSupportLabels, Fintype.card_subtype, Finset.card_eq_sum_ones,
    Finset.sum_filter, inverseSupportCount]

/-- The padded-target fibre is exactly the ordinary-output fibre, including
its actual padding-success proof. -/
def repairFibreOutputEquiv (X : Table r c) :
    TerminalRepairFibre r c U L X ≃
      {a : SuccessfulTerminalRepair r c U L // terminalRepairOutput r c U L a = X} where
  toFun a := by
    have hs : TerminalRepairSuccess r c U L a.val := by
      intro i j hij
      rw [a.property]
      change L ≤ X.val i j + if small i j then 0 else L
      simp only [hij, Bool.false_eq_true, ite_false]
      omega
    refine ⟨⟨a.val,hs⟩,?_⟩
    apply Subtype.ext
    funext i j
    rw [terminalRepairOutput_entry]
    change (terminalRepairedTable r c U L a.val).val.val i j - _ = _
    rw [a.property]
    change (X.val i j + if small i j then 0 else L) - (if small i j then 0 else L) = _
    exact Nat.add_sub_cancel _ _
  invFun a := ⟨a.val.val, by
    rw [← terminalRepairOutput_repad r c U L a.val, a.property]
    rfl⟩
  left_inv a := by apply Subtype.ext; rfl
  right_inv a := by apply Subtype.ext; apply Subtype.ext; rfl

/-- Actual ordinary-table output multiplicity, without any completion-count
oracle or assumed inverse cardinality. -/
theorem terminalOutput_card_eq_supportCount (hL : 1 ≤ L) (X : Table r c) :
    Fintype.card {a : SuccessfulTerminalRepair r c U L // terminalRepairOutput r c U L a = X} =
      inverseSupportCount r c U X := by
  rw [← Fintype.card_congr (repairFibreOutputEquiv r c U L X)]
  exact terminalRepairFibre_card_eq_supportCount r c U L hL X

end
end Math115.PhysicalTraceJoin
