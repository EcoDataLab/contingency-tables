/-
SPDX-License-Identifier: Apache-2.0
Finite-search initialization of the filtered reference branch. The fallback
and support-label search are computational definitions. The inherited actual
inverse-state map remains a noncomputable semantic construction; no encoded
initializer realizer or initializer cost is claimed.
-/
import ResearchPhysicalTraceJoin.ZeroMarginCorrected

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open FirstSuccess ResidualMixture SmallContextFibres
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.RetainedChainSquare Math115.CompletionRetryBudget
open scoped BigOperators

/-- A literal exhaustive row-major list of positions, with no choice. -/
def initializationCells (m n : ℕ) : List (Fin m × Fin n) :=
  (List.finRange m).flatMap (fun i => (List.finRange n).map (fun j => (i,j)))

def initializationPairs (m n : ℕ) : List ((Fin m × Fin n) × (Fin m × Fin n)) :=
  (initializationCells m n).flatMap (fun s => (initializationCells m n).map (fun t => (s,t)))

/-- Both positions are small, distinct, and their ordinary crossing passes
exactly the support/slack test used by the proved actual inverse. -/
def initializationLabelTest {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (U : ℕ) (X : Table r c) (st : (Fin m × Fin n) × (Fin m × Fin n)) : Bool :=
  let small := firstPaperSmall r c U
  small st.1.1 st.1.2 && small st.2.1 st.2.2 &&
    listedInverseLabelTest (List.ofFn r) (List.ofFn c) U (matrixCode X.val)
      (st.1.1.val,st.1.2.val) (st.2.1.val,st.2.2.val)

/-- This searches a finite explicit list; it is not Classical.choose. -/
def initializationLabelSearch {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (U : ℕ) (X : Table r c) : Option ((Fin m × Fin n) × (Fin m × Fin n)) :=
  (initializationPairs m n).find? (initializationLabelTest r c U X)

/-- The existing dimension-recursive greedy constructor is the fallback. -/
def positiveTraceFallback (xs ys : List ℕ)
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) :
    Table (filteredMargin xs) (filteredMargin ys) :=
  GreedyFeasibleTable.table (filteredMargin xs) (filteredMargin ys)
    (filtered_totals_equal xs ys htotal)

lemma mem_initializationCells {m n : ℕ} (s : Fin m × Fin n) :
    s ∈ initializationCells m n := by simp [initializationCells]

lemma mem_initializationPairs {m n : ℕ} (st : (Fin m × Fin n) × (Fin m × Fin n)) :
    st ∈ initializationPairs m n := by
  apply List.mem_flatMap.mpr
  exact ⟨st.1, mem_initializationCells _, List.mem_map.mpr ⟨st.2, mem_initializationCells _, rfl⟩⟩

open scoped Classical
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)

/-- Positive filtered margins and any nonempty small catalog already force
an actual successful inverse over every feasible ordinary table. -/
theorem initialization_inverseSupport_nonempty (X : Table r c)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hp : 0 < Fintype.card (Cells (firstPaperSmall r c U))) :
    Nonempty (InverseSupportLabels r c U X) := by
  have ha := inverseSupportAllowance_positive r c U hm hn hp
  have hb := inverseSupportAllowance_le_count r c U X hr hc
  have hcard : Fintype.card (InverseSupportLabels r c U X) = inverseSupportCount r c U X := by
    simp only [InverseSupportLabels, Fintype.card_subtype, Finset.card_eq_sum_ones,
      Finset.sum_filter, inverseSupportCount]
  apply Fintype.card_pos_iff.mp
  rw [hcard]
  omega

lemma initializationLabelTest_of_support (X : Table r c) (st : InverseSupportLabels r c U X) :
    initializationLabelTest r c U X (st.val.1.val,st.val.2.val) = true := by
  unfold initializationLabelTest
  simp only [st.val.1.property, st.val.2.property, Bool.true_and]
  rw [listedInverseLabelTest_code r c U X st.val.1 st.val.2]
  exact decide_eq_true st.property

/-- The explicit search cannot fail under the reference geometry. -/
theorem initializationLabelSearch_isSome (X : Table r c)
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (hp : 0 < Fintype.card (Cells (firstPaperSmall r c U))) :
    (initializationLabelSearch r c U X).isSome := by
  obtain ⟨st⟩ := initialization_inverseSupport_nonempty r c U X hr hc hm hn hp
  apply List.find?_isSome.mpr
  exact ⟨(st.val.1.val,st.val.2.val), mem_initializationPairs _,
    initializationLabelTest_of_support r c U X st⟩

/-- The returned pair carries exactly the support-label specification. -/
def initializationSupportLabels (X : Table r c)
    (h : (initializationLabelSearch r c U X).isSome) : InverseSupportLabels r c U X := by
  let st := (initializationLabelSearch r c U X).get h
  have ht := List.find?_some (Option.eq_some_of_isSome h)
  change initializationLabelTest r c U X st = true at ht
  unfold initializationLabelTest at ht
  simp only [Bool.and_eq_true] at ht
  let s : Cells (firstPaperSmall r c U) := ⟨st.1,ht.1.1⟩
  let t : Cells (firstPaperSmall r c U) := ⟨st.2,ht.1.2⟩
  refine ⟨(s,t), ?_⟩
  have hz := ht.2
  change listedInverseLabelTest (List.ofFn r) (List.ofFn c) U (matrixCode X.val)
    (s.val.1.val,s.val.2.val) (t.val.1.val,t.val.2.val) = true at hz
  rw [listedInverseLabelTest_code r c U X s t] at hz
  exact of_decide_eq_true hz

/-- Actual inverse construction turns the searched labels into the required
positive-weight defect state. This semantic map inherits noncomputability. -/
def initializationDefectStart (X : Table r c)
    (hL : 1 ≤ L) (h : (initializationLabelSearch r c U X).isSome) : DefectVertices r c U L :=
  let st := initializationSupportLabels r c U X h
  inverseDefectState r c U L X
    ⟨st.val, (inverseLocalTest_iff_support r c U L hL X st.val).mpr st.property⟩

variable (xs ys : List ℕ)

theorem positiveTraceDefect_nonempty
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) :
    Nonempty (DefectVertices (filteredMargin xs) (filteredMargin ys)
      (positiveTraceCutoff xs ys) 7) := by
  have hg := positiveTraceReference_conditions xs ys hb
  have h := initializationLabelSearch_isSome (filteredMargin xs) (filteredMargin ys)
    (positiveTraceCutoff xs ys) (positiveTraceFallback xs ys htotal)
    (filteredMargin_positive xs) (filteredMargin_positive ys) hg.1 hg.2.1 (by omega)
  exact ⟨initializationDefectStart _ _ _ 7 _ (by decide) h⟩

/-- No actual defect start or feasible fallback is supplied by the caller. -/
def positiveTraceInitialStart
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) :
    DefectVertices (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) 7 :=
  initializationDefectStart _ _ _ 7 (positiveTraceFallback xs ys htotal) (by decide)
    (initializationLabelSearch_isSome _ _ _ _
      (filteredMargin_positive xs) (filteredMargin_positive ys)
      (positiveTraceReference_conditions xs ys hb).1
      (positiveTraceReference_conditions xs ys hb).2.1 (by
        have hg := (positiveTraceReference_conditions xs ys hb).2.2.1
        omega))

def positiveTraceInitializedRetryLaw
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) (h k R : ℕ) :
    RationalLaw (Table (listMargin xs) (listMargin ys)) :=
  positiveTraceCorrectedRetryLaw xs ys hb (positiveTraceInitialStart xs ys htotal hb)
    h k (positiveTraceFallback xs ys htotal) R

/-- The previous reference law now closes initialization from equal totals
and the computed filtered reference tag alone. Precision/retry budgets remain
parameters, and no encoded initialization cost is asserted. -/
theorem positiveTraceInitializedRetry_accuracy
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) (h k R : ℕ) :
    letI := table_nonempty (listMargin xs) (listMargin ys) htotal
    variation (positiveTraceInitializedRetryLaw xs ys htotal hb h k R)
      (uniformLaw (α := Table (listMargin xs) (listMargin ys))) ≤
      (1 - positiveTraceCorrectionSuccess xs ys)^R + (R : ℚ) * (dyadic h + dyadic k) :=
  positiveTraceCorrectedRetry_accuracy xs ys htotal hb
    (positiveTraceInitialStart xs ys htotal hb) h k (positiveTraceFallback xs ys htotal) R

end
end Math115.PhysicalTraceJoin
