/-
SPDX-License-Identifier: Apache-2.0
Local candidate: exact fibers of the upstream designated physical repair.
The labels_unique proof is adapted from OpenAI's SmallDefectLabels at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; all other fiber constructions are local.
-/
import Math115.PhysicalRepairRefinement
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalOriginalResiduals
set_option linter.unusedSectionVars false

namespace Math115.AllSmallRepairFiber
open OAI.ContingencyTables
open SmallGraphProfiles SmallContextCoordinates SmallContextFibres
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions
open scoped BigOperators Classical

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

def viewProfile (small : I → J → Bool) (B X Q : I → J → ℕ) : SmallProfile small :=
  fun a => if a.2 then B a.1.val.1 a.1.val.2 - Q a.1.val.1 a.1.val.2
    else X a.1.val.1 a.1.val.2

lemma viewProfile_row (small : I → J → Bool) (hs : ∀ i j, small i j = true)
    (B X Q : I → J → ℕ) : smallView small (viewProfile small B X Q) false = X := by
  funext i j
  simp [smallView, viewProfile, hs]

lemma viewProfile_q (small : I → J → Bool) (hs : ∀ i j, small i j = true)
    (B X Q : I → J → ℕ) (hQ : ∀ i j, Q i j ≤ B i j) :
    smallQ small B (viewProfile small B X Q) = Q := by
  funext i j
  simp [smallQ, viewProfile, hs, Nat.sub_sub_self (hQ i j)]

lemma profile_columns (small : I → J → Bool) (hs : ∀ i j, small i j = true)
    (B : I → J → ℕ) (z : SmallProfile small) (j : J) :
    smallColumn small B (smallView small z true) j = ∑ i, smallQ small B z i j := by
  simp [smallColumn, smallView, smallQ, hs]

lemma positive_of_margins (small : I → J → Bool) (hs : ∀ i j, small i j = true)
    (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : SmallProfile small) (hb : ∀ a, z a ≤ B a.1.val.1 a.1.val.2)
    (hr : ∀ i, ∑ j, smallView small z false i j = r i)
    (hc : ∀ j, ∑ i, smallQ small B z i j = c j) :
    0 < hardMarginal small B r c L z := by
  have hrows : ∀ i, smallRow small (smallView small z false) i = r i := by
    intro i
    simpa [smallRow, hs] using hr i
  have hcols : ∀ j, smallColumn small B (smallView small z true) j = c j := by
    intro j
    rw [profile_columns small hs B z j]
    exact hc j
  have hres : OriginalResidualsNonnegative small B
      (smallView small z false) (smallView small z true) r c :=
    ⟨fun i => (hrows i).le, fun j => (hcols j).le⟩
  rw [hardMarginal_eq_completionCount small B r c L z hb
    (fun i j h => by rw [hs i j] at h; contradiction), ite_eq_left hres]
  have hR : (fun i => r i - smallRow small (smallView small z false) i +
      rowLargeCount small i * L) = fun _ => 0 := by
    funext i
    simp [hrows, rowLargeCount, hs]
  have hC : (fun j => c j - smallColumn small B (smallView small z true) j +
      columnLargeCount small j * L) = fun _ => 0 := by
    funext j
    simp [hcols, columnLargeCount, hs]
  rw [hR, hC]
  apply Nat.cast_pos.mpr
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨fun _ _ => 0, by constructor <;> simp⟩, by intro i j _; rfl⟩⟩

lemma physical_margins (small : I → J → Bool) (hs : ∀ i j, small i j = true)
    (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PhysicalStates small B r c L) :
    (∀ i, ∑ j, smallView small (physicalProfile small B r c L z) false i j = r i) ∧
    (∀ j, ∑ i, smallQ small B (physicalProfile small B r c L z) i j = c j) := by
  have hcap : ∀ i j, small i j = false →
      (∑ k, residualRows small B r c L z k) ≤ B i j := by
    intro i j h
    rw [hs i j] at h
    contradiction
  obtain ⟨A⟩ := physical_completions_nonempty small B r c L z hcap
  have hz : ∀ i j, A.val.val i j = 0 := fun i j => A.property i j (hs i j)
  have hres := physical_original_residuals small B r c L z hcap
  constructor
  · intro i
    have h := A.val.property.1 i
    simp only [hz, Finset.sum_const_zero] at h
    unfold residualRows at h
    have hh := hres.1 i
    simp [rowLargeCount, smallRow, hs] at h
    simp [smallRow, hs] at hh
    omega
  · intro j
    have h := A.val.property.2 j
    simp only [hz, Finset.sum_const_zero] at h
    unfold residualColumns at h
    simp only [columnLargeCount, hs, ite_true, Finset.sum_const_zero, zero_mul, add_zero] at h
    rw [profile_columns small hs B _ j] at h
    have hh := hres.2 j
    rw [profile_columns small hs B _ j] at hh
    omega

def inverseRow (A : I → J → ℕ) (s t : I × J) : I → J → ℕ :=
  fun i j => (transferInt A (t.1, s.2) t i j).toNat

def inverseQ (A : I → J → ℕ) (s t : I × J) : I → J → ℕ :=
  fun i j => (transferInt A (t.1, s.2) s i j).toNat

lemma inverseRow_cast (A : I → J → ℕ) (s t : I × J)
    (hpos : 0 < A t.1 s.2) (i : I) (j : J) :
    (inverseRow A s t i j : ℤ) = transferInt A (t.1, s.2) t i j :=
  Int.toNat_of_nonneg (transferInt_nonnegative A (t.1,s.2) t hpos i j)

lemma inverseQ_cast (A : I → J → ℕ) (s t : I × J)
    (hpos : 0 < A t.1 s.2) (i : I) (j : J) :
    (inverseQ A s t i j : ℤ) = transferInt A (t.1, s.2) s i j :=
  Int.toNat_of_nonneg (transferInt_nonnegative A (t.1,s.2) s hpos i j)

lemma inverse_defect (A : I → J → ℕ) (s t : I × J) (hne : s ≠ t)
    (hpos : 0 < A t.1 s.2) : IsDefect (inverseRow A s t) (inverseQ A s t) s t := by
  refine ⟨hne, ?_⟩
  intro i j
  rw [inverseQ_cast A s t hpos]
  simp only [transferInt]
  rw [inverseRow_cast A s t hpos]
  simp only [transferInt]
  omega

lemma inverse_repair (A : I → J → ℕ) (s t : I × J) (hne : s ≠ t)
    (hpos : 0 < A t.1 s.2) : repairMatrix (inverseRow A s t) s t = A := by
  funext i j
  apply Int.natCast_inj.mp
  rw [repairMatrix_cast (inverse_defect A s t hne hpos), transferInt,
    inverseRow_cast A s t hpos]
  simp only [transferInt]
  omega

lemma inverse_margins {r : I → ℕ} {c : J → ℕ}
    (A : Table r c) (s t : I × J) (hpos : 0 < A.val t.1 s.2) :
    (∀ i, ∑ j, inverseRow A.val s t i j = r i) ∧
    (∀ j, ∑ i, inverseQ A.val s t i j = c j) := by
  constructor
  · intro i
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [inverseRow_cast A.val s t hpos]
    rw [transferInt_row]
    simp [← Nat.cast_sum, A.property.1]
  · intro j
    apply Int.natCast_inj.mp
    rw [Nat.cast_sum]
    simp_rw [inverseQ_cast A.val s t hpos]
    rw [transferInt_column]
    simp [← Nat.cast_sum, A.property.2]

/- The following uniqueness proof is the upstream SmallDefectLabels proof;
   that module has no cached object in the focused local harness. -/
lemma labels_unique {x q : I → J → ℕ} {s t s' t' : I × J}
    (h : IsDefect x q s t) (h' : IsDefect x q s' t') : s = s' ∧ t = t' := by
  have hst : ¬(s.1 = t.1 ∧ s.2 = t.2) := fun he => h.1 (Prod.ext he.1 he.2)
  have hs := h.2 s.1 s.2
  simp only [transferInt, hst, ite_false, and_self, ite_true, sub_zero] at hs
  have hss : s = s' := by
    by_contra he
    have hss' : ¬(s.1 = s'.1 ∧ s.2 = s'.2) := fun hh => he (Prod.ext hh.1 hh.2)
    have hs' := h'.2 s.1 s.2
    simp only [transferInt, hss', ite_false, add_zero] at hs'
    split_ifs at hs' <;> omega
  subst s'
  refine ⟨rfl, ?_⟩
  by_contra he
  have htt : ¬(t.1 = t'.1 ∧ t.2 = t'.2) := fun hh => he (Prod.ext hh.1 hh.2)
  have hts : ¬(t.1 = s.1 ∧ t.2 = s.2) := fun hh => h.1 (Prod.ext hh.1.symm hh.2.symm)
  have ht := h.2 t.1 t.2
  have ht' := h'.2 t.1 t.2
  simp only [transferInt, htt, hts, ite_false, and_self, ite_true, sub_zero, add_zero] at ht ht'
  omega

lemma repair_cross_positive {x q : I → J → ℕ} {s t : I × J}
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

lemma state_of_views (small : I → J → Bool) (hs : ∀ i j, small i j = true)
    (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (X Q : I → J → ℕ) (hX : ∀ i j, X i j ≤ B i j) (hQ : ∀ i j, Q i j ≤ B i j)
    (hr : ∀ i, ∑ j, X i j = r i) (hc : ∀ j, ∑ i, Q i j = c j)
    (hp : X = Q ∨ ∃ s t, IsDefect X Q s t) :
    ∃ z : PhysicalStates small B r c L,
      smallView small (physicalProfile small B r c L z) false = X ∧
      smallQ small B (physicalProfile small B r c L z) = Q := by
  let v := viewProfile small B X Q
  have hv : ∀ a, v a ≤ B a.1.val.1 a.1.val.2 := by
    rintro ⟨a,b⟩
    cases b
    · exact hX _ _
    · exact Nat.sub_le _ _
  have hvr := viewProfile_row small hs B X Q
  have hvq := viewProfile_q small hs B X Q hQ
  have hpat : Pattern small B v := by
    rcases hp with hp | ⟨s,t,hd⟩
    · left
      intro i j
      rw [hvr, hvq, hp]
    · right
      refine ⟨s,t,hs _ _,hs _ _,?_⟩
      rw [hvr, hvq]
      exact hd
  let z : PhysicalStates small B r c L :=
    ⟨⟨fun a => ⟨v a, Nat.lt_succ_of_le (hv a)⟩, hpat⟩,
      positive_of_margins small hs B r c L v hv
        (by intro i; rw [show smallView small v false = X from hvr]; exact hr i)
        (by intro j; rw [show smallQ small B v = Q from hvq]; exact hc j)⟩
  exact ⟨z, hvr, hvq⟩

/- Exact number of permissible ordered defect labels at a fixed table. -/
abbrev LabelFiber (A : I → J → ℕ) :=
  {st : (I × J) × (I × J) // st.1 ≠ st.2 ∧ 0 < A st.2.1 st.1.2}

abbrev SupportedCell (A : I → J → ℕ) := {v : I × J // 0 < A v.1 v.2}

def labelEquiv (A : I → J → ℕ) :
    LabelFiber A ≃ (v : SupportedCell A) × {w : I × J // w ≠ v.val} where
  toFun st := ⟨⟨(st.val.2.1, st.val.1.2), st.property.2⟩,
    ⟨(st.val.1.1, st.val.2.2), by
      intro he
      have hi := congrArg Prod.fst he
      have hj := congrArg Prod.snd he
      exact st.property.1 (Prod.ext hi hj.symm)⟩⟩
  invFun vw := ⟨((vw.2.val.1, vw.1.val.2), (vw.1.val.1, vw.2.val.2)), by
    refine ⟨?_, vw.1.property⟩
    intro he
    have hi := congrArg Prod.fst he
    have hj := congrArg Prod.snd he
    exact vw.2.property (Prod.ext hi hj.symm)⟩
  left_inv st := by apply Subtype.ext; rfl
  right_inv vw := by cases vw; rfl

lemma labelFiber_card (A : I → J → ℕ) :
    Fintype.card (LabelFiber A) =
      (Fintype.card I * Fintype.card J - 1) * Fintype.card (SupportedCell A) := by
  rw [Fintype.card_congr (labelEquiv A), Fintype.card_sigma]
  have hcard (v : SupportedCell A) : Fintype.card {w : I × J // w ≠ v.val} =
      Fintype.card I * Fintype.card J - 1 := by
    simp [Fintype.card_subtype_compl, Fintype.card_prod]
  simp only [hcard, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  ring

lemma views_injective (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    {z w : PhysicalStates small B r c L}
    (hx : smallView small (physicalProfile small B r c L z) false =
      smallView small (physicalProfile small B r c L w) false)
    (hq : smallQ small B (physicalProfile small B r c L z) =
      smallQ small B (physicalProfile small B r c L w)) : z = w := by
  apply physicalProfile_injective small B r c L
  funext a
  rcases a with ⟨a,b⟩
  have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small) = a :=
    Subtype.ext (Prod.eta a.val)
  cases b
  · have he := congrFun (congrFun hx a.val.1) a.val.2
    simpa only [smallView, a.property, dite_eq_left, heta] using he
  · have hz := naturalProfile_bounded z.val.val (a,true)
    have hw := naturalProfile_bounded w.val.val (a,true)
    have he := congrFun (congrFun hq a.val.1) a.val.2
    simp only [smallQ, a.property, dite_eq_left, heta] at he
    change B a.val.1 a.val.2 - physicalProfile small B r c L z (a,true) =
      B a.val.1 a.val.2 - physicalProfile small B r c L w (a,true) at he
    change physicalProfile small B r c L z (a,true) ≤ B a.val.1 a.val.2 at hz
    change physicalProfile small B r c L w (a,true) ≤ B a.val.1 a.val.2 at hw
    omega

def stateDefect (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : PhysicalStates small B r c L)
    (hb : ¬Balanced small B (physicalProfile small B r c L z)) :
    PositiveDefects small B r c L :=
  ⟨z.val.val, z.val.property.resolve_left hb, z.property⟩

def designatedMatrix (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (z : PhysicalStates small B r c L) : I → J → ℕ :=
  if hb : Balanced small B (physicalProfile small B r c L z) then
    smallView small (physicalProfile small B r c L z) false
  else
    let st := defectLabels small B r c L (stateDefect small B r c L z hb)
    repairMatrix (smallView small (physicalProfile small B r c L z) false) st.1.val st.2.val

lemma designatedMatrix_margins (small : I → J → Bool) (hs : ∀ i j, small i j = true)
    (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PhysicalStates small B r c L) : HasMargins (designatedMatrix small B r c L z) r c := by
  have hm := physical_margins small hs B r c L z
  unfold designatedMatrix
  split_ifs with hb
  · refine ⟨hm.1, ?_⟩
    intro j
    calc
      _ = ∑ i, smallQ small B (physicalProfile small B r c L z) i j :=
        Finset.sum_congr rfl (fun i _ => hb i j)
      _ = c j := hm.2 j
  · exact repairMatrix_margins
      (defectLabels_spec small B r c L (stateDefect small B r c L z hb)) r c hm.1 hm.2

lemma row_entry_bound (X : I → J → ℕ) (r : I → ℕ) (U : ℕ)
    (hr : ∀ i, ∑ j, X i j = r i) (hsmall : ∀ i, r i < U) (i : I) (j : J) : X i j ≤ U := by
  have h := Finset.single_le_sum (f := fun j => X i j)
    (fun j _ => Nat.zero_le (X i j)) (Finset.mem_univ j)
  rw [hr] at h
  exact h.trans (hsmall i).le

lemma column_entry_bound (Q : I → J → ℕ) (c : J → ℕ) (U : ℕ)
    (hc : ∀ j, ∑ i, Q i j = c j) (hsmall : ∀ j, c j < U) (i : I) (j : J) : Q i j ≤ U := by
  have h := Finset.single_le_sum (f := fun i => Q i j)
    (fun i _ => Nat.zero_le (Q i j)) (Finset.mem_univ i)
  rw [hc] at h
  exact h.trans (hsmall j).le

/-- The literal designated matrix with its proved ordinary-table margins. -/
def repairTable (small : I → J → Bool) (hs : ∀ i j, small i j = true)
    (B : I → J → ℕ) (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (z : PhysicalStates small B r c L) : Table r c :=
  ⟨designatedMatrix small B r c L z, designatedMatrix_margins small hs B r c L z⟩

section ActualFiber
variable (small : I → J → Bool) (hs : ∀ i j, small i j = true)
variable (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
variable (hrU : ∀ i, r i < U) (hcU : ∀ j, c j < U)
local notation "B" => (fun (_ : I) (_ : J) => U)

def balancedState (A : Table r c) : PhysicalStates small B r c L :=
  Classical.choose (state_of_views small hs B r c L A.val A.val
    (row_entry_bound A.val r U A.property.1 hrU)
    (column_entry_bound A.val c U A.property.2 hcU)
    A.property.1 A.property.2 (Or.inl rfl))

lemma balancedState_views (A : Table r c) :
    smallView small (physicalProfile small B r c L (balancedState small hs r c U L hrU hcU A)) false = A.val ∧
    smallQ small B (physicalProfile small B r c L (balancedState small hs r c U L hrU hcU A)) = A.val :=
  Classical.choose_spec (state_of_views small hs B r c L A.val A.val
    (row_entry_bound A.val r U A.property.1 hrU)
    (column_entry_bound A.val c U A.property.2 hcU)
    A.property.1 A.property.2 (Or.inl rfl))

def inverseState (A : Table r c) (st : LabelFiber A.val) : PhysicalStates small B r c L :=
  let hm := inverse_margins A st.val.1 st.val.2 st.property.2
  Classical.choose (state_of_views small hs B r c L
    (inverseRow A.val st.val.1 st.val.2) (inverseQ A.val st.val.1 st.val.2)
    (row_entry_bound _ r U hm.1 hrU) (column_entry_bound _ c U hm.2 hcU)
    hm.1 hm.2 (Or.inr ⟨st.val.1, st.val.2,
      inverse_defect A.val st.val.1 st.val.2 st.property.1 st.property.2⟩))

lemma inverseState_views (A : Table r c) (st : LabelFiber A.val) :
    smallView small (physicalProfile small B r c L (inverseState small hs r c U L hrU hcU A st)) false =
      inverseRow A.val st.val.1 st.val.2 ∧
    smallQ small B (physicalProfile small B r c L (inverseState small hs r c U L hrU hcU A st)) =
      inverseQ A.val st.val.1 st.val.2 := by
  exact Classical.choose_spec (state_of_views small hs B r c L
    (inverseRow A.val st.val.1 st.val.2) (inverseQ A.val st.val.1 st.val.2)
    (row_entry_bound _ r U (inverse_margins A st.val.1 st.val.2 st.property.2).1 hrU)
    (column_entry_bound _ c U (inverse_margins A st.val.1 st.val.2 st.property.2).2 hcU)
    (inverse_margins A st.val.1 st.val.2 st.property.2).1
    (inverse_margins A st.val.1 st.val.2 st.property.2).2
    (Or.inr ⟨st.val.1, st.val.2, inverse_defect A.val st.val.1 st.val.2 st.property.1 st.property.2⟩))

lemma balancedState_balanced (A : Table r c) :
    Balanced small B (physicalProfile small B r c L (balancedState small hs r c U L hrU hcU A)) := by
  intro i j
  rw [(balancedState_views small hs r c U L hrU hcU A).1,
    (balancedState_views small hs r c U L hrU hcU A).2]

lemma inverseState_defect (A : Table r c) (st : LabelFiber A.val) :
    IsDefect
      (smallView small (physicalProfile small B r c L (inverseState small hs r c U L hrU hcU A st)) false)
      (smallQ small B (physicalProfile small B r c L (inverseState small hs r c U L hrU hcU A st)))
      st.val.1 st.val.2 := by
  rw [(inverseState_views small hs r c U L hrU hcU A st).1,
    (inverseState_views small hs r c U L hrU hcU A st).2]
  exact inverse_defect A.val st.val.1 st.val.2 st.property.1 st.property.2

lemma inverseState_not_balanced (A : Table r c) (st : LabelFiber A.val) :
    ¬Balanced small B (physicalProfile small B r c L (inverseState small hs r c U L hrU hcU A st)) := by
  intro hb
  exact balanced_not_defect small B _ hb
    ⟨st.val.1, st.val.2, hs _ _, hs _ _, inverseState_defect small hs r c U L hrU hcU A st⟩

lemma balancedState_repair (A : Table r c) :
    designatedMatrix small B r c L (balancedState small hs r c U L hrU hcU A) = A.val := by
  rw [designatedMatrix, dite_eq_left (balancedState_balanced small hs r c U L hrU hcU A)]
  exact (balancedState_views small hs r c U L hrU hcU A).1

lemma inverseState_repair (A : Table r c) (st : LabelFiber A.val) :
    designatedMatrix small B r c L (inverseState small hs r c U L hrU hcU A st) = A.val := by
  rw [designatedMatrix, dite_eq_right (inverseState_not_balanced small hs r c U L hrU hcU A st)]
  have hl := labels_unique
    (defectLabels_spec small B r c L (stateDefect small B r c L _
      (inverseState_not_balanced small hs r c U L hrU hcU A st)))
    (inverseState_defect small hs r c U L hrU hcU A st)
  dsimp only at hl ⊢
  rw [hl.1, hl.2, (inverseState_views small hs r c U L hrU hcU A st).1]
  exact inverse_repair A.val st.val.1 st.val.2 st.property.1 st.property.2

abbrev RepairFiber (A : Table r c) :=
  {z : PhysicalStates small B r c L // designatedMatrix small B r c L z = A.val}

def fiberState (A : Table r c) : Unit ⊕ LabelFiber A.val → RepairFiber small r c U L A
  | .inl _ => ⟨balancedState small hs r c U L hrU hcU A,
      balancedState_repair small hs r c U L hrU hcU A⟩
  | .inr st => ⟨inverseState small hs r c U L hrU hcU A st,
      inverseState_repair small hs r c U L hrU hcU A st⟩

lemma fiberState_injective (A : Table r c) :
    Function.Injective (fiberState small hs r c U L hrU hcU A) := by
  intro a b he
  have hev := congrArg Subtype.val he
  cases a with
  | inl a =>
    cases b with
    | inl b => cases a; cases b; rfl
    | inr b =>
      have hb := balancedState_balanced small hs r c U L hrU hcU A
      change balancedState small hs r c U L hrU hcU A =
        inverseState small hs r c U L hrU hcU A b at hev
      rw [hev] at hb
      exact False.elim (inverseState_not_balanced small hs r c U L hrU hcU A b hb)
  | inr a =>
    cases b with
    | inl b =>
      have hb := balancedState_balanced small hs r c U L hrU hcU A
      change inverseState small hs r c U L hrU hcU A a =
        balancedState small hs r c U L hrU hcU A at hev
      rw [←hev] at hb
      exact False.elim (inverseState_not_balanced small hs r c U L hrU hcU A a hb)
    | inr b =>
      change inverseState small hs r c U L hrU hcU A a =
        inverseState small hs r c U L hrU hcU A b at hev
      have ha := inverseState_defect small hs r c U L hrU hcU A a
      rw [hev] at ha
      have hl := labels_unique ha (inverseState_defect small hs r c U L hrU hcU A b)
      exact congrArg Sum.inr (Subtype.ext (Prod.ext hl.1 hl.2))

lemma fiberState_surjective (A : Table r c) :
    Function.Surjective (fiberState small hs r c U L hrU hcU A) := by
  intro z
  by_cases hb : Balanced small B (physicalProfile small B r c L z.val)
  · refine ⟨.inl (), ?_⟩
    apply Subtype.ext
    have hx : smallView small (physicalProfile small B r c L z.val) false = A.val := by
      simpa only [designatedMatrix, dite_eq_left hb] using z.property
    have hq : smallQ small B (physicalProfile small B r c L z.val) = A.val := by
      funext i j
      rw [←hb i j, hx]
    apply views_injective small B r c L
    · exact (balancedState_views small hs r c U L hrU hcU A).1.trans hx.symm
    · exact (balancedState_views small hs r c U L hrU hcU A).2.trans hq.symm
  · let d := stateDefect small B r c L z.val hb
    let st := defectLabels small B r c L d
    have hd := defectLabels_spec small B r c L d
    have he : repairMatrix (smallView small (physicalProfile small B r c L z.val) false)
        st.1.val st.2.val = A.val := by
      simpa only [designatedMatrix, dite_eq_right hb] using z.property
    have hp : 0 < A.val st.2.val.1 st.1.val.2 := by
      rw [←he]
      exact repair_cross_positive hd
    let a : LabelFiber A.val := ⟨(st.1.val,st.2.val), hd.1, hp⟩
    refine ⟨.inr a, ?_⟩
    apply Subtype.ext
    have hxy := repairMatrix_injective hd
      (inverse_defect A.val st.1.val st.2.val hd.1 hp)
      (he.trans (inverse_repair A.val st.1.val st.2.val hd.1 hp).symm)
    apply views_injective small B r c L
    · exact (inverseState_views small hs r c U L hrU hcU A a).1.trans hxy.1.symm
    · exact (inverseState_views small hs r c U L hrU hcU A a).2.trans hxy.2.symm

def repairFiberEquiv (A : Table r c) :
    (Unit ⊕ LabelFiber A.val) ≃ RepairFiber small r c U L A :=
  Equiv.ofBijective (fiberState small hs r c U L hrU hcU A)
    ⟨fiberState_injective small hs r c U L hrU hcU A,
      fiberState_surjective small hs r c U L hrU hcU A⟩

include hs hrU hcU in
/-- Cardinality of an actual physical repair fiber, with no assumed fiber count.
The proof constructs both inverse views and checks positive hard marginal weight. -/
theorem physical_repair_fiber_card (A : Table r c) :
    Fintype.card (RepairFiber small r c U L A) =
      1 + (Fintype.card I * Fintype.card J - 1) * Fintype.card (SupportedCell A.val) := by
  rw [← Fintype.card_congr (repairFiberEquiv small hs r c U L hrU hcU A),
    Fintype.card_sum, Fintype.card_unique, labelFiber_card]

include hrU hcU in
/-- Table-valued map version for direct use by a generic output kernel. -/
theorem repairTable_fiber_card (A : Table r c) :
    Fintype.card {z : PhysicalStates small B r c L // repairTable small hs B r c L z = A} =
      1 + (Fintype.card I * Fintype.card J - 1) * Fintype.card (SupportedCell A.val) := by
  let e : {z : PhysicalStates small B r c L // repairTable small hs B r c L z = A} ≃
      RepairFiber small r c U L A :=
    Equiv.subtypeEquivRight (fun z => Subtype.ext_iff)
  rw [Fintype.card_congr e]
  exact physical_repair_fiber_card small hs r c U L hrU hcU A

abbrev DefectRepairFiber (A : Table r c) :=
  {z : RepairFiber small r c U L A // ¬Balanced small B (physicalProfile small B r c L z.val)}

def defectFiberState (A : Table r c) (st : LabelFiber A.val) :
    DefectRepairFiber small r c U L A :=
  ⟨⟨inverseState small hs r c U L hrU hcU A st,
    inverseState_repair small hs r c U L hrU hcU A st⟩,
    inverseState_not_balanced small hs r c U L hrU hcU A st⟩

lemma defectFiberState_bijective (A : Table r c) :
    Function.Bijective (defectFiberState small hs r c U L hrU hcU A) := by
  constructor
  · intro a b he
    apply Sum.inr.inj
    apply fiberState_injective small hs r c U L hrU hcU A
    apply Subtype.ext
    exact congrArg (fun z => z.val.val) he
  · intro z
    obtain ⟨a,ha⟩ := fiberState_surjective small hs r c U L hrU hcU A z.val
    cases a with
    | inl a =>
      have hb := balancedState_balanced small hs r c U L hrU hcU A
      have he := congrArg Subtype.val ha
      change balancedState small hs r c U L hrU hcU A = z.val.val at he
      rw [he] at hb
      exact False.elim (z.property hb)
    | inr a =>
      refine ⟨a, ?_⟩
      apply Subtype.ext
      exact ha

include hs hrU hcU in
/-- The exact defect-only fiber count is available separately. -/
theorem physical_defect_repair_fiber_card (A : Table r c) :
    Fintype.card (DefectRepairFiber small r c U L A) =
      (Fintype.card I * Fintype.card J - 1) * Fintype.card (SupportedCell A.val) := by
  rw [← Fintype.card_congr (Equiv.ofBijective
    (defectFiberState small hs r c U L hrU hcU A)
    (defectFiberState_bijective small hs r c U L hrU hcU A))]
  exact labelFiber_card A.val

end ActualFiber

lemma firstPaperSmall_all (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (hrU : ∀ i, r i < U) (_hcU : ∀ j, c j < U) :
    ∀ i j, firstPaperSmall r c U i j = true := by
  intro i j
  simp [firstPaperSmall, hrU i]

/-- The count applies to the exact state type of the existing reduced chain. -/
theorem reduced_physical_repair_fiber_card (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hrU : ∀ i, r i < U) (hcU : ∀ j, c j < U) (A : Table r c) :
    Fintype.card {z : Math115.ReducedSmallChain.States r c U L //
      designatedMatrix (firstPaperSmall r c U) (Math115.ReducedSmallChain.capacity r c U L)
        r c L z = A.val} =
      1 + (Fintype.card I * Fintype.card J - 1) * Fintype.card (SupportedCell A.val) := by
  have hs := firstPaperSmall_all r c U hrU hcU
  have hB : Math115.ReducedSmallChain.capacity r c U L = fun _ _ => U := by
    funext i j
    exact Math115.ReducedSmallChain.capacity_small r c U L i j (hs i j)
  have hg (B' : I → J → ℕ) (hB' : B' = fun _ _ => U) :
      Fintype.card {z : PhysicalStates (firstPaperSmall r c U) B' r c L //
        designatedMatrix (firstPaperSmall r c U) B' r c L z = A.val} =
        1 + (Fintype.card I * Fintype.card J - 1) * Fintype.card (SupportedCell A.val) := by
    subst B'
    exact physical_repair_fiber_card (firstPaperSmall r c U) hs r c U L hrU hcU A
  exact hg _ hB

/-- Actual ordinary-table repair on the existing reduced physical state space. -/
def reducedRepairTable (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hrU : ∀ i, r i < U) (hcU : ∀ j, c j < U) :
    Math115.ReducedSmallChain.States r c U L → Table r c :=
  repairTable (firstPaperSmall r c U) (firstPaperSmall_all r c U hrU hcU)
    (Math115.ReducedSmallChain.capacity r c U L) r c L

/-- This equality instantiates a generic `fibreSize repair A` definition directly. -/
theorem reduced_repairTable_fiber_card (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hrU : ∀ i, r i < U) (hcU : ∀ j, c j < U) (A : Table r c) :
    Fintype.card {z : Math115.ReducedSmallChain.States r c U L //
      reducedRepairTable r c U L hrU hcU z = A} =
      1 + (Fintype.card I * Fintype.card J - 1) * Fintype.card (SupportedCell A.val) := by
  let e : {z : Math115.ReducedSmallChain.States r c U L // reducedRepairTable r c U L hrU hcU z = A} ≃
      {z : Math115.ReducedSmallChain.States r c U L //
        designatedMatrix (firstPaperSmall r c U) (Math115.ReducedSmallChain.capacity r c U L)
          r c L z = A.val} :=
    Equiv.subtypeEquivRight (fun z => Subtype.ext_iff)
  rw [Fintype.card_congr e]
  exact reduced_physical_repair_fiber_card r c U L hrU hcU A

lemma designatedMatrix_repairWord (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (B : I → J → ℕ) (hB : ∀ i j, firstPaperSmall r c U i j = true → B i j = U)
    (hs : ∀ i j, firstPaperSmall r c U i j = true)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hb : ¬Balanced (firstPaperSmall r c U) B (physicalProfile _ B r c L z)) :
    designatedMatrix (firstPaperSmall r c U) B r c L z =
      smallView (firstPaperSmall r c U)
        (SmallContextEnumeration.rawChoice (firstPaperSmall r c U) U
          (RowMajorEnumeration.wordChoices (firstPaperSmall r c U) U
            (repairWord r c U L B hB (stateDefect _ B r c L z hb)))) false := by
  rw [repairWord_profile]
  funext i j
  rw [designatedMatrix, dite_eq_right hb]
  simp only [smallView, hs i j, dite_eq_left, repairedProfile, Bool.false_eq_true, ite_false]
  rfl

end
end Math115.AllSmallRepairFiber

