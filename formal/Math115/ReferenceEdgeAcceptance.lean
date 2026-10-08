/-
SPDX-License-Identifier: Apache-2.0

Half acceptance for the actual source Accepted and reference completion maps,
with a free padding parameter. No bounded-cell or weighted extension is used.
-/
import Math115.SmallEntryTail
import Math115.PaddedMarginBridge
import Math115.CompletionAdjustment
import OAI.Combinatorics.ContingencyTables.Transport.TranslatedCompletionCounts
import OAI.Combinatorics.ContingencyTables.Transport.ReferenceCompletionBounds
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalEdgeMargins

namespace Math115.ReferenceEdgeAcceptance

open OAI.ContingencyTables
open OAI.ContingencyTables.CompletionTranslation
open Math115.CompletionAdjustment
open scoped BigOperators Classical

set_option maxHeartbeats 800000

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The zero-entry estimate, including `L=0`. The latter is the elementary
subtype count bound, so applying the threshold-one theorem never requires
an invalid `1 ≤ 0` premise. -/
theorem zero_entry_count (R : Option I → ℕ) (P : Option J → ℕ)
    (i : Option I) (j : Option J) (L : ℕ)
    (hr : L ≤ R i) (hp : L ≤ P j) :
    Fintype.card {X : Table R P // X.val i j = 0} *
        (L + Fintype.card I * Fintype.card J) ≤
      Fintype.card (Table R P) * (Fintype.card I * Fintype.card J) := by
  classical
  by_cases hL : L = 0
  · subst L
    simpa only [zero_add] using Nat.mul_le_mul_right
      (Fintype.card I * Fintype.card J)
      (Fintype.card_subtype_le (fun X : Table R P => X.val i j = 0))
  · have h := SmallEntryTail.all_donor_small_entry_count_strong i j L 1 hr hp
      (by omega)
    simpa only [Fintype.card_option, Nat.add_sub_cancel, Nat.lt_one_iff,
      one_mul] using h

/-- Rejected source tables are exactly the zero-entry union in the negative
unit cells of the actual signed translation. This is a predicate equivalence,
not an assumed count inequality. -/
theorem rejected_card_eq_zero_union (R : Option I → ℕ) (P : Option J → ℕ)
    (D : Option I → Option J → ℤ) (hD : Bounds D) :
    Fintype.card {X : Table R P // ¬ ∀ i j, 0 ≤ (X.val i j : ℤ) + D i j} =
      Fintype.card {X : Table R P // ∃ p : negative D, X.val p.val.1 p.val.2 = 0} := by
  classical
  apply Fintype.card_congr
  apply Equiv.subtypeEquivRight
  intro X
  rw [translation_rejection_iff hD X.val]
  constructor
  · rintro ⟨p, hp, hz⟩
    exact ⟨⟨p, hp⟩, hz⟩
  · rintro ⟨p, hz⟩
    exact ⟨p.val, p.property, hz⟩

/-- All-donor zero-entry counting and a finite union bound apply directly to
the rejected part of the source Accepted predicate. Only incident margins of
negative adjustment cells need the lower bound. -/
theorem rejected_count (R : Option I → ℕ) (P : Option J → ℕ)
    (D : Option I → Option J → ℤ) (hD : Bounds D) (L : ℕ)
    (hr : ∀ p ∈ negative D, L ≤ R p.1)
    (hp : ∀ p ∈ negative D, L ≤ P p.2) :
    Fintype.card {X : Table R P // ¬ ∀ i j, 0 ≤ (X.val i j : ℤ) + D i j} *
        (L + Fintype.card I * Fintype.card J) ≤
      Fintype.card (Table R P) *
        ((negative D).card * (Fintype.card I * Fintype.card J)) := by
  classical
  rw [rejected_card_eq_zero_union R P D hD]
  let event := fun (p : negative D) (X : Table R P) => X.val p.val.1 p.val.2 = 0
  have hlocal (p : negative D) :
      Fintype.card {X : Table R P // event p X} *
          (L + Fintype.card I * Fintype.card J) ≤
        Fintype.card (Table R P) * (Fintype.card I * Fintype.card J) :=
    zero_entry_count R P p.val.1 p.val.2 L (hr p.val p.property) (hp p.val p.property)
  have h := PaddedMarginBridge.union_count_mul_bound event
    (L + Fintype.card I * Fintype.card J) (Fintype.card I * Fintype.card J)
    (fun p => by simpa only [Fintype.card_eq_nat_card] using hlocal p)
  simpa only [event, Fintype.card_eq_nat_card, Nat.card_eq_finsetCard] using h

theorem rejected_count_le_two (R : Option I → ℕ) (P : Option J → ℕ)
    (D : Option I → Option J → ℤ) (hD : Bounds D) (L : ℕ)
    (hr : ∀ p ∈ negative D, L ≤ R p.1)
    (hp : ∀ p ∈ negative D, L ≤ P p.2) :
    Fintype.card {X : Table R P // ¬ ∀ i j, 0 ≤ (X.val i j : ℤ) + D i j} *
        (L + Fintype.card I * Fintype.card J) ≤
      Fintype.card (Table R P) * (2 * (Fintype.card I * Fintype.card J)) := by
  exact (rejected_count R P D hD L hr hp).trans
    (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hD.negative_card))

/-- Count partition into the actual source Accepted subtype and its complement.
It also holds for an empty fiber or unequal total margins. -/
theorem rejected_add_accepted (R : Option I → ℕ) (P : Option J → ℕ)
    (D : Option I → Option J → ℤ) :
    Fintype.card {X : Table R P // ¬ ∀ i j, 0 ≤ (X.val i j : ℤ) + D i j} +
      Fintype.card (Accepted R P D) = Fintype.card (Table R P) := by
  classical
  change Fintype.card {X : Table R P // ¬ ∀ i j, 0 ≤ (X.val i j : ℤ) + D i j} +
    Fintype.card {X : Table R P // ∀ i j, 0 ≤ (X.val i j : ℤ) + D i j} = _
  rw [Fintype.card_subtype_compl]
  exact Nat.sub_add_cancel (Fintype.card_subtype_le _)

/-- Actual uniform-source rejection probability. A positive denominator is
stated explicitly; the zero-donor, zero-padding between-map case is treated
by a deterministic translation equivalence below. -/
theorem rejection_probability_le (R : Option I → ℕ) (P : Option J → ℕ)
    (D : Option I → Option J → ℤ) (hD : Bounds D) (L : ℕ)
    (htotal : (∑ i, R i) = ∑ j, P j)
    (hden : 0 < L + Fintype.card I * Fintype.card J)
    (hr : ∀ p ∈ negative D, L ≤ R p.1)
    (hp : ∀ p ∈ negative D, L ≤ P p.2) :
    (Fintype.card {X : Table R P // ¬ ∀ i j, 0 ≤ (X.val i j : ℤ) + D i j} : ℝ) /
        Fintype.card (Table R P) ≤
      2 * (Fintype.card I * Fintype.card J : ℕ) /
        ((L : ℝ) + (Fintype.card I * Fintype.card J : ℕ)) := by
  classical
  have hcard : (0 : ℝ) < Fintype.card (Table R P) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (table_nonempty R P htotal)
  have hdenR : (0 : ℝ) < (L : ℝ) + (Fintype.card I * Fintype.card J : ℕ) := by
    exact_mod_cast hden
  have h := rejected_count_le_two R P D hD L hr hp
  have hR :
      (Fintype.card {X : Table R P // ¬ ∀ i j, 0 ≤ (X.val i j : ℤ) + D i j} : ℝ) *
          ((L : ℝ) + (Fintype.card I * Fintype.card J : ℕ)) ≤
        (Fintype.card (Table R P) : ℝ) * (2 * (Fintype.card I * Fintype.card J : ℕ)) := by
    exact_mod_cast h
  apply (div_le_div_iff₀ hcard hdenR).mpr
  simpa only [mul_comm] using hR

/-- At `L ≥ 3e`, at least half the actual source tables accept. This natural
count statement does not require a nonempty fiber or equal total margins. -/
theorem accepted_half_count (R : Option I → ℕ) (P : Option J → ℕ)
    (D : Option I → Option J → ℤ) (hD : Bounds D) (L : ℕ)
    (hden : 0 < L + Fintype.card I * Fintype.card J)
    (hscale : 3 * (Fintype.card I * Fintype.card J) ≤ L)
    (hr : ∀ p ∈ negative D, L ≤ R p.1)
    (hp : ∀ p ∈ negative D, L ≤ P p.2) :
    Fintype.card (Table R P) ≤ 2 * Fintype.card (Accepted R P D) := by
  classical
  let e := Fintype.card I * Fintype.card J
  let bad := Fintype.card {X : Table R P // ¬ ∀ i j, 0 ≤ (X.val i j : ℤ) + D i j}
  let total := Fintype.card (Table R P)
  have hcount : bad * (L + e) ≤ total * (2 * e) := rejected_count_le_two R P D hD L hr hp
  have hscale' : 4 * e ≤ L + e := by dsimp only [e]; omega
  have hdouble : (2 * bad) * (L + e) ≤ total * (L + e) := by
    calc
      _ = 2 * (bad * (L + e)) := by ring
      _ ≤ 2 * (total * (2 * e)) := Nat.mul_le_mul_left 2 hcount
      _ = total * (4 * e) := by ring
      _ ≤ _ := Nat.mul_le_mul_left total hscale'
  have hbad : 2 * bad ≤ total := Nat.le_of_mul_le_mul_right hdouble hden
  have hpartition := rejected_add_accepted R P D
  change bad + Fintype.card (Accepted R P D) = total at hpartition
  omega

/-- Specialize the source's literal translate/backward bijection to its
reference-star between map. Each accepted table is translated cellwise. -/
def betweenAcceptedEquiv (R₀ R₁ : Option I → ℕ) (P₀ P₁ : Option J → ℕ)
    (h₀ : (∑ i, R₀ i) = ∑ j, P₀ j) (h₁ : (∑ i, R₁ i) = ∑ j, P₁ j) :
    Accepted R₀ P₀ (between R₀ R₁ P₀ P₁) ≃
      Accepted R₁ P₁ (fun i j => -between R₀ R₁ P₀ P₁ i j) :=
  acceptedEquiv R₀ R₁ P₀ P₁ (between R₀ R₁ P₀ P₁)
    (between_rows R₀ R₁ P₀ P₁) (between_columns R₀ R₁ P₀ P₁ h₀ h₁)

/-- A singleton completion row or column has no rejection for a between map
to a feasible target, including zero padding and zero total. -/
theorem singleton_between_accepted_card (R₀ R₁ : Option I → ℕ) (P₀ P₁ : Option J → ℕ)
    (hs : IsEmpty I ∨ IsEmpty J) (h₁ : (∑ i, R₁ i) = ∑ j, P₁ j) :
    Fintype.card (Accepted R₀ P₀ (between R₀ R₁ P₀ P₁)) = Fintype.card (Table R₀ P₀) := by
  classical
  obtain ⟨Y⟩ := table_nonempty R₁ P₁ h₁
  let e : Table R₀ P₀ ≃ Accepted R₀ P₀ (between R₀ R₁ P₀ P₁) :=
    { toFun := fun X => ⟨X, singleton_translation_nonnegative hs X Y⟩
      invFun := Subtype.val
      left_inv := fun _ => rfl
      right_inv := fun _ => Subtype.ext rfl }
  exact (Fintype.card_congr e).symm

/-- The actual between map allows `L ≥ 3e` without an extra positivity
premise: when `L=e=0`, use the singleton-block translation, not division by zero. -/
theorem between_accepted_half_count (R₀ R₁ : Option I → ℕ) (P₀ P₁ : Option J → ℕ)
    (h₁ : (∑ i, R₁ i) = ∑ j, P₁ j)
    (hD : Bounds (between R₀ R₁ P₀ P₁)) (L : ℕ)
    (hscale : 3 * (Fintype.card I * Fintype.card J) ≤ L)
    (hr : ∀ p ∈ negative (between R₀ R₁ P₀ P₁), L ≤ R₀ p.1)
    (hp : ∀ p ∈ negative (between R₀ R₁ P₀ P₁), L ≤ P₀ p.2) :
    Fintype.card (Table R₀ P₀) ≤
      2 * Fintype.card (Accepted R₀ P₀ (between R₀ R₁ P₀ P₁)) := by
  classical
  by_cases hden : 0 < L + Fintype.card I * Fintype.card J
  · exact accepted_half_count R₀ P₀ _ hD L hden hscale hr hp
  · have he : Fintype.card I * Fintype.card J = 0 := by omega
    have hs : IsEmpty I ∨ IsEmpty J := by
      rcases Nat.mul_eq_zero.mp he with hi | hj
      · exact Or.inl (Fintype.card_eq_zero_iff.mp hi)
      · exact Or.inr (Fintype.card_eq_zero_iff.mp hj)
    rw [singleton_between_accepted_card R₀ R₁ P₀ P₁ hs h₁]
    omega

end Math115.ReferenceEdgeAcceptance

namespace Math115.ReferenceEdgeAcceptance

open OAI.ContingencyTables
open OAI.ContingencyTables.CompletionTranslation
open OAI.ContingencyTables.SmallGraphProfiles
open OAI.ContingencyTables.PhysicalCompletionFibres
open OAI.ContingencyTables.FirstPaperProfiles
open OAI.ContingencyTables.FirstPaperPhysicalMarginal
open OAI.ContingencyTables.CompletionCounts
open OAI.ContingencyTables.PaddedCompletions
open OAI.ContingencyTables.SmallContextFibres
open OAI.ContingencyTables.SmallContextCoordinates
open OAI.ContingencyTables.SmallContextEnumeration
open OAI.ContingencyTables.RowMajorEnumeration
open Math115.CompletionAdjustment
open scoped BigOperators Classical

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Recover the actual designated repair's labels and literal repaired profile
before invoking the exact three-cell adjustment theorem. -/
theorem designated_repair_adjustment_bounds (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (B : I → J → ℕ) (hB : ∀ i j, firstPaperSmall r c U i j = true → B i j = U)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hxcap : ∀ i j, firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L x k) ≤ B i j)
    (hycap : ∀ i j, firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L y k) ≤ B i j)
    (z : PositiveDefects (firstPaperSmall r c U) B r c L)
    (hsource : naturalProfile z.val = physicalProfile _ B r c L x)
    (htarget : rawChoice (firstPaperSmall r c U) U
      (wordChoices _ U (repairWord r c U L B hB z)) = physicalProfile _ B r c L y) :
    Bounds (between (referenceRows r c U L B i₀ x) (referenceRows r c U L B i₀ y)
      (referenceColumns r c U L B j₀ x) (referenceColumns r c U L B j₀ y)) ∧
    Bounds (between (referenceRows r c U L B i₀ y) (referenceRows r c U L B i₀ x)
      (referenceColumns r c U L B j₀ y) (referenceColumns r c U L B j₀ x)) := by
  let st := defectLabels (firstPaperSmall r c U) B r c L z
  have hd := defectLabels_spec (firstPaperSmall r c U) B r c L z
  have hcap := repair_small_capacity r c U L B hB (naturalProfile z.val)
    (naturalProfile_bounded z.val) st.1.val st.2.val st.1.property st.2.property hd z.property.2
  have he := htarget.symm.trans (repairWord_profile r c U L B hB z)
  rw [hsource] at hd hcap he
  constructor
  · exact repair_reference_adjustment_bounds r c U L B i₀ j₀ x y hxcap hycap
      st.1.val st.2.val hd st.2.property hcap he
  · exact repair_reverse_reference_adjustment_bounds r c U L B i₀ j₀ x y hxcap hycap
      st.1.val st.2.val hd st.2.property hcap he

/-- The actual physical graph's exchange, repair, and reverse-repair branches
all satisfy the exact signed-cell bounds. No abstract edge-count hypothesis
replaces the source graph predicate. -/
theorem physical_reference_adjustment_bounds (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (B : I → J → ℕ) (hB : ∀ i j, firstPaperSmall r c U i j = true → B i j = U)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (hcap : ∀ z : PhysicalStates (firstPaperSmall r c U) B r c L, ∀ i j,
      firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hxy : physicalAdjacent r c U L B hB x y) :
    Bounds (between (referenceRows r c U L B i₀ x) (referenceRows r c U L B i₀ y)
      (referenceColumns r c U L B j₀ x) (referenceColumns r c U L B j₀ y)) := by
  rcases Finset.mem_union.mp hxy with he | he
  · exact exchange_reference_adjustment_bounds r c U L B i₀ j₀ x y
      (hcap x) (hcap y) (Finset.mem_filter.mp he).2
  · rcases Finset.mem_union.mp he with he | he
    · obtain ⟨z, _, he⟩ := Finset.mem_image.mp he
      exact (designated_repair_adjustment_bounds r c U L B hB i₀ j₀ x y
        (hcap x) (hcap y) z (congrArg Prod.fst he) (congrArg Prod.snd he)).1
    · obtain ⟨z, _, he⟩ := Finset.mem_image.mp he
      exact (designated_repair_adjustment_bounds r c U L B hB i₀ j₀ y x
        (hcap y) (hcap x) z (congrArg Prod.snd he) (congrArg Prod.fst he)).2

/-- A replacement for the source reference_edge_acceptance with arbitrary
padding `L`: the actual shape-aware sufficient condition is `L ≥ 3e`.
The ordinary reference block is identified through the source cap premises;
this does not assert acceptance for an arbitrary capped or weighted fiber. -/
theorem reference_edge_acceptance_reduced (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (B : I → J → ℕ) (hB : ∀ i j, firstPaperSmall r c U i j = true → B i j = U)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (hscale : 3 * (Fintype.card {i : LargeRows r U // i ≠ i₀} *
      Fintype.card {j : LargeColumns c U // j ≠ j₀}) ≤ L)
    (hcap : ∀ z : PhysicalStates (firstPaperSmall r c U) B r c L, ∀ i j,
      firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hxy : physicalAdjacent r c U L B hB x y) :
    (blockCount (referenceRows r c U L B i₀) (referenceColumns r c U L B j₀) x : ℝ) / 2 ≤
      acceptedCount (referenceRows r c U L B i₀) (referenceColumns r c U L B j₀) x y := by
  have hD := physical_reference_adjustment_bounds r c U L B hB i₀ j₀ hcap x y hxy
  have h := between_accepted_half_count
    (referenceRows r c U L B i₀ x) (referenceRows r c U L B i₀ y)
    (referenceColumns r c U L B j₀ x) (referenceColumns r c U L B j₀ y)
    (reference_totals r c U L B i₀ j₀ y (hcap y)) hD L hscale
    (fun p _ => reference_row_padding r c U L B i₀ j₀ x p.1)
    (fun p _ => reference_column_padding r c U L B i₀ j₀ x p.2)
  have hR : (blockCount (referenceRows r c U L B i₀) (referenceColumns r c U L B j₀) x : ℝ) ≤
      2 * acceptedCount (referenceRows r c U L B i₀) (referenceColumns r c U L B j₀) x y := by
    exact_mod_cast h
  linarith

end Math115.ReferenceEdgeAcceptance
