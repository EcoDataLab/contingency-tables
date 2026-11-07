import Research.ReciprocalZero
import Research.AcceptancePadding

namespace Research.ReciprocalZeroPhysical

open OAI.ContingencyTables OAI.ContingencyTables.CompletionTranslation
open Math115.CompletionAdjustment Math115.ReferenceEdgeAcceptance
open Research.ReciprocalZero Research.WeightedIncidence

set_option maxHeartbeats 800000
open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J]

theorem zero_count_floor (r : I → ℕ) (c : J → ℕ) (a : I) (s : J) (L : ℕ)
    (hI : 2 ≤ Fintype.card I) (hJ : 2 ≤ Fintype.card J)
    (htotal : (∑ i, r i) = ∑ j, c j)
    (hr : Fintype.card J * L ≤ r a) (hc : Fintype.card I * L ≤ c s) :
    Fintype.card {X : Table r c // X.val a s = 0} * (L + 1) ≤
      Fintype.card (Table r c) * 2 := by
  classical
  have hsharp := zero_entry_probability_reciprocal r c a s hI hJ htotal
  have hcard : (0 : ℝ) < Fintype.card (Table r c) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (table_nonempty r c htotal)
  have hdenJ : (0 : ℝ) < (r a : ℝ) + (Fintype.card J - 1 : ℕ) := by
    have h : 0 < Fintype.card J - 1 := by omega
    have h' : (0 : ℝ) < (Fintype.card J - 1 : ℕ) := by exact_mod_cast h
    have h'' : (0 : ℝ) ≤ r a := Nat.cast_nonneg _
    linarith
  have hdenI : (0 : ℝ) < (c s : ℝ) + (Fintype.card I - 1 : ℕ) := by
    have h : 0 < Fintype.card I - 1 := by omega
    have h' : (0 : ℝ) < (Fintype.card I - 1 : ℕ) := by exact_mod_cast h
    have h'' : (0 : ℝ) ≤ c s := Nat.cast_nonneg _
    linarith
  have hL : (0 : ℝ) < (L : ℝ) + 1 := by positivity
  have hj : (Fintype.card J - 1 : ℕ) / ((r a : ℝ) + (Fintype.card J - 1 : ℕ)) ≤
      1 / ((L : ℝ) + 1) := by
    apply (div_le_div_iff₀ hdenJ hL).mpr
    have hn : (Fintype.card J - 1) * (L + 1) ≤ r a + (Fintype.card J - 1) := by
      have h := (Nat.mul_le_mul_right L (Nat.sub_le (Fintype.card J) 1)).trans hr
      nlinarith
    simpa only [one_mul] using (show ((Fintype.card J - 1 : ℕ) : ℝ) * ((L : ℝ) + 1) ≤ (r a : ℝ) + (Fintype.card J - 1 : ℕ) by exact_mod_cast hn)
  have hi : (Fintype.card I - 1 : ℕ) / ((c s : ℝ) + (Fintype.card I - 1 : ℕ)) ≤
      1 / ((L : ℝ) + 1) := by
    apply (div_le_div_iff₀ hdenI hL).mpr
    have hn : (Fintype.card I - 1) * (L + 1) ≤ c s + (Fintype.card I - 1) := by
      have h := (Nat.mul_le_mul_right L (Nat.sub_le (Fintype.card I) 1)).trans hc
      nlinarith
    simpa only [one_mul] using (show ((Fintype.card I - 1 : ℕ) : ℝ) * ((L : ℝ) + 1) ≤ (c s : ℝ) + (Fintype.card I - 1 : ℕ) by exact_mod_cast hn)
  have hcor : (0 : ℝ) ≤ ((Fintype.card J - 1 : ℕ) * (Fintype.card I - 1 : ℕ) : ℕ) /
      (((r a : ℝ) + (Fintype.card J - 1 : ℕ)) * ((c s : ℝ) + (Fintype.card I - 1 : ℕ))) := by positivity
  have hp : (Fintype.card (Level r c a s 0) : ℝ) / Fintype.card (Table r c) ≤
      2 / ((L : ℝ) + 1) := by
    have heq : 2 / ((L : ℝ) + 1) = 1 / ((L : ℝ) + 1) + 1 / ((L : ℝ) + 1) := by ring
    rw [heq]
    linarith
  have hm := (div_le_div_iff₀ hcard hL).mp hp
  rw [mul_comm (2 : ℝ) (Fintype.card (Table r c) : ℝ)] at hm
  have hn : Fintype.card (Level r c a s 0) * (L + 1) ≤ Fintype.card (Table r c) * 2 := by
    exact_mod_cast hm
  exact hn

/-- At L≥7 and full row/column padding floors, every bounded signed reference
translation with at most two negative unit cells accepts at least one half.
This is a natural count conclusion derived from the sharp actual Table bound. -/
theorem accepted_half_seven (R : Option I → ℕ) (P : Option J → ℕ)
    (D : Option I → Option J → ℤ) (hD : Bounds D) (L : ℕ) (hL : 7 ≤ L)
    (hI : 2 ≤ Fintype.card (Option I)) (hJ : 2 ≤ Fintype.card (Option J))
    (htotal : (∑ i, R i) = ∑ j, P j)
    (hr : ∀ p ∈ negative D, Fintype.card (Option J) * L ≤ R p.1)
    (hc : ∀ p ∈ negative D, Fintype.card (Option I) * L ≤ P p.2) :
    Fintype.card (Table R P) ≤ 2 * Fintype.card (Accepted R P D) := by
  classical
  let event := fun (p : negative D) (X : Table R P) => X.val p.val.1 p.val.2 = 0
  have hlocal (p : negative D) : Fintype.card {X : Table R P // event p X} * (L + 1) ≤
      Fintype.card (Table R P) * 2 :=
    zero_count_floor R P p.val.1 p.val.2 L hI hJ htotal (hr p.val p.property) (hc p.val p.property)
  have h := Math115.PaddedMarginBridge.union_count_mul_bound event (L + 1) 2
    (fun p => by simpa only [Fintype.card_eq_nat_card] using hlocal p)
  have hu : Fintype.card {X : Table R P // ∃ p : negative D, event p X} * (L + 1) ≤
      Fintype.card (Table R P) * 4 := by
    have hneg : Fintype.card (negative D) ≤ 2 := by
      simpa only [Fintype.card_eq_nat_card, Nat.card_eq_finsetCard] using hD.negative_card
    have hterm : Fintype.card (negative D) * 2 ≤ 4 := by omega
    have h' : Fintype.card {X : Table R P // ∃ p : negative D, event p X} * (L + 1) ≤
        Fintype.card (Table R P) * (Fintype.card (negative D) * 2) := by
      simpa only [Fintype.card_eq_nat_card] using h
    exact h'.trans (Nat.mul_le_mul_left (Fintype.card (Table R P)) hterm)
  rw [← rejected_card_eq_zero_union R P D hD] at hu
  have hs := rejected_add_accepted R P D
  nlinarith

end Research.ReciprocalZeroPhysical

namespace Research.ConstantPaddingAcceptance

open OAI.ContingencyTables OAI.ContingencyTables.CompletionTranslation
open OAI.ContingencyTables.SmallGraphProfiles
open OAI.ContingencyTables.PhysicalCompletionFibres
open OAI.ContingencyTables.FirstPaperProfiles
open OAI.ContingencyTables.FirstPaperPhysicalMarginal
open OAI.ContingencyTables.CompletionCounts
open OAI.ContingencyTables.PaddedCompletions
open Math115.ReferenceEdgeAcceptance Research.AcceptancePadding
open Research.ReciprocalZeroPhysical
open scoped BigOperators Classical

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Constant positive padding suffices for every actual directed physical
reference edge. The signed translation, singleton dimensions and zero-donor cases, ordinary
completion identification, and all crossing repair branches are retained. -/
theorem reference_edge_acceptance_seven (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (B : I → J → ℕ) (hB : ∀ i j, firstPaperSmall r c U i j = true → B i j = U)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (hL : 7 ≤ L)
    (hcap : ∀ z : PhysicalStates (firstPaperSmall r c U) B r c L, ∀ i j,
      firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hxy : physicalAdjacent r c U L B hB x y) :
    (blockCount (referenceRows r c U L B i₀) (referenceColumns r c U L B j₀) x : ℝ) / 2 ≤
      acceptedCount (referenceRows r c U L B i₀) (referenceColumns r c U L B j₀) x y := by
  classical
  have hrCard := Fintype.card_congr (Equiv.optionSubtypeNe i₀)
  have hcCard := Fintype.card_congr (Equiv.optionSubtypeNe j₀)
  by_cases hR : 2 ≤ Fintype.card (LargeRows r U)
  · by_cases hC : 2 ≤ Fintype.card (LargeColumns c U)
    · have hD := physical_reference_adjustment_bounds r c U L B hB i₀ j₀ hcap x y hxy
      have h := accepted_half_seven
        (referenceRows r c U L B i₀ x) (referenceColumns r c U L B j₀ x) _ hD L hL
        (by simpa only [hrCard] using hR) (by simpa only [hcCard] using hC)
        (reference_totals r c U L B i₀ j₀ x (hcap x))
        (fun p _ => by
          rw [hcCard]
          exact residual_row_floor r c U L B x ((Equiv.optionSubtypeNe i₀) p.1))
        (fun p _ => by
          rw [hrCard]
          exact residual_column_floor r c U L B x ((Equiv.optionSubtypeNe j₀) p.2))
      have hreal : (blockCount (referenceRows r c U L B i₀) (referenceColumns r c U L B j₀) x : ℝ) ≤
          2 * acceptedCount (referenceRows r c U L B i₀) (referenceColumns r c U L B j₀) x y := by
        exact_mod_cast h
      linarith
    · have hc0 : Fintype.card {j : LargeColumns c U // j ≠ j₀} = 0 := by
        rw [Fintype.card_option] at hcCard
        omega
      exact reference_edge_acceptance_reduced r c U L B hB i₀ j₀
        (by rw [hc0]; simp) hcap x y hxy
  · have hr0 : Fintype.card {i : LargeRows r U // i ≠ i₀} = 0 := by
      rw [Fintype.card_option] at hrCard
      omega
    exact reference_edge_acceptance_reduced r c U L B hB i₀ j₀
      (by rw [hr0]; simp) hcap x y hxy

end Research.ConstantPaddingAcceptance
