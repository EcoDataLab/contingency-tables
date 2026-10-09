/-
SPDX-License-Identifier: Apache-2.0

An ideal-oracle scale choice, separate from the dense finite-bit sampler.
The padding counts and reference-chain Poincare bound use actual upstream
objects. The dense geometry hypotheses are explicitly incompatible.
-/
import Math115.ReducedSmallChain
import Math115.PaddingGrowth
import Math115.PhysicalStateNonempty

namespace Math115.IdealOracleScales

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open CompletionCounts SmallGraphProfiles
open scoped BigOperators Classical

def idealL (d : ℕ) : ℕ := 3 * d
def idealU (d : ℕ) : ℕ := 5 * d ^ 3

theorem threshold_at_least_two (d : ℕ) (hd : 1 ≤ d) : 2 ≤ idealU d := by
  have hp : d ≤ d ^ 3 := Nat.le_self_pow (by decide) d
  unfold idealU
  omega

theorem padding_at_least_three_dimension (d : ℕ) : 3 * d ≤ idealL d := le_refl _

theorem threshold_at_least_twice_padding (d : ℕ) (hd : 2 ≤ d) :
    2 * idealL d ≤ idealU d := by
  have hp : 2 ≤ d * d := by nlinarith
  have hm := Nat.mul_le_mul_right d hp
  have hcube : d ^ 3 = d * d * d := by ring
  unfold idealL idealU
  rw [hcube]
  nlinarith only [hm]

/-- The full-dimension budget precedes the threshold-selected marked set. -/
theorem sequential_scale_budget (d g e : ℕ) (hg : g ≤ d) (he : e ≤ d) :
    47 * (g * idealL d) * e ≤ 32 * (idealU d + 1) := by
  calc
    _ = (47 * idealL d) * (g * e) := by ring
    _ ≤ (47 * idealL d) * (d * d) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hg he)
    _ = 141 * d ^ 3 := by unfold idealL; ring
    _ ≤ 32 * (idealU d + 1) := by unfold idealU; omega

/-- Actual ordinary-table counts, including empty fibers and marked sets.
This is not a probability statement about the defect-augmented chain. -/
theorem padded_count_le_twice_original
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (r : I → ℕ) (c : J → ℕ) (K : Finset (I × J)) (d : ℕ)
    (hsize : Fintype.card I * Fintype.card J ≤ d)
    (hrow : ∀ p ∈ K, idealU d ≤ r p.1)
    (hcol : ∀ p ∈ K, idealU d ≤ c p.2) :
    Fintype.card (Table (paddedRows r (largePadding K (idealL d)))
      (paddedColumns c (largePadding K (idealL d)))) ≤ 2 * Fintype.card (Table r c) := by
  classical
  have hK : K.card ≤ d :=
    (show K.card ≤ Fintype.card I * Fintype.card J by
      simpa only [Fintype.card_prod] using K.card_le_univ).trans hsize
  have he : (Fintype.card I - 1) * (Fintype.card J - 1) ≤ d :=
    (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)).trans hsize
  exact PaddingGrowthAlgebra.count_le_twice_of_growth _ _ _ _ _
    (PaddingGrowth.large_padding_count_growth r c K (idealL d) (idealU d) hrow hcol)
    (sequential_scale_budget d K.card _ hK he)

/-- Actual unpadding-successful table cardinalities, with no denominator. -/
theorem padded_count_le_twice_successful
    {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    (r : I → ℕ) (c : J → ℕ) (K : Finset (I × J)) (d : ℕ)
    (hsize : Fintype.card I * Fintype.card J ≤ d)
    (hrow : ∀ p ∈ K, idealU d ≤ r p.1)
    (hcol : ∀ p ∈ K, idealU d ≤ c p.2) :
    Fintype.card (Table (paddedRows r (largePadding K (idealL d)))
      (paddedColumns c (largePadding K (idealL d)))) ≤
      2 * Fintype.card {Y : Table (paddedRows r (largePadding K (idealL d)))
        (paddedColumns c (largePadding K (idealL d))) //
        ¬∃ p : K, Y.val p.val.1 p.val.2 < idealL d} := by
  rw [PaddedMarginBridge.large_padding_good_card r c K (idealL d)]
  exact padded_count_le_twice_original r c K d hsize hrow hcol

/-- The retained sufficient dense interface forces `L >= 32*d^3`.
This is an interface obstruction, not a lower bound for dense algorithms. -/
theorem dense_padding_lower_bound (d A B L : ℕ) (h : DenseScaleConditions d A B L) :
    32 * d ^ 3 ≤ L := by
  have hchange := Nat.mul_le_mul_left (8 * d ^ 2) h.density_change
  have hAB : A * (16 * d ^ 3) ≤ A * B := by
    calc
      _ = 8 * d ^ 2 * (A * d) + 8 * d ^ 3 * A := by ring
      _ ≤ 8 * d ^ 2 * B + 8 * d ^ 3 * A := Nat.add_le_add_right hchange _
      _ ≤ A * B := h.normalizer_budget
  have hB : 16 * d ^ 3 ≤ B := Nat.le_of_mul_le_mul_left hAB h.penalty_pos
  calc
    32 * d ^ 3 = 2 * (16 * d ^ 3) := by ring
    _ ≤ 2 * B := Nat.mul_le_mul_left 2 hB
    _ ≤ L := h.padding_width

/-- Retuning `A,B` cannot recover the retained dense sufficient interface
at `L = 3*d` in positive dimensions. -/
theorem incompatible_dense_scales (d A B : ℕ) (hd : 1 ≤ d) :
    ¬DenseScaleConditions d A B (idealL d) := by
  intro h
  have hp : d ≤ d ^ 3 := Nat.le_self_pow (by decide) d
  have hw := dense_padding_lower_bound d A B (idealL d) h
  unfold idealL at hw
  omega

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

theorem dimension_at_least_eleven : 11 ≤ dimensionAllowance (I := I) (J := J) := by
  unfold dimensionAllowance
  have hi : 1 ≤ Fintype.card I + 1 := by omega
  have hj : 1 ≤ Fintype.card J + 1 := by omega
  have hm := Nat.mul_le_mul hi hj
  omega

noncomputable abbrev cutoff : ℕ := idealU (dimensionAllowance (I := I) (J := J))
noncomputable abbrev padding : ℕ := idealL (dimensionAllowance (I := I) (J := J))

abbrev IdealStates (r : I → ℕ) (c : J → ℕ) :=
  ReducedSmallChain.States r c (cutoff (I := I) (J := J)) (padding (I := I) (J := J))

noncomputable def idealLarge (r : I → ℕ) (c : J → ℕ) : Finset (I × J) :=
  Finset.univ.filter (fun p => firstPaperSmall r c (cutoff (I := I) (J := J)) p.1 p.2 = false)

/-- Specialize the count bound to the actual threshold-selected large rectangle. -/
theorem ideal_large_padded_count_le_twice_original (r : I → ℕ) (c : J → ℕ) :
    Fintype.card (Table (paddedRows r (largePadding (idealLarge r c) (padding (I := I) (J := J))))
      (paddedColumns c (largePadding (idealLarge r c) (padding (I := I) (J := J))))) ≤
      2 * Fintype.card (Table r c) := by
  have hr : ∀ p ∈ idealLarge r c, cutoff (I := I) (J := J) ≤ r p.1 := by
    intro p hp
    exact ((firstPaperSmall_false_iff r c _ _ _).mp (Finset.mem_filter.mp hp).2).1
  have hc : ∀ p ∈ idealLarge r c, cutoff (I := I) (J := J) ≤ c p.2 := by
    intro p hp
    exact ((firstPaperSmall_false_iff r c _ _ _).mp (Finset.mem_filter.mp hp).2).2
  exact padded_count_le_twice_original r c (idealLarge r c) _ dimension_le_allowance hr hc

/-- The actual reference completion chain at the ideal-only scales. -/
noncomputable def referenceChain (r : I → ℕ) (c : J → ℕ) [Nonempty (IdealStates r c)]
    (i₀ : LargeRows r (cutoff (I := I) (J := J)))
    (j₀ : LargeColumns c (cutoff (I := I) (J := J))) : FiniteChain (IdealStates r c) :=
  ReducedSmallChain.chain r c _ _ i₀ j₀

/-- An actual-chain inverse-gap allowance, not a finite-bit runtime bound. -/
theorem referenceChain_poincare_d17 (r : I → ℕ) (c : J → ℕ) [Nonempty (IdealStates r c)]
    (i₀ : LargeRows r (cutoff (I := I) (J := J)))
    (j₀ : LargeColumns c (cutoff (I := I) (J := J))) (H : IdealStates r c → ℝ) :
    (referenceChain r c i₀ j₀).variance H ≤
      ((1024 * 5^4 : ℝ) * (dimensionAllowance (I := I) (J := J) : ℝ)^17) *
        (referenceChain r c i₀ j₀).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  have hd : 1 ≤ d := by dsimp [d, dimensionAllowance]; omega
  have h := ReducedSmallChain.chain_poincare_polynomial r c (idealU d) (idealL d) i₀ j₀
    (threshold_at_least_two d hd) (padding_at_least_three_dimension d) H
  change (ReducedSmallChain.chain r c (idealU d) (idealL d) i₀ j₀).variance H ≤
    ((1024 * 5^4 : ℝ) * (d : ℝ)^17) *
      (ReducedSmallChain.chain r c (idealU d) (idealL d) i₀ j₀).energy H
  convert h using 1
  unfold idealU
  push_cast
  ring

/-- Select the reference branch when possible and the unit branch otherwise. -/
noncomputable def selectedChain (r : I → ℕ) (c : J → ℕ) [Nonempty (IdealStates r c)] :
    FiniteChain (IdealStates r c) :=
  ReducedAllSmallChain.selectedChain r c _ _

theorem selectedChain_poincare_d17 (r : I → ℕ) (c : J → ℕ) [Nonempty (IdealStates r c)]
    (H : IdealStates r c → ℝ) :
    (selectedChain r c).variance H ≤
      ((1024 * 5^4 : ℝ) * (dimensionAllowance (I := I) (J := J) : ℝ)^17) *
        (selectedChain r c).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  have hd : 1 ≤ d := by dsimp [d, dimensionAllowance]; omega
  have h := ReducedAllSmallChain.selectedChain_poincare_polynomial r c (idealU d) (idealL d)
    (threshold_at_least_two d hd) (padding_at_least_three_dimension d) H
  change (ReducedAllSmallChain.selectedChain r c (idealU d) (idealL d)).variance H ≤
    ((1024 * 5^4 : ℝ) * (d : ℝ)^17) *
      (ReducedAllSmallChain.selectedChain r c (idealU d) (idealL d)).energy H
  convert h using 1
  unfold idealU
  push_cast
  ring

/-- Equal ordinary totals supply a positive state at the chosen ideal scales. -/
noncomputable def feasibleChain (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) : FiniteChain (IdealStates r c) := by
  letI := PhysicalStateNonempty.states_nonempty r c (cutoff (I := I) (J := J))
    (padding (I := I) (J := J)) htotal
  exact selectedChain r c

/-- The ideal d17 bound for all equal-total ordinary margins, including
missing reference rows/columns and empty index types. -/
theorem feasibleChain_poincare_d17 (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (H : IdealStates r c → ℝ) :
    (feasibleChain r c htotal).variance H ≤
      ((1024 * 5^4 : ℝ) * (dimensionAllowance (I := I) (J := J) : ℝ)^17) *
        (feasibleChain r c htotal).energy H := by
  letI := PhysicalStateNonempty.states_nonempty r c (cutoff (I := I) (J := J))
    (padding (I := I) (J := J)) htotal
  exact selectedChain_poincare_d17 r c H

end Math115.IdealOracleScales
