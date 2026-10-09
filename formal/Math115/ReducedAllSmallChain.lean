/-
SPDX-License-Identifier: Apache-2.0
The reduced-scale ideal chain when no reference row or column exists,
and a single branch-selection wrapper covering every margin shape.
-/
import Math115.ReducedSmallChain
import OAI.Combinatorics.ContingencyTables.Sampling.UnitGraphEnergy

namespace Math115.ReducedAllSmallChain

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open PhysicalFullVariance ReducedSmallChain
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts SmallContextCoordinates SmallContextFibres
open SmallContextEnumeration RowMajorEnumeration
open SmallGraphProfiles FiniteExposureVariance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The source unit Metropolis construction on the actual reduced physical
graph: every valid proposal is accepted. -/
noncomputable def unitChain (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] : FiniteChain (States r c U L) :=
  MetropolisChain.chain (fun _ => 1) (fun _ => by norm_num)
    (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L))
    (physicalAdjacent_symmetric r c U L (capacity r c U L) (capacity_small r c U L))
    (smallProposal (dimensionAllowance (I := I) (J := J)))
    ((smallProposal_bounds _ (by unfold dimensionAllowance; omega)).1.le)
    (5 * (dimensionAllowance (I := I) (J := J))^2 + 1)
    (physicalAdjacent_degree_allowance r c U L (capacity r c U L) (capacity_small r c U L))
    (smallProposal_degree _ (by unfold dimensionAllowance; omega))

/-- Actual completion weights equal one when the large rectangle is empty.
The source capacity premise is discharged, rather than assumed. -/
theorem weight_eq_one (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U))
    (z : States r c U L) : weight r c U L z = 1 := by
  exact CompletionAdjustment.physical_empty_completion_weight r c U L (capacity r c U L) z
    (physical_paper_capacity _ r c _ L U dimension_le_allowance z) hempty

lemma unitChain_pi (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (z : States r c U L) :
    (unitChain r c U L).π z = 1 / (Fintype.card (States r c U L) : ℝ) := by
  simp only [unitChain, MetropolisChain.chain, FiniteChain.ofMoves,
    MetropolisChain.normalizer, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem unitChain_pi_weight (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)]
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U))
    (z : States r c U L) :
    (unitChain r c U L).π z = weight r c U L z / (∑ y, weight r c U L y) := by
  rw [unitChain_pi]
  simp only [weight_eq_one r c U L hempty, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one]

lemma graphEnergy_empty (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U))
    (H : States r c U L → ℝ) :
    graphEnergy r c U L H = (∑ x, ∑ y,
      if physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y then
        (H x - H y)^2 else 0) / 2 := by
  have he := fullEnergy_physical_eq r c U L (capacity r c U L) (capacity_small r c U L) H
  change graphEnergy r c U L H = (∑ x, ∑ y,
    if physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y then
      min (weight r c U L x) (weight r c U L y) * (H x - H y)^2 else 0) / 2 at he
  simpa only [weight_eq_one r c U L hempty, min_self, one_mul] using he

/-- The unit branch has an exact energy identity, with no half-acceptance loss. -/
theorem unitChain_energy (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)]
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U))
    (H : States r c U L → ℝ) :
    (unitChain r c U L).energy H =
      (smallProposal (dimensionAllowance (I := I) (J := J)) /
        (∑ z, weight r c U L z)) * graphEnergy r c U L H := by
  have he := MetropolisChain.unit_chain_energy
    (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L))
    (physicalAdjacent_symmetric r c U L (capacity r c U L) (capacity_small r c U L))
    (smallProposal (dimensionAllowance (I := I) (J := J)))
    ((smallProposal_bounds _ (by unfold dimensionAllowance; omega)).1.le)
    (5 * (dimensionAllowance (I := I) (J := J))^2 + 1)
    (physicalAdjacent_degree_allowance r c U L (capacity r c U L) (capacity_small r c U L))
    (smallProposal_degree _ (by unfold dimensionAllowance; omega)) H
  rw [graphEnergy_empty r c U L hempty H]
  simpa only [unitChain, States, weight_eq_one r c U L hempty, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] using he

/-- The generic unit branch needs `U ≥ 2`; its empty completion block imposes
no lower bound on the padding `L`. -/
theorem unitChain_poincare_exact (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)]
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U))
    (hU : 2 ≤ U) (H : States r c U L → ℝ) :
    (unitChain r c U L).variance H ≤
      (fullConstant (Fintype.card (Cells (firstPaperSmall r c U))) U /
        smallProposal (dimensionAllowance (I := I) (J := J))) * (unitChain r c U L).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  let K := fullConstant (Fintype.card (Cells (firstPaperSmall r c U))) U
  have hβ := (smallProposal_bounds d (by dsimp [d, dimensionAllowance]; omega)).1
  have hZ : 0 < ∑ z : States r c U L, weight r c U L z :=
    Finset.sum_pos (fun z _ => weight_positive r c U L z) Finset.univ_nonempty
  have hv : variance (weight r c U L) H ≤ K * graphEnergy r c U L H :=
    state_variance_localized r c U L hU H
  rw [chain_variance_eq (unitChain r c U L) (weight r c U L) H
    (unitChain_pi_weight r c U L hempty)]
  calc
    _ ≤ (K * graphEnergy r c U L H) / (∑ z, weight r c U L z) :=
      div_le_div_of_nonneg_right hv hZ.le
    _ = (K / smallProposal d) * (unitChain r c U L).energy H := by
      rw [unitChain_energy r c U L hempty H]
      field_simp [ne_of_gt hβ, ne_of_gt hZ]
      ring

theorem unitChain_poincare_polynomial (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)]
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U))
    (hU : 2 ≤ U) (H : States r c U L → ℝ) :
    (unitChain r c U L).variance H ≤
      (512 * (dimensionAllowance (I := I) (J := J) : ℝ)^5 * (U : ℝ)^4) *
        (unitChain r c U L).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  let K := fullConstant (Fintype.card (Cells (firstPaperSmall r c U))) U
  have hd : 1 ≤ d := by dsimp [d, dimensionAllowance]; omega
  have hp : Fintype.card (Cells (firstPaperSmall r c U)) ≤ d :=
    (small_card_le_dimension (firstPaperSmall r c U)).trans dimension_le_allowance
  have hb := SmallChainGap.smallProposal_localized_budget
    (Fintype.card (Cells (firstPaperSmall r c U))) d U hd (by omega) hp
  have hb' : 2 * (K / smallProposal d) ≤ 1024 * (d : ℝ)^5 * (U : ℝ)^4 := by
    convert hb using 1
    ring
  have hc : K / smallProposal d ≤ 512 * (d : ℝ)^5 * (U : ℝ)^4 := by
    linarith only [hb']
  exact (unitChain_poincare_exact r c U L hempty hU H).trans
    (mul_le_mul_of_nonneg_right hc ((unitChain r c U L).energy_nonneg H))

omit [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J] in
lemma missing_reference_empty (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (h : ¬ (Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U))) :
    IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U) := by
  by_cases hi : Nonempty (LargeRows r U)
  · exact Or.inr ⟨fun j => h ⟨hi, ⟨j⟩⟩⟩
  · exact Or.inl ⟨fun i => hi ⟨i⟩⟩

/-- Choose a reference row and column when both exist; otherwise use the
unit chain on the same positive-weight physical state space. -/
noncomputable def selectedChain (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] : FiniteChain (States r c U L) :=
  if h : Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U) then
    ReducedSmallChain.chain r c U L (Classical.choice h.1) (Classical.choice h.2)
  else unitChain r c U L

/-- Both branches have the same desired completion-weight stationary law. -/
theorem selectedChain_pi (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (z : States r c U L) :
    (selectedChain r c U L).π z = weight r c U L z / (∑ y, weight r c U L y) := by
  unfold selectedChain
  split_ifs with h
  · exact chain_pi r c U L (Classical.choice h.1) (Classical.choice h.2) z
  · exact unitChain_pi_weight r c U L (missing_reference_empty r c U h) z

/-- The exact reference-branch coefficient bounds the selected chain in
either branch; the empty-block branch has the stronger factor-one result. -/
theorem selectedChain_poincare_exact (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (hU : 2 ≤ U)
    (hL : 3 * dimensionAllowance (I := I) (J := J) ≤ L) (H : States r c U L → ℝ) :
    (selectedChain r c U L).variance H ≤
      (2 * fullConstant (Fintype.card (Cells (firstPaperSmall r c U))) U /
        smallProposal (dimensionAllowance (I := I) (J := J))) *
      (selectedChain r c U L).energy H := by
  unfold selectedChain
  split_ifs with h
  · exact chain_poincare_exact r c U L (Classical.choice h.1) (Classical.choice h.2) hU hL H
  · have hu := unitChain_poincare_exact r c U L (missing_reference_empty r c U h) hU H
    have hb := (smallProposal_bounds (dimensionAllowance (I := I) (J := J))
      (by unfold dimensionAllowance; omega)).1
    have hn : 0 ≤ fullConstant (Fintype.card (Cells (firstPaperSmall r c U))) U /
        smallProposal (dimensionAllowance (I := I) (J := J)) :=
      div_nonneg (fullConstant_nonnegative _ _) hb.le
    exact hu.trans (mul_le_mul_of_nonneg_right (by
      rw [mul_div_assoc]
      linarith only [hn])
      ((unitChain r c U L).energy_nonneg H))

theorem selectedChain_poincare_polynomial (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (hU : 2 ≤ U)
    (hL : 3 * dimensionAllowance (I := I) (J := J) ≤ L) (H : States r c U L → ℝ) :
    (selectedChain r c U L).variance H ≤
      (1024 * (dimensionAllowance (I := I) (J := J) : ℝ)^5 * (U : ℝ)^4) *
        (selectedChain r c U L).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  have hd : 1 ≤ d := by dsimp [d, dimensionAllowance]; omega
  have hp : Fintype.card (Cells (firstPaperSmall r c U)) ≤ d :=
    (small_card_le_dimension (firstPaperSmall r c U)).trans dimension_le_allowance
  exact (selectedChain_poincare_exact r c U L hU hL H).trans
    (mul_le_mul_of_nonneg_right (SmallChainGap.smallProposal_localized_budget
      (Fintype.card (Cells (firstPaperSmall r c U))) d U hd (by omega) hp)
      ((selectedChain r c U L).energy_nonneg H))

noncomputable def reducedUnitChain (r : I → ℕ) (c : J → ℕ) [Nonempty (ReducedStates r c)] :
    FiniteChain (ReducedStates r c) := unitChain r c _ _

theorem reducedUnitChain_poincare_d25 (r : I → ℕ) (c : J → ℕ)
    [Nonempty (ReducedStates r c)]
    (hempty : IsEmpty (LargeRows r (reducedU (I := I) (J := J))) ∨
      IsEmpty (LargeColumns c (reducedU (I := I) (J := J)))) (H : ReducedStates r c → ℝ) :
    (reducedUnitChain r c).variance H ≤
      ((512 * 47^4 : ℝ) * (dimensionAllowance (I := I) (J := J) : ℝ)^25) *
        (reducedUnitChain r c).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  have hd : 1 ≤ d := by dsimp [d, dimensionAllowance]; omega
  have hd5 : d ≤ d^5 := Nat.le_self_pow (by decide) d
  have hU : 2 ≤ 47 * d^5 := by omega
  have h := unitChain_poincare_polynomial r c (47 * d^5) (32 * d^3) hempty hU H
  change (unitChain r c (47 * d^5) (32 * d^3)).variance H ≤
    ((512 * 47^4 : ℝ) * (d : ℝ)^25) * (unitChain r c (47 * d^5) (32 * d^3)).energy H
  convert h using 1
  push_cast
  ring

noncomputable def reducedSelectedChain (r : I → ℕ) (c : J → ℕ)
    [Nonempty (ReducedStates r c)] : FiniteChain (ReducedStates r c) := selectedChain r c _ _

/-- A single actual reduced ideal chain satisfies the `d^25` bound for every
margin shape, with no externally supplied reference row or column. -/
theorem reducedSelectedChain_poincare_d25 (r : I → ℕ) (c : J → ℕ)
    [Nonempty (ReducedStates r c)] (H : ReducedStates r c → ℝ) :
    (reducedSelectedChain r c).variance H ≤
      ((1024 * 47^4 : ℝ) * (dimensionAllowance (I := I) (J := J) : ℝ)^25) *
        (reducedSelectedChain r c).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  have hd : 1 ≤ d := by dsimp [d, dimensionAllowance]; omega
  have hd3 : d ≤ d^3 := Nat.le_self_pow (by decide) d
  have hd5 : d ≤ d^5 := Nat.le_self_pow (by decide) d
  have hU : 2 ≤ 47 * d^5 := by omega
  have hL : 3 * d ≤ 32 * d^3 := by omega
  have h := selectedChain_poincare_polynomial r c (47 * d^5) (32 * d^3) hU hL H
  change (selectedChain r c (47 * d^5) (32 * d^3)).variance H ≤
    ((1024 * 47^4 : ℝ) * (d : ℝ)^25) * (selectedChain r c (47 * d^5) (32 * d^3)).energy H
  convert h using 1
  push_cast
  ring

end Math115.ReducedAllSmallChain
