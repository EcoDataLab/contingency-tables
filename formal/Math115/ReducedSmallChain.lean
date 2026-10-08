/-
SPDX-License-Identifier: Apache-2.0
An actual ideal completion chain with free cutoff and padding parameters.
The finite-bit implementation of its dense completion oracle is separate.
-/
import Math115.SmallChainGap
import Math115.ReferenceEdgeAcceptance

namespace Math115.ReducedSmallChain

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open PhysicalFullVariance
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts SmallContextCoordinates SmallContextFibres
open SmallContextEnumeration RowMajorEnumeration
open SmallGraphProfiles FiniteExposureVariance CompletionTranslation

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable abbrev capacity (r : I → ℕ) (c : J → ℕ) (U L : ℕ) : I → J → ℕ :=
  paperCapacity (firstPaperSmall r c U) r (dimensionAllowance (I := I) (J := J)) L U

abbrev States (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :=
  PhysicalStates (firstPaperSmall r c U) (capacity r c U L) r c L

noncomputable instance statesFintype (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :
    Fintype (States r c U L) :=
  physicalStatesFintype (firstPaperSmall r c U) (capacity r c U L) r c L

omit [LinearOrder I] [LinearOrder J] in
lemma capacity_small (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (i : I) (j : J)
    (h : firstPaperSmall r c U i j = true) : capacity r c U L i j = U := by
  simp only [capacity, paperCapacity, h, ite_true]

/-- The source completion-chain constructor, with its physical graph and
dyadic proposal unchanged, now instantiated at explicit free `U,L`. -/
noncomputable def chain (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U) :
    FiniteChain (States r c U L) :=
  completionChain
    (referenceRows r c U L (capacity r c U L) i₀)
    (referenceColumns r c U L (capacity r c U L) j₀)
    (fun z => reference_totals r c U L (capacity r c U L) i₀ j₀ z
      (physical_paper_capacity _ r c _ L U dimension_le_allowance z))
    (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L))
    (physicalAdjacent_symmetric r c U L (capacity r c U L) (capacity_small r c U L))
    (smallProposal (dimensionAllowance (I := I) (J := J)))
    ((smallProposal_bounds _ (by unfold dimensionAllowance; omega)).1.le)
    (5 * (dimensionAllowance (I := I) (J := J))^2 + 1)
    (physicalAdjacent_degree_allowance r c U L (capacity r c U L) (capacity_small r c U L))
    (smallProposal_degree _ (by unfold dimensionAllowance; omega))

noncomputable def weight (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (z : States r c U L) : ℝ :=
  hardMarginal (firstPaperSmall r c U) (capacity r c U L) r c L
    (physicalProfile _ (capacity r c U L) r c L z)

noncomputable def graphEnergy (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (H : States r c U L → ℝ) : ℝ :=
  fullEnergy r c U L (capacity r c U L) (capacity_small r c U L)
    (physicalExtension _ (capacity r c U L) r c L H)

lemma weight_positive (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (z : States r c U L) : 0 < weight r c U L z := z.property

lemma chain_pi (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (z : States r c U L) :
    (chain r c U L i₀ j₀).π z = weight r c U L z / (∑ y, weight r c U L y) := by
  have hw (y : States r c U L) := physical_weight_reference_block r c U L (capacity r c U L)
    i₀ j₀ y (physical_paper_capacity _ r c _ L U dimension_le_allowance y)
  change _ = hardMarginal _ _ _ _ _ _ / (∑ y, hardMarginal _ _ _ _ _ _)
  simp_rw [hw]
  rfl

/-- Every source residual table fits the actual chosen capacity. Thus this
variance bound has no new assumed weighted-graph inequality. -/
theorem state_variance_localized (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hU : 2 ≤ U) (H : States r c U L → ℝ) :
    variance (weight r c U L) H ≤
      fullConstant (Fintype.card (Cells (firstPaperSmall r c U))) U * graphEnergy r c U L H := by
  let d := dimensionAllowance (I := I) (J := J)
  let B := capacity r c U L
  have hlarge : ∀ i j, firstPaperSmall r c U i j = false → 2 ≤ B i j := by
    intro i j hij
    simp only [B, capacity, paperCapacity, hij, Bool.false_eq_true, ite_false]
    omega
  have hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i + rowLargeCount (firstPaperSmall r c U) i * L)
      (fun j => c j + columnLargeCount (firstPaperSmall r c U) j * L),
      ∀ i j, T.val.val i j ≤ B i j :=
    paper_residual_capacity r c d L U dimension_le_allowance
  exact physical_variance_localized r c U L B hU (capacity_small r c U L) hlarge hcap H

/-- The source reference block's donor count is bounded by the original
dimension allowance, including singleton reference blocks. -/
lemma nonreference_product_le_allowance (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) :
    Fintype.card {i : LargeRows r U // i ≠ i₀} *
        Fintype.card {j : LargeColumns c U // j ≠ j₀} ≤
      dimensionAllowance (I := I) (J := J) := by
  have hi : Fintype.card {i : LargeRows r U // i ≠ i₀} ≤ Fintype.card I :=
    (Fintype.card_subtype_le _).trans (Fintype.card_subtype_le _)
  have hj : Fintype.card {j : LargeColumns c U // j ≠ j₀} ≤ Fintype.card J :=
    (Fintype.card_subtype_le _).trans (Fintype.card_subtype_le _)
  exact (Nat.mul_le_mul hi hj).trans dimension_le_allowance

/-- The proved reduced-padding acceptance theorem supplies the actual
source completion-chain energy comparison. -/
theorem chain_energy_lower (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (hL : 3 * dimensionAllowance (I := I) (J := J) ≤ L)
    (H : States r c U L → ℝ) :
    smallProposal (dimensionAllowance (I := I) (J := J)) /
        (2 * (∑ z, weight r c U L z)) * graphEnergy r c U L H ≤
      (chain r c U L i₀ j₀).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  let B := capacity r c U L
  let R := referenceRows r c U L B i₀
  let P := referenceColumns r c U L B j₀
  have hcap := physical_paper_capacity (firstPaperSmall r c U) r c d L U dimension_le_allowance
  have hw (z : States r c U L) : weight r c U L z = (blockCount R P z : ℝ) :=
    physical_weight_reference_block r c U L B i₀ j₀ z (hcap z)
  have hscale : 3 * (Fintype.card {i : LargeRows r U // i ≠ i₀} *
      Fintype.card {j : LargeColumns c U // j ≠ j₀}) ≤ L :=
    (Nat.mul_le_mul_left 3 (nonreference_product_le_allowance r c U i₀ j₀)).trans hL
  have hh := completionChain_energy_lower R P
    (fun z => reference_totals r c U L B i₀ j₀ z (hcap z))
    (physicalAdjacent r c U L B (capacity_small r c U L))
    (physicalAdjacent_symmetric r c U L B (capacity_small r c U L))
    (smallProposal d) ((smallProposal_bounds d (by dsimp [d, dimensionAllowance]; omega)).1.le)
    (5 * d^2 + 1)
    (physicalAdjacent_degree_allowance r c U L B (capacity_small r c U L))
    (smallProposal_degree d (by dsimp [d, dimensionAllowance]; omega))
    (ReferenceEdgeAcceptance.reference_edge_acceptance_reduced r c U L B
      (capacity_small r c U L) i₀ j₀ hscale hcap) H
  have hE := fullEnergy_physical_eq r c U L B (capacity_small r c U L) H
  change graphEnergy r c U L H = (∑ x, ∑ y,
    if physicalAdjacent r c U L B (capacity_small r c U L) x y then
      min (weight r c U L x) (weight r c U L y) * (H x - H y)^2 else 0) / 2 at hE
  rw [hE]
  simp_rw [hw]
  exact hh

/-- Exact Poincare coefficient for the actual parameterized ideal chain. -/
theorem chain_poincare_exact (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (hU : 2 ≤ U) (hL : 3 * dimensionAllowance (I := I) (J := J) ≤ L)
    (H : States r c U L → ℝ) :
    (chain r c U L i₀ j₀).variance H ≤
      (2 * fullConstant (Fintype.card (Cells (firstPaperSmall r c U))) U /
        smallProposal (dimensionAllowance (I := I) (J := J))) *
      (chain r c U L i₀ j₀).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  exact chain_poincare_of_weighted_graph (chain r c U L i₀ j₀) (weight r c U L) H
    (weight_positive r c U L) (chain_pi r c U L i₀ j₀) (graphEnergy r c U L H)
    (fullConstant (Fintype.card (Cells (firstPaperSmall r c U))) U) (smallProposal d)
    (fullConstant_nonnegative _ _) (smallProposal_bounds d (by dsimp [d, dimensionAllowance]; omega)).1
    (state_variance_localized r c U L hU H) (chain_energy_lower r c U L i₀ j₀ hL H)

/-- The generic ideal chain has inverse-gap allowance `1024*d^5*U^4`. -/
theorem chain_poincare_polynomial (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (hU : 2 ≤ U) (hL : 3 * dimensionAllowance (I := I) (J := J) ≤ L)
    (H : States r c U L → ℝ) :
    (chain r c U L i₀ j₀).variance H ≤
      (1024 * (dimensionAllowance (I := I) (J := J) : ℝ)^5 * (U : ℝ)^4) *
        (chain r c U L i₀ j₀).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  have hd : 1 ≤ d := by dsimp [d, dimensionAllowance]; omega
  have hp : Fintype.card (Cells (firstPaperSmall r c U)) ≤ d :=
    (small_card_le_dimension (firstPaperSmall r c U)).trans dimension_le_allowance
  exact SmallChainGap.chain_poincare_localized (chain r c U L i₀ j₀) (weight r c U L) H
    (graphEnergy r c U L H) (Fintype.card (Cells (firstPaperSmall r c U))) d U hd
    (by omega) hp (weight_positive r c U L) (chain_pi r c U L i₀ j₀)
    (state_variance_localized r c U L hU H) (chain_energy_lower r c U L i₀ j₀ hL H)

noncomputable abbrev reducedU : ℕ :=
  47 * (dimensionAllowance (I := I) (J := J))^5

noncomputable abbrev reducedL : ℕ :=
  32 * (dimensionAllowance (I := I) (J := J))^3

abbrev ReducedStates (r : I → ℕ) (c : J → ℕ) :=
  States r c (reducedU (I := I) (J := J)) (reducedL (I := I) (J := J))

noncomputable def reducedChain (r : I → ℕ) (c : J → ℕ) [Nonempty (ReducedStates r c)]
    (i₀ : LargeRows r (reducedU (I := I) (J := J)))
    (j₀ : LargeColumns c (reducedU (I := I) (J := J))) : FiniteChain (ReducedStates r c) :=
  chain r c _ _ i₀ j₀

/-- The new scales define an actual ideal chain with a `d^25` inverse-gap
bound. This is a chain theorem, not a finite-bit runtime theorem. -/
theorem reducedChain_poincare_d25 (r : I → ℕ) (c : J → ℕ) [Nonempty (ReducedStates r c)]
    (i₀ : LargeRows r (reducedU (I := I) (J := J)))
    (j₀ : LargeColumns c (reducedU (I := I) (J := J))) (H : ReducedStates r c → ℝ) :
    (reducedChain r c i₀ j₀).variance H ≤
      ((1024 * 47^4 : ℝ) * (dimensionAllowance (I := I) (J := J) : ℝ)^25) *
        (reducedChain r c i₀ j₀).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  have hd : 1 ≤ d := by dsimp [d, dimensionAllowance]; omega
  have hd3 : d ≤ d^3 := Nat.le_self_pow (by decide) d
  have hd5 : d ≤ d^5 := Nat.le_self_pow (by decide) d
  have hU : 2 ≤ 47 * d^5 := by omega
  have hL : 3 * d ≤ 32 * d^3 := by omega
  have h := chain_poincare_polynomial r c (47 * d^5) (32 * d^3) i₀ j₀ hU hL H
  change (chain r c (47 * d^5) (32 * d^3) i₀ j₀).variance H ≤
    ((1024 * 47^4 : ℝ) * (d : ℝ)^25) * (chain r c (47 * d^5) (32 * d^3) i₀ j₀).energy H
  convert h using 1
  push_cast
  ring

end Math115.ReducedSmallChain
