/-
SPDX-License-Identifier: Apache-2.0
Sharper repair coefficients for the unchanged positive-weight physical state
space and ideal completion chains. No dense-oracle runtime claim is made.
-/
import Math115.RepairVarianceRefinement
import Math115.ReducedAllSmallChain

namespace Math115.PhysicalRepairRefinement

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres FirstPaperProfiles
open FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration FiniteExposureVariance IntegerWeightedTransport
open SmallGraphProfiles Math115.PhysicalExposureVariance Math115.PhysicalFullVariance
open Math115.ReducedSmallChain Math115.ReducedAllSmallChain

/-- The base variance stays outside the defect-side cross term. -/
noncomputable def refinedConstant (p U : ℕ) : ℝ :=
  transversalConstant p U +
    (Real.sqrt ((p : ℝ)^2 * transversalConstant p U) + 1)^2

lemma refinedConstant_nonnegative (p U : ℕ) : 0 ≤ refinedConstant p U :=
  RepairVarianceRefinement.repair_sqrt_coefficient_nonnegative _ _
    (transversalConstant_nonnegative p U)

/-- The earlier certificate remains valid, with its name and proof unchanged. -/
lemma refinedConstant_le_fullConstant (p U : ℕ) :
    refinedConstant p U ≤ fullConstant p U :=
  RepairVarianceRefinement.repair_sqrt_coefficient_le_source _ _
    (sq_nonneg _) (transversalConstant_nonnegative p U)

/-- A freely tuned Young envelope for the square-root repair coefficient.
This proof divides only by positive d, so D*C=0 is included. -/
lemma sqrt_coefficient_le_young (D C d : ℝ) (hD : 0 ≤ D) (hC : 0 ≤ C) (hd : 0 < d) :
    C + (Real.sqrt (D * C) + 1)^2 ≤ (1 + (1 + 1 / d) * D) * C + 1 + d := by
  have hs := Real.sq_sqrt (mul_nonneg hD hC)
  have hid : d * ((1 + (1 + 1 / d) * D) * C + 1 + d -
      (C + (Real.sqrt (D * C) + 1)^2)) = (Real.sqrt (D * C) - d)^2 := by
    simp only [add_sq, sub_sq, hs]
    field_simp [ne_of_gt hd]
    ring
  have hn : 0 ≤ d * ((1 + (1 + 1 / d) * D) * C + 1 + d -
      (C + (Real.sqrt (D * C) + 1)^2)) := by rw [hid]; exact sq_nonneg _
  have h := (mul_nonneg_iff_of_pos_left hd).mp hn
  linarith

/-- A sharper polynomial envelope; Nat subtraction handles p=0 explicitly. -/
theorem refinedConstant_le_polynomial (p d U : ℕ)
    (hd : 11 ≤ d) (hU : 2 ≤ U) (hp : p ≤ d) :
    refinedConstant p U ≤ (d : ℝ)^3 * (U : ℝ)^4 := by
  have hdR : (11 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  have hUR : (2 : ℝ) ≤ U := by exact_mod_cast hU
  have hpR : (p : ℝ) ≤ d := by exact_mod_cast hp
  have hpminus : ((p - 1 : ℕ) : ℝ) ≤ (d : ℝ) - 1 := by
    have h : ((p - 1 : ℕ) : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le_sub_right hp 1
    simpa only [Nat.cast_sub (show 1 ≤ d by omega), Nat.cast_one] using h
  have hT : (U : ℝ) * ((U : ℝ) + 1) / 2 ≤ 3 / 4 * (U : ℝ)^2 := by
    have h := mul_le_mul_of_nonneg_left hUR (Nat.cast_nonneg U : (0 : ℝ) ≤ U)
    nlinarith only [h]
  have hq : ((U : ℝ) + 1)^2 ≤ 9 / 4 * (U : ℝ)^2 := by
    nlinarith only [hUR, sq_nonneg ((U : ℝ) - 2)]
  have hU2 : (4 : ℝ) ≤ (U : ℝ)^2 := by nlinarith only [hUR, sq_nonneg ((U : ℝ) - 2)]
  have hinner : 2 + ((p - 1 : ℕ) : ℝ) * ((U : ℝ) + 1)^2 / 2 ≤
      9 / 8 * (d : ℝ) * (U : ℝ)^2 := by
    have hpc := mul_le_mul_of_nonneg_right hpminus (sq_nonneg ((U : ℝ) + 1))
    have hdq := mul_le_mul_of_nonneg_left hq (show 0 ≤ (d : ℝ) - 1 by linarith)
    nlinarith only [hpc, hdq, hU2]
  have htrans : transversalConstant p U ≤ 27 / 32 * (d : ℝ) * (U : ℝ)^4 := by
    unfold transversalConstant
    calc
      _ ≤ (3 / 4 * (U : ℝ)^2) * (9 / 8 * (d : ℝ) * (U : ℝ)^2) :=
        mul_le_mul hT hinner (by positivity) (by positivity)
      _ = _ := by ring
  have hp2 : (p : ℝ)^2 ≤ (d : ℝ)^2 := by gcongr
  have hm : 1 + (1 + 1 / (d : ℝ)) * (p : ℝ)^2 ≤ 9 / 8 * (d : ℝ)^2 := by
    have hmul := mul_le_mul_of_nonneg_left hp2 (show 0 ≤ 1 + 1 / (d : ℝ) by positivity)
    have he : (1 + 1 / (d : ℝ)) * (d : ℝ)^2 = (d : ℝ)^2 + d := by
      field_simp [ne_of_gt hd0]
    rw [he] at hmul
    nlinarith only [hmul, hdR, sq_nonneg ((d : ℝ) - 9)]
  have hrest : 1 + (d : ℝ) ≤ (d : ℝ)^2 := by nlinarith only [hdR, sq_nonneg ((d : ℝ) - 2)]
  have hU4 : (16 : ℝ) ≤ (U : ℝ)^4 := by nlinarith only [hU2, sq_nonneg ((U : ℝ)^2 - 4)]
  have hlarge : (128 : ℝ) ≤ (d : ℝ) * (U : ℝ)^4 := by
    nlinarith only [mul_le_mul_of_nonneg_left hU4 hd0.le, hdR]
  have hbudget : (d : ℝ)^2 ≤ (d : ℝ)^3 * (U : ℝ)^4 / 128 := by
    have h := mul_le_mul_of_nonneg_left hlarge (sq_nonneg (d : ℝ))
    nlinarith only [h]
  calc
    refinedConstant p U ≤ (1 + (1 + 1 / (d : ℝ)) * (p : ℝ)^2) *
        transversalConstant p U + 1 + d :=
      sqrt_coefficient_le_young _ _ _ (sq_nonneg _) (transversalConstant_nonnegative p U) hd0
    _ ≤ (9 / 8 * (d : ℝ)^2) * (27 / 32 * (d : ℝ) * (U : ℝ)^4) + (d : ℝ)^2 := by
      have h := mul_le_mul hm htrans (transversalConstant_nonnegative p U) (by positivity)
      linarith only [h, hrest]
    _ ≤ (d : ℝ)^3 * (U : ℝ)^4 := by
      nlinarith only [hbudget, (show 0 ≤ (d : ℝ)^3 * (U : ℝ)^4 by positivity)]

/-- The original dyadic proposal contributes the unchanged reciprocal
budget 64*d^2. -/
theorem refinedProposal_budget (p d U : ℕ)
    (hd : 11 ≤ d) (hU : 2 ≤ U) (hp : p ≤ d) :
    refinedConstant p U / smallProposal d ≤ 64 * (d : ℝ)^5 * (U : ℝ)^4 := by
  have hproposal := smallProposal_bounds d (show 1 ≤ d by omega)
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hrecip : 1 / smallProposal d ≤ 64 * (d : ℝ)^2 := by
    apply (div_le_iff₀ hproposal.1).mpr
    have h := (div_le_iff₀ (show (0 : ℝ) < 64 * (d : ℝ)^2 by positivity)).mp hproposal.2.1
    nlinarith only [h]
  calc
    _ = refinedConstant p U * (1 / smallProposal d) := by ring
    _ ≤ refinedConstant p U * (64 * (d : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hrecip (refinedConstant_nonnegative p U)
    _ ≤ ((d : ℝ)^3 * (U : ℝ)^4) * (64 * (d : ℝ)^2) :=
      mul_le_mul_of_nonneg_right (refinedConstant_le_polynomial p d U hd hU hp) (by positivity)
    _ = _ := by ring

theorem refinedReferenceProposal_budget (p d U : ℕ)
    (hd : 11 ≤ d) (hU : 2 ≤ U) (hp : p ≤ d) :
    2 * refinedConstant p U / smallProposal d ≤ 128 * (d : ℝ)^5 * (U : ℝ)^4 := by
  have h := mul_le_mul_of_nonneg_left (refinedProposal_budget p d U hd hU hp)
    (show (0 : ℝ) ≤ 2 by norm_num)
  convert h using 1 <;> ring

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The same actual repairWord, defectLabels, capacities, and graph energy
now give the defect-side square-root coefficient. -/
theorem physical_full_variance_refined
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hU : 2 ≤ U)
    (hB : ∀ i j, firstPaperSmall r c U i j = true → B i j = U)
    (hlarge : ∀ i j, firstPaperSmall r c U i j = false → 2 ≤ B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i + rowLargeCount (firstPaperSmall r c U) i * L)
      (fun j => c j + columnLargeCount (firstPaperSmall r c U) j * L),
      ∀ i j, T.val.val i j ≤ B i j)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    let small := firstPaperSmall r c U
    let w := wordWeight small B r c L U
    let v := fun z : PositiveDefects small B r c L => hardMarginal small B r c L (naturalProfile z.val)
    let G := wordObservable small U H
    let K := fun z : PositiveDefects small B r c L => H (naturalProfile z.val)
    variance (Sum.elim w v) (Sum.elim G K) ≤
      refinedConstant (Fintype.card (Cells small)) U * fullEnergy r c U L B hB H := by
  dsimp only
  let small := firstPaperSmall r c U
  let p := Fintype.card (Cells small)
  let E := fullEnergy r c U L B hB H
  have hvar : variance (wordWeight small B r c L U) (wordObservable small U H) ≤
      transversalConstant p U * E := by
    exact (physical_transversal_variance_localized small B r c L U hU hB hlarge hcap H).trans
      (mul_le_mul_of_nonneg_left (physicalEnergy_le_full r c U L B hB H)
        (transversalConstant_nonnegative p U))
  have hrepair := actual_repair_energy_le r c U L B hB hcap H
  have hv := RepairVarianceRefinement.variance_repaired_energy_sqrt
    (wordWeight small B r c L U)
    (fun z : PositiveDefects small B r c L => hardMarginal small B r c L (naturalProfile z.val))
    (wordObservable small U H) (fun z => H (naturalProfile z.val))
    (repairWord r c U L B hB) (defectLabels small B r c L)
    (fun a => hardMarginal_nonnegative _ _ _ _ _ _) (fun z => le_of_lt z.property.2)
    (repairWord_weight r c U L B hB hcap) (repairWord_type_injective r c U L B hB)
    (transversalConstant p U) E (transversalConstant_nonnegative p U)
    (fullEnergy_nonnegative r c U L B hB H) hvar hrepair
  have hcard : (Fintype.card (Cells small × Cells small) : ℝ) = (p : ℝ)^2 := by
    simp only [Fintype.card_prod, Nat.cast_mul, p, pow_two]
  rw [hcard] at hv
  exact hv

/-- The unchanged positive-support and encoding identities transfer the
refinement to every observable on actual physical states. -/
theorem physical_variance_refined
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hU : 2 ≤ U)
    (hB : ∀ i j, firstPaperSmall r c U i j = true → B i j = U)
    (hlarge : ∀ i j, firstPaperSmall r c U i j = false → 2 ≤ B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i + rowLargeCount (firstPaperSmall r c U) i * L)
      (fun j => c j + columnLargeCount (firstPaperSmall r c U) j * L),
      ∀ i j, T.val.val i j ≤ B i j)
    (H : PhysicalStates (firstPaperSmall r c U) B r c L → ℝ) :
    let small := firstPaperSmall r c U
    variance (fun z => hardMarginal small B r c L (physicalProfile small B r c L z)) H ≤
      refinedConstant (Fintype.card (Cells small)) U *
        fullEnergy r c U L B hB (physicalExtension small B r c L H) := by
  dsimp only
  let small := firstPaperSmall r c U
  let G := physicalExtension small B r c L H
  have hext : ∀ z : PhysicalStates small B r c L, G (naturalProfile z.val.val) = H z :=
    physicalExtension_at small B r c L H
  have hv := variance_positive_support
    (fun z : Profiles small B => hardMarginal small B r c L (naturalProfile z.val))
    (fun z => G (naturalProfile z.val)) (fun _ => hardMarginal_nonnegative _ _ _ _ _ _)
  have hv' : variance (fun z : PhysicalStates small B r c L =>
      hardMarginal small B r c L (physicalProfile small B r c L z)) H =
      variance (fun z : Profiles small B => hardMarginal small B r c L (naturalProfile z.val))
        (fun z => G (naturalProfile z.val)) := by
    simpa only [physicalProfile, hext] using hv
  rw [hv', ← encoding_variance_eq small B r c L U hB G]
  exact physical_full_variance_refined r c U L B hU hB hlarge hcap G

theorem state_variance_refined (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hU : 2 ≤ U) (H : States r c U L → ℝ) :
    variance (weight r c U L) H ≤
      refinedConstant (Fintype.card (Cells (firstPaperSmall r c U))) U * graphEnergy r c U L H := by
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
  exact physical_variance_refined r c U L B hU (capacity_small r c U L) hlarge hcap H

theorem chain_poincare_exact_refined (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (hU : 2 ≤ U) (hL : 3 * dimensionAllowance (I := I) (J := J) ≤ L)
    (H : States r c U L → ℝ) :
    (chain r c U L i₀ j₀).variance H ≤
      (2 * refinedConstant (Fintype.card (Cells (firstPaperSmall r c U))) U /
        smallProposal (dimensionAllowance (I := I) (J := J))) *
      (chain r c U L i₀ j₀).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  exact chain_poincare_of_weighted_graph (chain r c U L i₀ j₀) (weight r c U L) H
    (weight_positive r c U L) (chain_pi r c U L i₀ j₀) (graphEnergy r c U L H)
    (refinedConstant (Fintype.card (Cells (firstPaperSmall r c U))) U) (smallProposal d)
    (refinedConstant_nonnegative _ _) (smallProposal_bounds d (by dsimp [d, dimensionAllowance]; omega)).1
    (state_variance_refined r c U L hU H) (chain_energy_lower r c U L i₀ j₀ hL H)

theorem unitChain_poincare_exact_refined (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)]
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U))
    (hU : 2 ≤ U) (H : States r c U L → ℝ) :
    (unitChain r c U L).variance H ≤
      (refinedConstant (Fintype.card (Cells (firstPaperSmall r c U))) U /
        smallProposal (dimensionAllowance (I := I) (J := J))) * (unitChain r c U L).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  let K := refinedConstant (Fintype.card (Cells (firstPaperSmall r c U))) U
  have hβ := (smallProposal_bounds d (by dsimp [d, dimensionAllowance]; omega)).1
  have hZ : 0 < ∑ z : States r c U L, weight r c U L z :=
    Finset.sum_pos (fun z _ => weight_positive r c U L z) Finset.univ_nonempty
  have hv : variance (weight r c U L) H ≤ K * graphEnergy r c U L H :=
    state_variance_refined r c U L hU H
  rw [chain_variance_eq (unitChain r c U L) (weight r c U L) H
    (unitChain_pi_weight r c U L hempty)]
  calc
    _ ≤ (K * graphEnergy r c U L H) / (∑ z, weight r c U L z) :=
      div_le_div_of_nonneg_right hv hZ.le
    _ = (K / smallProposal d) * (unitChain r c U L).energy H := by
      rw [unitChain_energy r c U L hempty H]
      field_simp [ne_of_gt hβ, ne_of_gt hZ]
      ring

theorem selectedChain_poincare_exact_refined (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (hU : 2 ≤ U)
    (hL : 3 * dimensionAllowance (I := I) (J := J) ≤ L) (H : States r c U L → ℝ) :
    (selectedChain r c U L).variance H ≤
      (2 * refinedConstant (Fintype.card (Cells (firstPaperSmall r c U))) U /
        smallProposal (dimensionAllowance (I := I) (J := J))) *
      (selectedChain r c U L).energy H := by
  unfold selectedChain
  split_ifs with h
  · exact chain_poincare_exact_refined r c U L (Classical.choice h.1) (Classical.choice h.2) hU hL H
  · have hu := unitChain_poincare_exact_refined r c U L (missing_reference_empty r c U h) hU H
    have hb := (smallProposal_bounds (dimensionAllowance (I := I) (J := J))
      (by unfold dimensionAllowance; omega)).1
    have hn : 0 ≤ refinedConstant (Fintype.card (Cells (firstPaperSmall r c U))) U /
        smallProposal (dimensionAllowance (I := I) (J := J)) :=
      div_nonneg (refinedConstant_nonnegative _ _) hb.le
    exact hu.trans (mul_le_mul_of_nonneg_right (by
      rw [mul_div_assoc]
      linarith only [hn])
      ((unitChain r c U L).energy_nonneg H))

omit [LinearOrder I] [LinearOrder J] in
/-- Actual allowance is at least eleven even when an index type is empty. -/
lemma dimension_at_least_eleven : 11 ≤ dimensionAllowance (I := I) (J := J) := by
  unfold dimensionAllowance
  have hi : 1 ≤ Fintype.card I + 1 := by omega
  have hj : 1 ≤ Fintype.card J + 1 := by omega
  have hm := Nat.mul_le_mul hi hj
  omega

/-- Sharper coefficient for the existing actual reference chain. -/
theorem chain_poincare_polynomial_refined (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (hU : 2 ≤ U) (hL : 3 * dimensionAllowance (I := I) (J := J) ≤ L)
    (H : States r c U L → ℝ) :
    (chain r c U L i₀ j₀).variance H ≤
      (128 * (dimensionAllowance (I := I) (J := J) : ℝ)^5 * (U : ℝ)^4) *
        (chain r c U L i₀ j₀).energy H := by
  have hp : Fintype.card (Cells (firstPaperSmall r c U)) ≤ dimensionAllowance (I := I) (J := J) :=
    (small_card_le_dimension (firstPaperSmall r c U)).trans dimension_le_allowance
  exact (chain_poincare_exact_refined r c U L i₀ j₀ hU hL H).trans
    (mul_le_mul_of_nonneg_right (refinedReferenceProposal_budget _ _ U
      dimension_at_least_eleven hU hp) ((chain r c U L i₀ j₀).energy_nonneg H))

/-- The empty-completion branch retains its stronger factor-one coefficient. -/
theorem unitChain_poincare_polynomial_refined (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)]
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U))
    (hU : 2 ≤ U) (H : States r c U L → ℝ) :
    (unitChain r c U L).variance H ≤
      (64 * (dimensionAllowance (I := I) (J := J) : ℝ)^5 * (U : ℝ)^4) *
        (unitChain r c U L).energy H := by
  have hp : Fintype.card (Cells (firstPaperSmall r c U)) ≤ dimensionAllowance (I := I) (J := J) :=
    (small_card_le_dimension (firstPaperSmall r c U)).trans dimension_le_allowance
  exact (unitChain_poincare_exact_refined r c U L hempty hU H).trans
    (mul_le_mul_of_nonneg_right (refinedProposal_budget _ _ U
      dimension_at_least_eleven hU hp) ((unitChain r c U L).energy_nonneg H))

/-- A single existing selector covers every margin shape. -/
theorem selectedChain_poincare_polynomial_refined (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (hU : 2 ≤ U)
    (hL : 3 * dimensionAllowance (I := I) (J := J) ≤ L) (H : States r c U L → ℝ) :
    (selectedChain r c U L).variance H ≤
      (128 * (dimensionAllowance (I := I) (J := J) : ℝ)^5 * (U : ℝ)^4) *
        (selectedChain r c U L).energy H := by
  have hp : Fintype.card (Cells (firstPaperSmall r c U)) ≤ dimensionAllowance (I := I) (J := J) :=
    (small_card_le_dimension (firstPaperSmall r c U)).trans dimension_le_allowance
  exact (selectedChain_poincare_exact_refined r c U L hU hL H).trans
    (mul_le_mul_of_nonneg_right (refinedReferenceProposal_budget _ _ U
      dimension_at_least_eleven hU hp) ((selectedChain r c U L).energy_nonneg H))

end Math115.PhysicalRepairRefinement
