/-
SPDX-License-Identifier: Apache-2.0
Integration of localized physical variance with the original
small-chain stationary law and dyadic proposal comparison. The paper's
original U=d^20 scale remains separate from reduced-scale certificates.
-/
import Math115.PhysicalFullVariance
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperSmallChain

namespace Math115.SmallChainGap

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open PhysicalFullVariance
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts SmallContextCoordinates SmallContextFibres
open SmallContextEnumeration RowMajorEnumeration
open SmallGraphProfiles FiniteExposureVariance

/-- A conservative polynomial bound on the actual localized full-graph
coefficient, permitting no small cells (`p=0`). -/
theorem fullConstant_le_polynomial (p d U : ℕ)
    (hd : 1 ≤ d) (hU : 1 ≤ U) (hp : p ≤ d) :
    fullConstant p U ≤ 8 * (d : ℝ)^3 * (U : ℝ)^4 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hUR : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hpR : (p : ℝ) ≤ d := by exact_mod_cast hp
  have hpminus : ((p - 1 : ℕ) : ℝ) ≤ (d : ℝ) - 1 := by
    have h : ((p - 1 : ℕ) : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.sub_le_sub_right hp 1
    simpa only [Nat.cast_sub hd, Nat.cast_one] using h
  have hT : (U : ℝ) * ((U : ℝ) + 1) / 2 ≤ (U : ℝ)^2 := by
    nlinarith [sq_nonneg ((U : ℝ) - 1)]
  have hq : ((U : ℝ) + 1)^2 ≤ 4 * (U : ℝ)^2 := by
    nlinarith [sq_nonneg ((U : ℝ) - 1)]
  have hU2 : (1 : ℝ) ≤ (U : ℝ)^2 := one_le_pow₀ hUR
  have hinner : 2 + ((p - 1 : ℕ) : ℝ) * ((U : ℝ) + 1)^2 / 2 ≤
      2 * (d : ℝ) * (U : ℝ)^2 := by
    have hpc := mul_le_mul_of_nonneg_right hpminus (sq_nonneg ((U : ℝ) + 1))
    have hdq := mul_le_mul_of_nonneg_left hq (sub_nonneg.mpr hdR)
    nlinarith only [hpc, hdq, hU2]
  have htrans : transversalConstant p U ≤ 2 * (d : ℝ) * (U : ℝ)^4 := by
    unfold transversalConstant
    calc
      _ ≤ (U : ℝ)^2 * (2 * (d : ℝ) * (U : ℝ)^2) :=
        mul_le_mul hT hinner (by positivity) (sq_nonneg _)
      _ = _ := by ring
  have hp2 : (p : ℝ)^2 ≤ (d : ℝ)^2 := by gcongr
  have hrepair : 1 + 2 * (p : ℝ)^2 ≤ 3 * (d : ℝ)^2 := by
    nlinarith only [hp2, (one_le_pow₀ hdR : (1 : ℝ) ≤ (d : ℝ)^2)]
  have hunit : (1 : ℝ) ≤ (d : ℝ)^3 * (U : ℝ)^4 := by
    simpa using mul_le_mul (one_le_pow₀ hdR : (1 : ℝ) ≤ (d : ℝ)^3)
      (one_le_pow₀ hUR : (1 : ℝ) ≤ (U : ℝ)^4) zero_le_one (by positivity)
  unfold fullConstant
  calc
    _ ≤ 3 * (d : ℝ)^2 * (2 * (d : ℝ) * (U : ℝ)^4) + 2 := by
      exact add_le_add
        (mul_le_mul hrepair htrans (transversalConstant_nonnegative p U) (by positivity)) (le_refl 2)
    _ ≤ _ := by nlinarith only [hunit]

/-- The source's unchanged dyadic proposal adds a factor at most `128*d^2`. -/
theorem smallProposal_localized_budget (p d U : ℕ)
    (hd : 1 ≤ d) (hU : 1 ≤ U) (hp : p ≤ d) :
    2 * fullConstant p U / smallProposal d ≤ 1024 * (d : ℝ)^5 * (U : ℝ)^4 := by
  have hproposal := smallProposal_bounds d hd
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hrecip : 1 / smallProposal d ≤ 64 * (d : ℝ)^2 := by
    apply (div_le_iff₀ hproposal.1).mpr
    have h := (div_le_iff₀ (show (0 : ℝ) < 64 * (d : ℝ)^2 by positivity)).mp hproposal.2.1
    nlinarith only [h]
  calc
    _ = (2 * fullConstant p U) * (1 / smallProposal d) := by ring
    _ ≤ (2 * fullConstant p U) * (64 * (d : ℝ)^2) :=
      mul_le_mul_of_nonneg_left hrecip
        (mul_nonneg (by norm_num) (fullConstant_nonnegative p U))
    _ = 128 * (d : ℝ)^2 * fullConstant p U := by ring
    _ ≤ 128 * (d : ℝ)^2 * (8 * (d : ℝ)^3 * (U : ℝ)^4) :=
      mul_le_mul_of_nonneg_left (fullConstant_le_polynomial p d U hd hU hp) (by positivity)
    _ = _ := by ring

/-- Normalize a localized weighted-graph estimate for a chain with the
source stationary weights and proposal comparison. -/
theorem chain_poincare_localized {X : Type*} [Fintype X] [Nonempty X]
    (C : FiniteChain X) (w H : X → ℝ) (E : ℝ) (p d U : ℕ)
    (hd : 1 ≤ d) (hU : 1 ≤ U) (hp : p ≤ d)
    (hw : ∀ x, 0 < w x) (hπ : ∀ x, C.π x = w x / (∑ y, w y))
    (hv : variance w H ≤ fullConstant p U * E)
    (he : smallProposal d / (2 * (∑ x, w x)) * E ≤ C.energy H) :
    C.variance H ≤ (1024 * (d : ℝ)^5 * (U : ℝ)^4) * C.energy H := by
  have h := chain_poincare_of_weighted_graph C w H hw hπ E (fullConstant p U)
    (smallProposal d) (fullConstant_nonnegative p U) (smallProposal_bounds d hd).1 hv he
  exact h.trans (mul_le_mul_of_nonneg_right (smallProposal_localized_budget p d U hd hU hp)
    (C.energy_nonneg H))

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- The original paper scales discharge every capacity and width premise of
the localized physical-variance theorem. -/
theorem paper_state_variance_localized (r : I → ℕ) (c : J → ℕ) (H : PaperStates r c → ℝ) :
    variance (stateWeight r c) H ≤
      fullConstant (Fintype.card (Cells (paperSmall r c)))
        ((dimensionAllowance (I := I) (J := J))^20) * stateGraphEnergy r c H := by
  let d := dimensionAllowance (I := I) (J := J)
  let U := d^20
  let L := d^12
  let B := stateCapacity r c
  have hd : 2 ≤ d := by dsimp only [d]; unfold dimensionAllowance; omega
  have hU : 2 ≤ U := hd.trans (Nat.le_self_pow (by decide) d)
  have hB : ∀ i j, firstPaperSmall r c U i j = true → B i j = U := stateCapacity_small r c
  have hlarge : ∀ i j, firstPaperSmall r c U i j = false → 2 ≤ B i j := by
    intro i j hij
    simp only [B, stateCapacity, paperCapacity, show paperSmall r c i j = false from hij,
      Bool.false_eq_true, ite_false]
    omega
  have hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i + rowLargeCount (firstPaperSmall r c U) i * L)
      (fun j => c j + columnLargeCount (firstPaperSmall r c U) j * L),
      ∀ i j, T.val.val i j ≤ B i j :=
    paper_residual_capacity r c d L U dimension_le_allowance
  exact physical_variance_localized r c U L B hU hB hlarge hcap H

/-- The exact sharpened Poincare constant for the unchanged ideal small
chain, retaining the actual number of small cells and dyadic proposal. -/
theorem paperSmallChain_poincare_exact (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (H : PaperStates r c → ℝ) :
    let d := dimensionAllowance (I := I) (J := J)
    (paperSmallChain r c i₀ j₀).variance H ≤
      (2 * fullConstant (Fintype.card (Cells (paperSmall r c))) (d^20) / smallProposal d) *
        (paperSmallChain r c i₀ j₀).energy H := by
  dsimp only
  let d := dimensionAllowance (I := I) (J := J)
  exact chain_poincare_of_weighted_graph (paperSmallChain r c i₀ j₀)
    (stateWeight r c) H (stateWeight_positive r c) (paperSmallChain_pi r c i₀ j₀)
    (stateGraphEnergy r c H) (fullConstant (Fintype.card (Cells (paperSmall r c))) (d^20))
    (smallProposal d) (fullConstant_nonnegative _ _)
    (smallProposal_bounds d (by dsimp only [d]; unfold dimensionAllowance; omega)).1
    (paper_state_variance_localized r c H) (paperSmallChain_energy_lower r c i₀ j₀ H)

/-- The literal original-scale chain satisfies the conservative `1024*d^85`
inverse-gap bound. This theorem does not substitute the proposed new scales. -/
theorem paperSmallChain_poincare_d85 (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (i₀ : LargeRows r ((dimensionAllowance (I := I) (J := J))^20))
    (j₀ : LargeColumns c ((dimensionAllowance (I := I) (J := J))^20))
    (H : PaperStates r c → ℝ) :
    (paperSmallChain r c i₀ j₀).variance H ≤
      (1024 * (dimensionAllowance (I := I) (J := J) : ℝ)^85) *
        (paperSmallChain r c i₀ j₀).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  change (paperSmallChain r c i₀ j₀).variance H ≤
    (1024 * (d : ℝ)^85) * (paperSmallChain r c i₀ j₀).energy H
  have hd : 1 ≤ d := by dsimp only [d]; unfold dimensionAllowance; omega
  have hU : 1 ≤ d^20 := hd.trans (Nat.le_self_pow (by decide) d)
  have hp : Fintype.card (Cells (paperSmall r c)) ≤ d :=
    (small_card_le_dimension (paperSmall r c)).trans dimension_le_allowance
  have h := chain_poincare_localized (paperSmallChain r c i₀ j₀)
    (stateWeight r c) H (stateGraphEnergy r c H) (Fintype.card (Cells (paperSmall r c))) d (d^20)
    hd hU hp (stateWeight_positive r c) (paperSmallChain_pi r c i₀ j₀)
    (paper_state_variance_localized r c H) (paperSmallChain_energy_lower r c i₀ j₀ H)
  convert h using 1
  push_cast
  ring

end Math115.SmallChainGap
