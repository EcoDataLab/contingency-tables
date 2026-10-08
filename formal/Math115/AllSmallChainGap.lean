/-
SPDX-License-Identifier: Apache-2.0
Localized Poincare comparison for the original all-small ideal chain.
-/
import Math115.SmallChainGap
import OAI.Combinatorics.ContingencyTables.Sampling.AllSmallChain

namespace Math115.SmallChainGap

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open PhysicalFullVariance
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts SmallContextCoordinates SmallContextFibres
open SmallContextEnumeration RowMajorEnumeration
open SmallGraphProfiles FiniteExposureVariance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- With no dense completion block, the source unit-chain energy identity
removes the extra factor two from the acceptance comparison. -/
theorem unitSmallChain_poincare_exact (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (hsmall : ∀ i j, paperSmall r c i j = true) (H : PaperStates r c → ℝ) :
    let d := dimensionAllowance (I := I) (J := J)
    (unitSmallChain r c).variance H ≤
      (fullConstant (Fintype.card (Cells (paperSmall r c))) (d^20) / smallProposal d) *
        (unitSmallChain r c).energy H := by
  dsimp only
  let d := dimensionAllowance (I := I) (J := J)
  let K := fullConstant (Fintype.card (Cells (paperSmall r c))) (d^20)
  have hβ := (smallProposal_bounds d (by dsimp only [d]; unfold dimensionAllowance; omega)).1
  have hZ : 0 < ∑ z : PaperStates r c, stateWeight r c z :=
    Finset.sum_pos (fun z _ => stateWeight_positive r c z) Finset.univ_nonempty
  have hv : variance (stateWeight r c) H ≤ K * stateGraphEnergy r c H :=
    paper_state_variance_localized r c H
  have hsum : (∑ z : PaperStates r c, stateWeight r c z) =
      (Fintype.card (PaperStates r c) : ℝ) := by
    simp only [stateWeight_allSmall r c hsmall, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
  have hE := unitSmallChain_energy r c H
  rw [← stateGraphEnergy_allSmall r c hsmall H, ← hsum] at hE
  rw [chain_variance_eq (unitSmallChain r c) (stateWeight r c) H
    (unitSmallChain_pi_weight r c hsmall)]
  calc
    _ ≤ (K * stateGraphEnergy r c H) / (∑ z, stateWeight r c z) :=
      div_le_div_of_nonneg_right hv hZ.le
    _ = (K / smallProposal d) * (unitSmallChain r c).energy H := by
      rw [hE]
      field_simp [ne_of_gt hβ, ne_of_gt hZ]
      ring

/-- The all-small original-scale branch has the stronger conservative
`512*d^85` bound, using its exact acceptance-one energy identity. -/
theorem unitSmallChain_poincare_d85 (r : I → ℕ) (c : J → ℕ) [Nonempty (PaperStates r c)]
    (hsmall : ∀ i j, paperSmall r c i j = true) (H : PaperStates r c → ℝ) :
    (unitSmallChain r c).variance H ≤
      (512 * (dimensionAllowance (I := I) (J := J) : ℝ)^85) * (unitSmallChain r c).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  let K := fullConstant (Fintype.card (Cells (paperSmall r c))) (d^20)
  have hd : 1 ≤ d := by dsimp only [d]; unfold dimensionAllowance; omega
  have hU : 1 ≤ d^20 := hd.trans (Nat.le_self_pow (by decide) d)
  have hp : Fintype.card (Cells (paperSmall r c)) ≤ d :=
    (small_card_le_dimension (paperSmall r c)).trans dimension_le_allowance
  have hbudget := smallProposal_localized_budget (Fintype.card (Cells (paperSmall r c))) d (d^20)
    hd hU hp
  have hcoef : K / smallProposal d ≤ 512 * (d : ℝ)^85 := by
    have hbudgetR : 2 * (K / smallProposal d) ≤ 1024 * (d : ℝ)^85 := by
      convert hbudget using 1 <;> push_cast <;> ring
    linarith only [hbudgetR]
  exact (unitSmallChain_poincare_exact r c hsmall H).trans
    (mul_le_mul_of_nonneg_right hcoef ((unitSmallChain r c).energy_nonneg H))

end Math115.SmallChainGap
