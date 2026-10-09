/-
SPDX-License-Identifier: Apache-2.0
Refined repair coefficients at the ideal-only U=5*d^3,L=3*d scales.
This changes no dense finite-bit compatibility or runtime claim.
-/
import Math115.PhysicalRepairRefinement
import Math115.IdealOracleScales

namespace Math115.IdealRepairRefinement

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open CompletionCounts SmallGraphProfiles Math115.IdealOracleScales
open scoped BigOperators Classical

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

theorem referenceChain_poincare_d17_refined (r : I → ℕ) (c : J → ℕ) [Nonempty (IdealStates r c)]
    (i₀ : LargeRows r (cutoff (I := I) (J := J)))
    (j₀ : LargeColumns c (cutoff (I := I) (J := J))) (H : IdealStates r c → ℝ) :
    (referenceChain r c i₀ j₀).variance H ≤
      ((128 * 5^4 : ℝ) * (dimensionAllowance (I := I) (J := J) : ℝ)^17) *
        (referenceChain r c i₀ j₀).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  have hd : 1 ≤ d := by dsimp [d, dimensionAllowance]; omega
  have h := PhysicalRepairRefinement.chain_poincare_polynomial_refined r c (idealU d) (idealL d) i₀ j₀
    (threshold_at_least_two d hd) (padding_at_least_three_dimension d) H
  change (ReducedSmallChain.chain r c (idealU d) (idealL d) i₀ j₀).variance H ≤
    ((128 * 5^4 : ℝ) * (d : ℝ)^17) *
      (ReducedSmallChain.chain r c (idealU d) (idealL d) i₀ j₀).energy H
  convert h using 1
  unfold idealU
  push_cast
  ring

theorem selectedChain_poincare_d17_refined (r : I → ℕ) (c : J → ℕ) [Nonempty (IdealStates r c)]
    (H : IdealStates r c → ℝ) :
    (selectedChain r c).variance H ≤
      ((128 * 5^4 : ℝ) * (dimensionAllowance (I := I) (J := J) : ℝ)^17) *
        (selectedChain r c).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  have hd : 1 ≤ d := by dsimp [d, dimensionAllowance]; omega
  have h := PhysicalRepairRefinement.selectedChain_poincare_polynomial_refined r c (idealU d) (idealL d)
    (threshold_at_least_two d hd) (padding_at_least_three_dimension d) H
  change (ReducedAllSmallChain.selectedChain r c (idealU d) (idealL d)).variance H ≤
    ((128 * 5^4 : ℝ) * (d : ℝ)^17) *
      (ReducedAllSmallChain.selectedChain r c (idealU d) (idealL d)).energy H
  convert h using 1
  unfold idealU
  push_cast
  ring

theorem feasibleChain_poincare_d17_refined (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (H : IdealStates r c → ℝ) :
    (feasibleChain r c htotal).variance H ≤
      ((128 * 5^4 : ℝ) * (dimensionAllowance (I := I) (J := J) : ℝ)^17) *
        (feasibleChain r c htotal).energy H := by
  letI := PhysicalStateNonempty.states_nonempty r c (cutoff (I := I) (J := J))
    (padding (I := I) (J := J)) htotal
  exact selectedChain_poincare_d17_refined r c H

/-- The actual unit branch at the same ideal-only scales has coefficient
40000*d^17, using its exact energy identity. -/
theorem unitChain_poincare_d17_refined (r : I → ℕ) (c : J → ℕ) [Nonempty (IdealStates r c)]
    (hempty : IsEmpty (LargeRows r (cutoff (I := I) (J := J))) ∨
      IsEmpty (LargeColumns c (cutoff (I := I) (J := J)))) (H : IdealStates r c → ℝ) :
    (ReducedAllSmallChain.unitChain r c (cutoff (I := I) (J := J))
      (padding (I := I) (J := J))).variance H ≤
      ((64 * 5^4 : ℝ) * (dimensionAllowance (I := I) (J := J) : ℝ)^17) *
        (ReducedAllSmallChain.unitChain r c (cutoff (I := I) (J := J))
          (padding (I := I) (J := J))).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  have hd : 1 ≤ d := by dsimp [d, dimensionAllowance]; omega
  have h := PhysicalRepairRefinement.unitChain_poincare_polynomial_refined r c
    (idealU d) (idealL d) hempty (threshold_at_least_two d hd) H
  change (ReducedAllSmallChain.unitChain r c (idealU d) (idealL d)).variance H ≤
    ((64 * 5^4 : ℝ) * (d : ℝ)^17) *
      (ReducedAllSmallChain.unitChain r c (idealU d) (idealL d)).energy H
  convert h using 1
  unfold idealU
  push_cast
  ring

end Math115.IdealRepairRefinement
