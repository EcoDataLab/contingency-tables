/-
SPDX-License-Identifier: Apache-2.0
Refined repair constants for the unchanged dense-compatible U=47*d^5,L=32*d^3
scales. These are ideal-chain Poincare certificates, not runtime theorems.
-/
import Math115.PhysicalRepairRefinement
import Math115.PhysicalStateNonempty

namespace Math115.ReducedRepairRefinement

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open CompletionCounts SmallGraphProfiles ReducedSmallChain ReducedAllSmallChain
open scoped BigOperators Classical

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

theorem reducedChain_poincare_d25_refined (r : I → ℕ) (c : J → ℕ) [Nonempty (ReducedStates r c)]
    (i₀ : LargeRows r (reducedU (I := I) (J := J)))
    (j₀ : LargeColumns c (reducedU (I := I) (J := J))) (H : ReducedStates r c → ℝ) :
    (reducedChain r c i₀ j₀).variance H ≤
      ((128 * 47^4 : ℝ) * (dimensionAllowance (I := I) (J := J) : ℝ)^25) *
        (reducedChain r c i₀ j₀).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  have hd : 1 ≤ d := by dsimp [d, dimensionAllowance]; omega
  have hd3 : d ≤ d^3 := Nat.le_self_pow (by decide) d
  have hd5 : d ≤ d^5 := Nat.le_self_pow (by decide) d
  have hU : 2 ≤ 47 * d^5 := by omega
  have hL : 3 * d ≤ 32 * d^3 := by omega
  have h := PhysicalRepairRefinement.chain_poincare_polynomial_refined r c (47 * d^5) (32 * d^3) i₀ j₀ hU hL H
  change (chain r c (47 * d^5) (32 * d^3) i₀ j₀).variance H ≤
    ((128 * 47^4 : ℝ) * (d : ℝ)^25) * (chain r c (47 * d^5) (32 * d^3) i₀ j₀).energy H
  convert h using 1
  push_cast
  ring

theorem reducedUnitChain_poincare_d25_refined (r : I → ℕ) (c : J → ℕ)
    [Nonempty (ReducedStates r c)]
    (hempty : IsEmpty (LargeRows r (reducedU (I := I) (J := J))) ∨
      IsEmpty (LargeColumns c (reducedU (I := I) (J := J)))) (H : ReducedStates r c → ℝ) :
    (reducedUnitChain r c).variance H ≤
      ((64 * 47^4 : ℝ) * (dimensionAllowance (I := I) (J := J) : ℝ)^25) *
        (reducedUnitChain r c).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  have hd : 1 ≤ d := by dsimp [d, dimensionAllowance]; omega
  have hd5 : d ≤ d^5 := Nat.le_self_pow (by decide) d
  have hU : 2 ≤ 47 * d^5 := by omega
  have h := PhysicalRepairRefinement.unitChain_poincare_polynomial_refined r c (47 * d^5) (32 * d^3) hempty hU H
  change (unitChain r c (47 * d^5) (32 * d^3)).variance H ≤
    ((64 * 47^4 : ℝ) * (d : ℝ)^25) * (unitChain r c (47 * d^5) (32 * d^3)).energy H
  convert h using 1
  push_cast
  ring

theorem reducedSelectedChain_poincare_d25_refined (r : I → ℕ) (c : J → ℕ)
    [Nonempty (ReducedStates r c)] (H : ReducedStates r c → ℝ) :
    (reducedSelectedChain r c).variance H ≤
      ((128 * 47^4 : ℝ) * (dimensionAllowance (I := I) (J := J) : ℝ)^25) *
        (reducedSelectedChain r c).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  have hd : 1 ≤ d := by dsimp [d, dimensionAllowance]; omega
  have hd3 : d ≤ d^3 := Nat.le_self_pow (by decide) d
  have hd5 : d ≤ d^5 := Nat.le_self_pow (by decide) d
  have hU : 2 ≤ 47 * d^5 := by omega
  have hL : 3 * d ≤ 32 * d^3 := by omega
  have h := PhysicalRepairRefinement.selectedChain_poincare_polynomial_refined r c (47 * d^5) (32 * d^3) hU hL H
  change (selectedChain r c (47 * d^5) (32 * d^3)).variance H ≤
    ((128 * 47^4 : ℝ) * (d : ℝ)^25) * (selectedChain r c (47 * d^5) (32 * d^3)).energy H
  convert h using 1
  push_cast
  ring

theorem feasibleReducedChain_poincare_d25_refined (r : I → ℕ) (c : J → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (H : ReducedStates r c → ℝ) :
    (PhysicalStateNonempty.feasibleReducedChain r c htotal).variance H ≤
      ((128 * 47^4 : ℝ) * (dimensionAllowance (I := I) (J := J) : ℝ)^25) *
        (PhysicalStateNonempty.feasibleReducedChain r c htotal).energy H := by
  letI := PhysicalStateNonempty.states_nonempty r c (reducedU (I := I) (J := J))
    (reducedL (I := I) (J := J)) htotal
  exact reducedSelectedChain_poincare_d25_refined r c H

end Math115.ReducedRepairRefinement
