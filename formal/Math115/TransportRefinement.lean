/-
SPDX-License-Identifier: Apache-2.0
Adapted from OpenAI's IntegerRootTransport.lean at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; source remains unchanged upstream.
Changes: quarter-sized correction bound and an exported leaf-energy bound.
-/
import OAI.Combinatorics.ContingencyTables.Transport.IntegerRootTransport
import Math115.QuadraticCoefficient

/-!
# A sharper and localized integer root transport bound

The original proof bounds `a * (M - a)` by `(W + 1)^2` when `M ≤ W + 1`.
Completing the square improves that coefficient by a factor of four.  The
recursive transport inequality also retains its actual leaf energy, so there
is no need to enlarge to the full exchange graph at this stage.

All definitions and hypotheses below come from the pinned upstream #115
formalization.  Theorems are additive: the original statements are unchanged.
-/

namespace OAI.ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open FactorialSignatures BalancedFamily BalancedEnumeration IntegerMarginal

universe u

/-- The exact quadratic maximum before applying the common width bound. -/
lemma weightedFuture_upper_quadratic {I : Type u}
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (M : ℕ)
    (hF : ∀ x, 0 ≤ F x) (z : I → ℕ) :
    weightedFuture F M z ≤ ((M : ℝ)^2 / 4) * marginal F M z := by
  unfold weightedFuture marginal
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_right _ (hF _)
  exact Math115.pair_product_le_quarter_square (a : ℝ) (M : ℝ)

/-- The upstream `weightedFuture_upper` coefficient divided by four. -/
lemma weightedFuture_upper_quarter {I : Type u}
    (F : ((I ⊕ Bool) → ℕ) → ℝ) (M W : ℕ) (hM : M ≤ W + 1)
    (hF : ∀ x, 0 ≤ F x) (z : I → ℕ) :
    weightedFuture F M z ≤ (((W : ℝ) + 1)^2 / 4) * marginal F M z := by
  apply (weightedFuture_upper_quadratic F M hF z).trans
  apply mul_le_mul_of_nonneg_right
  · have hMR : (M : ℝ) ≤ (W : ℝ) + 1 := by exact_mod_cast hM
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    nlinarith
  · exact Finset.sum_nonneg (fun _ _ => hF _)

theorem correctionKernel_upper_quarter {I : Type u} (Ms : List ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (W : ℕ)
    (hwidth : ∀ U ∈ Ms, U ≤ W) (hF : ∀ x, 0 ≤ F x) (z : I → ℕ) :
    correctionKernel Ms F z ≤ (((W : ℝ) + 1)^2 / 4) * auxiliaryKernel Ms F z := by
  induction Ms with
  | nil => simp [correctionKernel, auxiliaryKernel]
  | cons U Ms ih =>
    have hcur := weightedFuture_upper_quarter (exposedFamily Ms F) (U + 1) W
      (by have := hwidth U (by simp); omega)
      (fun x => eliminate_nonnegative Ms _ (fun p => hF _) _) z
    have htail := ih (marginal F U) (fun V hV => hwidth V (by simp [hV]))
      (fun x => Finset.sum_nonneg (fun j _ => hF _))
    change _ + _ ≤ (((W : ℝ) + 1)^2 / 4) * (_ + _)
    linarith

lemma correction_offdiagonal_upper_quarter (Ms : List ℕ)
    (F : (Coordinates Bool Ms → ℕ) → ℝ) (W : ℕ)
    (hwidth : ∀ U ∈ Ms, U ≤ W) (hF : ∀ x, 0 ≤ F x) (z : Bool → ℕ) :
    integerRemovalMatrix (correctionKernel Ms F) z false true ≤
      (((W : ℝ) + 1)^2 / 4) *
        integerRemovalMatrix (auxiliaryKernel Ms F) z false true := by
  unfold integerRemovalMatrix
  split_ifs
  · exact correctionKernel_upper_quarter Ms F W hwidth hF _
  · simp

/-- The auxiliary-defect term has one quarter of the original coefficient. -/
theorem recursive_root_potential_quarter (Ms : List ℕ)
    (F : (Coordinates Bool Ms → ℕ) → ℝ) (m z : Bool → ℕ) (R W : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hF : ∀ x, 0 ≤ F x)
    (hpos : BalancedBox.PositiveSlice F (bounds m Ms) (R + Ms.sum))
    (hsig : BalancedBox.RemovalSlice F (bounds m Ms) (R + Ms.sum))
    (hz : BalancedBox.InBox m z) (htotal : (∑ i, z i) = R + 1)
    (hs : 0 < oneHole (eliminate Ms F) z false)
    (ht : 0 < oneHole (eliminate Ms F) z true) :
    let s := oneHole (eliminate Ms F) z false
    let t := oneHole (eliminate Ms F) z true
    let c := integerRemovalMatrix (auxiliaryKernel Ms F) z false true
    recursivePotential Ms F z (rootCoefficients s t) ≤
      1 / s + 1 / t + (((W : ℝ) + 1)^2 / 2) * c / (s * t) := by
  dsimp only
  have hp := recursivePotential_bound Ms F m z R
    (rootCoefficients _ _) hlower hF hpos hsig hz htotal (root_balance _ _ hs ht)
  rw [root_holePotential _ _ hs ht] at hp
  have hq := root_future_bound (integerRemovalMatrix (correctionKernel Ms F) z)
    (oneHole (eliminate Ms F) z false) (oneHole (eliminate Ms F) z true)
    ((((W : ℝ) + 1)^2) / 4)
    (integerRemovalMatrix (auxiliaryKernel Ms F) z false true)
    hs ht (integerRemoval_symm _ _ _ _)
    (removal_nonnegative _ (correctionKernel_nonnegative Ms F hF) _ _ _)
    (removal_nonnegative _ (correctionKernel_nonnegative Ms F hF) _ _ _)
    (correction_offdiagonal_upper_quarter Ms F W hupper hF z)
  have hscale : (2 : ℝ) * (((W : ℝ) + 1)^2 / 4) = ((W : ℝ) + 1)^2 / 2 := by ring
  rw [hscale] at hq
  linarith

/-- A localized root bound: keep the exact leaf energy for later ownership
arguments instead of charging this contrast to every graph edge. -/
theorem integer_root_leaf_transport_quarter (Ms : List ℕ)
    (F H : (Coordinates Bool Ms → ℕ) → ℝ) (m z : Bool → ℕ) (R W : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hF : ∀ x, 0 ≤ F x)
    (hpos : BalancedBox.PositiveSlice F (bounds m Ms) (R + Ms.sum))
    (hsig : BalancedBox.RemovalSlice F (bounds m Ms) (R + Ms.sum))
    (hz : BalancedBox.InBox m z) (htotal : (∑ i, z i) = R + 1)
    (hs : 0 < oneHole (eliminate Ms F) z false)
    (ht : 0 < oneHole (eliminate Ms F) z true) :
    let s := oneHole (eliminate Ms F) z false
    let t := oneHole (eliminate Ms F) z true
    let c := integerRemovalMatrix (auxiliaryKernel Ms F) z false true
    (holeLinear (eliminate Ms (fun p => F p * H p)) z (rootCoefficients s t))^2 ≤
      (1 / s + 1 / t + (((W : ℝ) + 1)^2 / 2) * c / (s * t)) *
        leafEnergySum Ms F H z := by
  dsimp only
  have hp := recursive_root_potential_quarter Ms F m z R W
    hlower hupper hF hpos hsig hz htotal hs ht
  have hb := integer_recursive_transport_of_slice Ms F H m z R (rootCoefficients _ _)
    hF hpos hz htotal (root_balance _ _ hs ht)
  have hen := recursiveEnergy_nonnegative Ms F H z (rootCoefficients
    (oneHole (eliminate Ms F) z false) (oneHole (eliminate Ms F) z true)) hF
  have h := hb.trans (mul_le_mul_of_nonneg_right hp hen)
  simpa only [recursiveEnergy_eq_leafEnergySum] using h

/-- The original graph-energy interface with the sharper coefficient. -/
theorem integer_root_graph_transport_quarter (Ms : List ℕ)
    (F H : (Coordinates Bool Ms → ℕ) → ℝ) (m z : Bool → ℕ) (R W : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hF : ∀ x, 0 ≤ F x)
    (hpos : BalancedBox.PositiveSlice F (bounds m Ms) (R + Ms.sum))
    (hsig : BalancedBox.RemovalSlice F (bounds m Ms) (R + Ms.sum))
    (hz : BalancedBox.InBox m z) (htotal : (∑ i, z i) = R + 1)
    (hs : 0 < oneHole (eliminate Ms F) z false)
    (ht : 0 < oneHole (eliminate Ms F) z true)
    (V : Finset (Coordinates Bool Ms → ℕ)) (hV : leafVertices Ms z ⊆ V) :
    let s := oneHole (eliminate Ms F) z false
    let t := oneHole (eliminate Ms F) z true
    let c := integerRemovalMatrix (auxiliaryKernel Ms F) z false true
    (holeLinear (eliminate Ms (fun p => F p * H p)) z (rootCoefficients s t))^2 ≤
      (1 / s + 1 / t + (((W : ℝ) + 1)^2 / 2) * c / (s * t)) *
        integerGraphEnergy V F H := by
  dsimp only
  have hp := recursive_root_potential_quarter Ms F m z R W
    hlower hupper hF hpos hsig hz htotal hs ht
  have hb := integer_root_leaf_transport_quarter Ms F H m z R W
    hlower hupper hF hpos hsig hz htotal hs ht
  have he := leafEnergySum_le_graphEnergy Ms F H z hF V hV
  have hpn := recursivePotential_nonnegative Ms F z (rootCoefficients
    (oneHole (eliminate Ms F) z false) (oneHole (eliminate Ms F) z true)) hF
  exact hb.trans (mul_le_mul_of_nonneg_left he (hpn.trans hp))

end OAI.ContingencyTables.IntegerWeightedTransport
