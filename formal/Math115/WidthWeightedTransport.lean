/-
SPDX-License-Identifier: Apache-2.0
Adapted from OpenAI's IntegerRootTransport.lean at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
Changes: retain each individual slot width before summing auxiliary masses.
-/
import Math115.TransportRefinement

/-!
# Transport with each slot's actual quadratic width

The auxiliary mass is weighted before summation, avoiding a common maximum
width. This is an abstract transport theorem under the existing signature and
positivity hypotheses; it does not establish those hypotheses for new models.
-/

namespace OAI.ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix
open FactorialSignatures BalancedFamily BalancedEnumeration IntegerMarginal

universe u

noncomputable def quadraticAuxiliaryKernel {I : Type u} : (Ms : List ℕ) →
    ((Coordinates I Ms → ℕ) → ℝ) → (I → ℕ) → ℝ
  | [], _ => fun _ => 0
  | U :: Ms, F => fun z => (((U + 1 : ℕ) : ℝ)^2 / 4) *
      marginal (exposedFamily Ms F) (U + 1) z +
      quadraticAuxiliaryKernel Ms (marginal F U) z

theorem correctionKernel_le_quadraticAuxiliary {I : Type u} (Ms : List ℕ)
    (F : (Coordinates I Ms → ℕ) → ℝ) (hF : ∀ x, 0 ≤ F x) (z : I → ℕ) :
    correctionKernel Ms F z ≤ quadraticAuxiliaryKernel Ms F z := by
  induction Ms with
  | nil => simp [correctionKernel, quadraticAuxiliaryKernel]
  | cons U Ms ih =>
    have hcur := weightedFuture_upper_quadratic (exposedFamily Ms F) (U + 1)
      (fun x => eliminate_nonnegative Ms _ (fun p => hF _) _) z
    have htail := ih (marginal F U)
      (fun x => Finset.sum_nonneg (fun j _ => hF _))
    exact add_le_add hcur htail

lemma correction_offdiagonal_le_quadraticAuxiliary (Ms : List ℕ)
    (F : (Coordinates Bool Ms → ℕ) → ℝ) (hF : ∀ x, 0 ≤ F x) (z : Bool → ℕ) :
    integerRemovalMatrix (correctionKernel Ms F) z false true ≤
      integerRemovalMatrix (quadraticAuxiliaryKernel Ms F) z false true := by
  unfold integerRemovalMatrix
  split_ifs
  · exact correctionKernel_le_quadraticAuxiliary Ms F hF _
  · exact le_rfl

/-- No common upper width is needed: each slot is weighted separately. -/
theorem recursive_root_potential_widths (Ms : List ℕ)
    (F : (Coordinates Bool Ms → ℕ) → ℝ) (m z : Bool → ℕ) (R : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hF : ∀ x, 0 ≤ F x)
    (hpos : BalancedBox.PositiveSlice F (bounds m Ms) (R + Ms.sum))
    (hsig : BalancedBox.RemovalSlice F (bounds m Ms) (R + Ms.sum))
    (hz : BalancedBox.InBox m z) (htotal : (∑ i, z i) = R + 1)
    (hs : 0 < oneHole (eliminate Ms F) z false)
    (ht : 0 < oneHole (eliminate Ms F) z true) :
    let s := oneHole (eliminate Ms F) z false
    let t := oneHole (eliminate Ms F) z true
    let c := integerRemovalMatrix (quadraticAuxiliaryKernel Ms F) z false true
    recursivePotential Ms F z (rootCoefficients s t) ≤
      1 / s + 1 / t + 2 * c / (s * t) := by
  dsimp only
  have hp := recursivePotential_bound Ms F m z R
    (rootCoefficients _ _) hlower hF hpos hsig hz htotal (root_balance _ _ hs ht)
  rw [root_holePotential _ _ hs ht] at hp
  have hq := root_future_bound (integerRemovalMatrix (correctionKernel Ms F) z)
    (oneHole (eliminate Ms F) z false) (oneHole (eliminate Ms F) z true) 1
    (integerRemovalMatrix (quadraticAuxiliaryKernel Ms F) z false true)
    hs ht (integerRemoval_symm _ _ _ _)
    (removal_nonnegative _ (correctionKernel_nonnegative Ms F hF) _ _ _)
    (removal_nonnegative _ (correctionKernel_nonnegative Ms F hF) _ _ _)
    (by simpa only [one_mul] using
      correction_offdiagonal_le_quadraticAuxiliary Ms F hF z)
  simp only [mul_one] at hq
  linarith

theorem integer_root_leaf_transport_widths (Ms : List ℕ)
    (F H : (Coordinates Bool Ms → ℕ) → ℝ) (m z : Bool → ℕ) (R : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hF : ∀ x, 0 ≤ F x)
    (hpos : BalancedBox.PositiveSlice F (bounds m Ms) (R + Ms.sum))
    (hsig : BalancedBox.RemovalSlice F (bounds m Ms) (R + Ms.sum))
    (hz : BalancedBox.InBox m z) (htotal : (∑ i, z i) = R + 1)
    (hs : 0 < oneHole (eliminate Ms F) z false)
    (ht : 0 < oneHole (eliminate Ms F) z true) :
    let s := oneHole (eliminate Ms F) z false
    let t := oneHole (eliminate Ms F) z true
    let c := integerRemovalMatrix (quadraticAuxiliaryKernel Ms F) z false true
    (holeLinear (eliminate Ms (fun p => F p * H p)) z (rootCoefficients s t))^2 ≤
      (1 / s + 1 / t + 2 * c / (s * t)) * leafEnergySum Ms F H z := by
  dsimp only
  have hp := recursive_root_potential_widths Ms F m z R hlower hF hpos hsig hz htotal hs ht
  have hb := integer_recursive_transport_of_slice Ms F H m z R (rootCoefficients _ _)
    hF hpos hz htotal (root_balance _ _ hs ht)
  have hen := recursiveEnergy_nonnegative Ms F H z (rootCoefficients
    (oneHole (eliminate Ms F) z false) (oneHole (eliminate Ms F) z true)) hF
  have h := hb.trans (mul_le_mul_of_nonneg_right hp hen)
  simpa only [recursiveEnergy_eq_leafEnergySum] using h

end OAI.ContingencyTables.IntegerWeightedTransport
