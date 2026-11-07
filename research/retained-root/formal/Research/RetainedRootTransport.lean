/-
SPDX-License-Identifier: Apache-2.0
Additive formalization using OpenAI math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
The actual correction kernel is retained. No diagonal upper envelope is used.
-/
import Math115.PhysicalLeafEnergy

namespace OAI.ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Matrix Topology
open FactorialSignatures BalancedFamily BalancedBox BalancedEnumeration IntegerMarginal
open IntegerBoxTruncation Filter Math115.PhysicalLeafEnergy

universe u

/-- Expansion retaining all four entries, even before symmetry is invoked. -/
lemma root_form_four_entries (B : Matrix Bool Bool ℝ) (s t : ℝ) :
    B.toBilin' (rootCoefficients s t) (rootCoefficients s t) =
      B false false / s^2 - (B false true + B true false) / (s*t) +
        B true true / t^2 := by
  simp only [Matrix.toBilin'_apply, Fintype.sum_bool, rootCoefficients,
    Bool.false_eq_true, ↓reduceIte]
  ring

/-- Exact retained-root coefficient for a symmetric correction matrix. -/
noncomputable def retainedRootCoefficient (B : Matrix Bool Bool ℝ) (s t : ℝ) : ℝ :=
  1/s + 1/t - B false false / s^2 + 2*B false true/(s*t) - B true true/t^2

lemma root_potential_sub_form (B : Matrix Bool Bool ℝ) (s t : ℝ)
    (hsymm : B true false = B false true) :
    1/s + 1/t - B.toBilin' (rootCoefficients s t) (rootCoefficients s t) =
      retainedRootCoefficient B s t := by
  rw [root_form_four_entries, hsymm]
  unfold retainedRootCoefficient
  ring

/-- The softened transport retains the actual root diagonal savings. -/
theorem integer_root_leaf_transport_retained (Ms : List ℕ)
    (F H : (Coordinates Bool Ms → ℕ) → ℝ) (m z : Bool → ℕ) (R : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hF : ∀ x, 0 ≤ F x)
    (hpos : PositiveSlice F (bounds m Ms) (R+Ms.sum))
    (hsig : RemovalSlice F (bounds m Ms) (R+Ms.sum))
    (hz : InBox m z) (htotal : (∑ i, z i)=R+1)
    (hs : 0 < oneHole (eliminate Ms F) z false)
    (ht : 0 < oneHole (eliminate Ms F) z true) :
    let s := oneHole (eliminate Ms F) z false
    let t := oneHole (eliminate Ms F) z true
    let B := integerRemovalMatrix (correctionKernel Ms F) z
    (holeLinear (eliminate Ms (fun p => F p*H p)) z (rootCoefficients s t))^2 ≤
      retainedRootCoefficient B s t * leafEnergySum Ms F H z := by
  dsimp only
  have hp := recursivePotential_bound Ms F m z R (rootCoefficients _ _)
    hlower hF hpos hsig hz htotal (root_balance _ _ hs ht)
  rw [root_holePotential _ _ hs ht,
    root_potential_sub_form _ _ _ (integerRemoval_symm _ _ _ _)] at hp
  have hb := integer_recursive_transport_of_slice Ms F H m z R (rootCoefficients _ _)
    hF hpos hz htotal (root_balance _ _ hs ht)
  have hen := recursiveEnergy_nonnegative Ms F H z (rootCoefficients
    (oneHole (eliminate Ms F) z false) (oneHole (eliminate Ms F) z true)) hF
  simpa only [recursiveEnergy_eq_leafEnergySum] using
    hb.trans (mul_le_mul_of_nonneg_right hp hen)

/-- The retained coefficient is nonnegative as a consequence of the actual
recursive potential bound, rather than a separate assumed estimate. -/
theorem retainedRootCoefficient_nonnegative (Ms : List ℕ)
    (F : (Coordinates Bool Ms → ℕ) → ℝ) (m z : Bool → ℕ) (R : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hF : ∀ x, 0 ≤ F x)
    (hpos : PositiveSlice F (bounds m Ms) (R+Ms.sum))
    (hsig : RemovalSlice F (bounds m Ms) (R+Ms.sum))
    (hz : InBox m z) (htotal : (∑ i, z i)=R+1)
    (hs : 0 < oneHole (eliminate Ms F) z false)
    (ht : 0 < oneHole (eliminate Ms F) z true) :
    0 ≤ retainedRootCoefficient (integerRemovalMatrix (correctionKernel Ms F) z)
      (oneHole (eliminate Ms F) z false) (oneHole (eliminate Ms F) z true) := by
  have hp := recursivePotential_bound Ms F m z R (rootCoefficients _ _)
    hlower hF hpos hsig hz htotal (root_balance _ _ hs ht)
  rw [root_holePotential _ _ hs ht,
    root_potential_sub_form _ _ _ (integerRemoval_symm _ _ _ _)] at hp
  exact (recursivePotential_nonnegative Ms F z (rootCoefficients _ _) hF).trans hp

/-- Every actual correction entry converges, since the correction kernel is a
finite weighted sum of literal source evaluations. -/
lemma correctionKernel_tendsto {K : Type*} {l : Filter K} {I : Type u}
    (Ms : List ℕ) (F : K → (Coordinates I Ms → ℕ) → ℝ)
    (f : (Coordinates I Ms → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x))) (z : I → ℕ) :
    Tendsto (fun t => correctionKernel Ms (F t) z) l
      (nhds (correctionKernel Ms f z)) := by
  induction Ms with
  | nil => exact tendsto_const_nhds
  | cons U Ms ih =>
    apply Tendsto.add
    · unfold weightedFuture
      apply tendsto_finsetSum
      intro j _
      apply Tendsto.const_mul
      exact eliminate_tendsto Ms _ _ (fun x => hlim _) _
    · apply ih
      intro x
      unfold marginal
      apply tendsto_finsetSum
      intro j _
      exact hlim _

/-- Hard finite-limit transport; only the two root child masses must remain
positive. The three displayed entries encode all four by exact symmetry. -/
theorem integer_root_leaf_transport_retained_limit {K : Type*} {l : Filter K}
    [l.NeBot] (Ms : List ℕ)
    (F : K → (Coordinates Bool Ms → ℕ) → ℝ) (f H : (Coordinates Bool Ms → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x)))
    (m z : Bool → ℕ) (R : ℕ) (hlower : ∀ U ∈ Ms, 2 ≤ U)
    (hsoft : ∀ᶠ t in l, (∀ x, 0 ≤ F t x) ∧
      PositiveSlice (F t) (bounds m Ms) (R+Ms.sum) ∧
      RemovalSlice (F t) (bounds m Ms) (R+Ms.sum))
    (hz : InBox m z) (htotal : (∑ i, z i)=R+1)
    (hs : 0 < oneHole (eliminate Ms f) z false)
    (ht : 0 < oneHole (eliminate Ms f) z true) :
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let B := integerRemovalMatrix (correctionKernel Ms f) z
    (oneHole (eliminate Ms (fun p => f p*H p)) z false / s -
      oneHole (eliminate Ms (fun p => f p*H p)) z true / t)^2 ≤
      retainedRootCoefficient B s t * leafEnergySum Ms f H z := by
  dsimp only
  have hmarg := eliminate_tendsto Ms F f hlim
  have hnum := eliminate_tendsto Ms (fun t p => F t p*H p) (fun p => f p*H p)
    (fun p => (hlim p).mul_const (H p))
  have hsm := oneHole_tendsto _ _ hmarg z false
  have htm := oneHole_tendsto _ _ hmarg z true
  have hsn := oneHole_tendsto _ _ hnum z false
  have htn := oneHole_tendsto _ _ hnum z true
  have hB (i j : Bool) := removal_tendsto _ _
    (correctionKernel_tendsto Ms F f hlim) z i j
  have he := leafEnergySum_tendsto Ms F f H hlim z
  have hleft := ((hsn.div hsm (ne_of_gt hs)).sub (htn.div htm (ne_of_gt ht))).pow 2
  have h1 : Tendsto (fun _ : K => (1 : ℝ)) l (nhds 1) := tendsto_const_nhds
  have hcoeff := ((((h1.div hsm (ne_of_gt hs)).add (h1.div htm (ne_of_gt ht))).sub
    ((hB false false).div (hsm.pow 2) (pow_ne_zero 2 (ne_of_gt hs)))).add
    (((hB false true).const_mul 2).div (hsm.mul htm)
      (mul_ne_zero (ne_of_gt hs) (ne_of_gt ht)))).sub
    ((hB true true).div (htm.pow 2) (pow_ne_zero 2 (ne_of_gt ht)))
  have hright := hcoeff.mul he
  apply le_of_tendsto_of_tendsto hleft hright
  have hspos : ∀ᶠ t in l, 0 < oneHole (eliminate Ms (F t)) z false :=
    hsm.eventually (lt_mem_nhds hs)
  have htpos : ∀ᶠ t in l, 0 < oneHole (eliminate Ms (F t)) z true :=
    htm.eventually (lt_mem_nhds ht)
  filter_upwards [hsoft, hspos, htpos] with t hf hsp htp
  have hb := integer_root_leaf_transport_retained Ms (F t) H m z R hlower
    hf.1 hf.2.1 hf.2.2 hz htotal hsp htp
  simpa only [root_linear_eq, Pi.div_apply, retainedRootCoefficient] using hb

end OAI.ContingencyTables.IntegerWeightedTransport

#print axioms OAI.ContingencyTables.IntegerWeightedTransport.integer_root_leaf_transport_retained_limit
