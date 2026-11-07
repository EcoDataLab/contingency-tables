import Math115.WidthWeightedTransport
import Math115.PhysicalLeafEnergy

namespace OAI.ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Topology
open FactorialSignatures BalancedFamily BalancedBox BalancedEnumeration IntegerMarginal
open IntegerBoxTruncation Filter Math115.PhysicalLeafEnergy

universe u

lemma quadraticAuxiliaryKernel_tendsto {K : Type*} {l : Filter K} {I : Type u}
    (Ms : List ℕ) (F : K → (Coordinates I Ms → ℕ) → ℝ)
    (f : (Coordinates I Ms → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x))) (z : I → ℕ) :
    Tendsto (fun t => quadraticAuxiliaryKernel Ms (F t) z) l
      (nhds (quadraticAuxiliaryKernel Ms f z)) := by
  induction Ms with
  | nil => exact tendsto_const_nhds
  | cons U Ms ih =>
    apply Tendsto.add
    · apply Tendsto.const_mul
      unfold marginal
      apply tendsto_finsetSum
      intro j _
      exact eliminate_tendsto Ms _ _ (fun x => hlim _) _
    · apply ih
      intro x
      unfold marginal
      apply tendsto_finsetSum
      intro j _
      exact hlim _

theorem integer_root_leaf_transport_widths_limit {K : Type*} {l : Filter K}
    [l.NeBot] (Ms : List ℕ)
    (F : K → (Coordinates Bool Ms → ℕ) → ℝ) (f H : (Coordinates Bool Ms → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x)))
    (m z : Bool → ℕ) (R : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U)
    (hsoft : ∀ᶠ t in l, (∀ x, 0 ≤ F t x) ∧
      PositiveSlice (F t) (bounds m Ms) (R + Ms.sum) ∧
      RemovalSlice (F t) (bounds m Ms) (R + Ms.sum))
    (hz : InBox m z) (htotal : (∑ i, z i) = R + 1)
    (hs : 0 < oneHole (eliminate Ms f) z false)
    (ht : 0 < oneHole (eliminate Ms f) z true) :
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let c := integerRemovalMatrix (quadraticAuxiliaryKernel Ms f) z false true
    (oneHole (eliminate Ms (fun p => f p * H p)) z false / s -
      oneHole (eliminate Ms (fun p => f p * H p)) z true / t)^2 ≤
      (1 / s + 1 / t + 2 * c / (s * t)) * leafEnergySum Ms f H z := by
  dsimp only
  have hmarg := eliminate_tendsto Ms F f hlim
  have hnum := eliminate_tendsto Ms (fun t p => F t p * H p) (fun p => f p * H p)
    (fun p => (hlim p).mul_const (H p))
  have hsm := oneHole_tendsto _ _ hmarg z false
  have htm := oneHole_tendsto _ _ hmarg z true
  have hsn := oneHole_tendsto _ _ hnum z false
  have htn := oneHole_tendsto _ _ hnum z true
  have hc := removal_tendsto _ _ (quadraticAuxiliaryKernel_tendsto Ms F f hlim) z false true
  have he := leafEnergySum_tendsto Ms F f H hlim z
  have hleft := ((hsn.div hsm (ne_of_gt hs)).sub (htn.div htm (ne_of_gt ht))).pow 2
  have h1 : Tendsto (fun _ : K => (1 : ℝ)) l (nhds 1) := tendsto_const_nhds
  have hright := (((h1.div hsm (ne_of_gt hs)).add
    (h1.div htm (ne_of_gt ht))).add
    ((hc.const_mul 2).div (hsm.mul htm)
      (mul_ne_zero (ne_of_gt hs) (ne_of_gt ht)))).mul he
  apply le_of_tendsto_of_tendsto hleft hright
  have hspos : ∀ᶠ t in l, 0 < oneHole (eliminate Ms (F t)) z false :=
    hsm.eventually (lt_mem_nhds hs)
  have htpos : ∀ᶠ t in l, 0 < oneHole (eliminate Ms (F t)) z true :=
    htm.eventually (lt_mem_nhds ht)
  filter_upwards [hsoft, hspos, htpos] with t hf hsp htp
  have hb := integer_root_leaf_transport_widths Ms (F t) H m z R hlower
    hf.1 hf.2.1 hf.2.2 hz htotal hsp htp
  simpa only [root_linear_eq, Pi.div_apply] using hb

theorem integer_box_root_leaf_transport_widths_limit {K : Type*} {l : Filter K}
    [l.NeBot] (Ms : List ℕ)
    (F : K → (Coordinates Bool Ms → ℕ) → ℝ) (f H : (Coordinates Bool Ms → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x)))
    (m z : Bool → ℕ) (R : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U)
    (hsoft : ∀ᶠ t in l, (∀ x, 0 ≤ F t x) ∧
      PositiveSlice (F t) (bounds m Ms) (R + Ms.sum) ∧
      RemovalSlice (F t) (bounds m Ms) (R + Ms.sum))
    (hz : InBox m z) (htotal : (∑ i, z i) = R + 1)
    (hs : 0 < oneHole (eliminate Ms f) z false)
    (ht : 0 < oneHole (eliminate Ms f) z true) :
    let g := truncate f (bounds m Ms) (R + Ms.sum)
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let c := integerRemovalMatrix (quadraticAuxiliaryKernel Ms g) z false true
    (oneHole (eliminate Ms (fun p => f p * H p)) z false / s -
      oneHole (eliminate Ms (fun p => f p * H p)) z true / t)^2 ≤
      (1 / s + 1 / t + 2 * c / (s * t)) * leafEnergySum Ms f H z := by
  dsimp only
  let M := bounds m Ms
  let D := R + Ms.sum
  have hF : ∀ᶠ t in l, (∀ x, 0 ≤ truncate (F t) M D x) ∧
      PositiveSlice (truncate (F t) M D) M D ∧
      RemovalSlice (truncate (F t) M D) M D := by
    filter_upwards [hsoft] with t ht
    exact truncate_all_slices (F t) M D ht.1 ht.2.1 ht.2.2
  have hf : ∀ x, 0 ≤ f x := by
    intro x
    apply le_of_tendsto_of_tendsto tendsto_const_nhds (hlim x)
    filter_upwards [hsoft] with t ht
    exact ht.1 x
  have hs' : 0 < oneHole (eliminate Ms (truncate f M D)) z false := by
    simpa only [M, D, oneHole_eliminate_truncate Ms f m z R hz htotal] using hs
  have ht' : 0 < oneHole (eliminate Ms (truncate f M D)) z true := by
    simpa only [M, D, oneHole_eliminate_truncate Ms f m z R hz htotal] using ht
  have h := integer_root_leaf_transport_widths_limit Ms (fun t => truncate (F t) M D)
    (truncate f M D) H (truncate_tendsto F f M D hlim) m z R hlower hF
    hz htotal hs' ht'
  dsimp only at h
  rw [truncate_mul] at h
  simpa only [M, D, oneHole_eliminate_truncate Ms _ m z R hz htotal,
    leafEnergySum_truncate_eq Ms m z R hz htotal f H hf] using h

end OAI.ContingencyTables.IntegerWeightedTransport

#print axioms OAI.ContingencyTables.IntegerWeightedTransport.integer_box_root_leaf_transport_widths_limit
