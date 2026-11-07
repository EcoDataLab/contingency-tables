/-
SPDX-License-Identifier: Apache-2.0
Additive actual physical hard-limit specialization.
-/
import Research.RetainedRootTransport

namespace OAI.ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Topology
open FactorialSignatures BalancedFamily BalancedBox BalancedEnumeration IntegerMarginal
open IntegerBoxTruncation Filter Math115.PhysicalLeafEnergy

/-- Box truncation remains inside the actual correction kernel, while endpoint
means and literal leaf energy are exactly the original hard-limit quantities. -/
theorem integer_box_root_leaf_transport_retained_limit {K : Type*} {l : Filter K}
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
    let g := truncate f (bounds m Ms) (R+Ms.sum)
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let B := integerRemovalMatrix (correctionKernel Ms g) z
    (oneHole (eliminate Ms (fun p => f p*H p)) z false / s -
      oneHole (eliminate Ms (fun p => f p*H p)) z true / t)^2 ≤
      retainedRootCoefficient B s t * leafEnergySum Ms f H z := by
  dsimp only
  let M := bounds m Ms
  let D := R+Ms.sum
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
    simpa only [M,D,oneHole_eliminate_truncate Ms f m z R hz htotal] using hs
  have ht' : 0 < oneHole (eliminate Ms (truncate f M D)) z true := by
    simpa only [M,D,oneHole_eliminate_truncate Ms f m z R hz htotal] using ht
  have h := integer_root_leaf_transport_retained_limit Ms (fun t => truncate (F t) M D)
    (truncate f M D) H (truncate_tendsto F f M D hlim) m z R hlower hF
    hz htotal hs' ht'
  dsimp only at h
  rw [truncate_mul] at h
  simpa only [M,D,oneHole_eliminate_truncate Ms _ m z R hz htotal,
    leafEnergySum_truncate_eq Ms m z R hz htotal f H hf] using h

end OAI.ContingencyTables.IntegerWeightedTransport

namespace Math115.RetainedRootPhysical

open OAI.ContingencyTables
open scoped BigOperators Classical Topology
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles
open ExcessContextProfiles SmallGraphProfiles FactorialSignatures IntegerBoxTruncation
open FirstPaperPhysicalMarginal FirstPaperContextTransport Filter
open PaddedCompletions CompletionCounts Math115.PhysicalLeafEnergy

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

omit [LinearOrder I] [LinearOrder J] in
/-- The original hard physical completion context satisfies the retained-root
local bound, using its proved upstream soft-signature approximation. -/
theorem context_leaf_transport_retained {C : Type u} [Fintype C] [DecidableEq C]
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ mC : C → ℕ) (m z : Bool → ℕ) (R : ℕ)
    (hprefix : InBox mC σ)
    (hlarge : ∀ i j, small i j=false → 2 ≤ B i j)
    (hlower : ∀ U ∈ Ms, 2 ≤ U)
    (hz : InBox m z) (htotal : (∑ i, z i)=R+1)
    (H : (Coordinates Bool Ms → ℕ) → ℝ)
    (hs : 0 < oneHole (eliminate Ms (contextHard small B r c L Ms e σ)) z false)
    (ht : 0 < oneHole (eliminate Ms (contextHard small B r c L Ms e σ)) z true) :
    let f := contextHard small B r c L Ms e σ
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let A := integerRemovalMatrix (correctionKernel Ms f) z
    (oneHole (eliminate Ms (fun p => f p*H p)) z false/s -
      oneHole (eliminate Ms (fun p => f p*H p)) z true/t)^2 ≤
      retainedRootCoefficient A s t * leafEnergySum Ms f H z := by
  apply integer_root_leaf_transport_retained_limit Ms
    (contextSoft small B r c L Ms e σ) _ H
    (contextSoft_tendsto small B r c L Ms e σ) m z R hlower
    _ hz htotal hs ht
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with a ha
  exact ⟨contextSoft_nonnegative small B r c L Ms e σ a,
    contextSoft_slices small B r c L Ms e σ mC m R hprefix a ha hlarge⟩

/-- Exact adjacent conditional means are controlled by their actual correction
matrix and the physical leaf energy owned by this root display. The statement
contains no repair-injection, global variance, or spectral-gap hypothesis. -/
theorem adjacent_physical_leaf_transport_retained
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hU : 2 ≤ U) (hl0 : 1 ≤ l) (hlU : l ≤ U)
    (hlarge : ∀ i j, small i j=false → 2 ≤ B i j)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U)
    {n : ℕ} (e : Fin n ≃ Later small s) (H : SmallProfile small → ℝ)
    (hleft : 0 < eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U (l-1)))
    (hright : 0 < eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U l)) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    let a := eliminate Ms f (childProfile U (l-1))
    let b := eliminate Ms f (childProfile U l)
    let A := integerRemovalMatrix (correctionKernel Ms f) (rootDisplay U l)
    let h := fun p => H (assemble small s hs σ U e p)
    (eliminate Ms (fun p => f p*h p) (childProfile U (l-1))/a -
      eliminate Ms (fun p => f p*h p) (childProfile U l)/b)^2 ≤
      retainedRootCoefficient A a b *
        physicalLeafEnergy small s hs σ U l e (hardMarginal small B r c L) H := by
  dsimp only
  have htransport := context_leaf_transport_retained small B r c L
    (widths (fun _ : Fin n => U))
    (contextEquiv small s hs e U) (prefixRaw small s σ U) (fun _ => U)
    (fun _ => U) (rootDisplay U l) U (prefixRaw_inBox small s σ U hσ) hlarge
    (fun w hw => by rw [widths_constant_mem U w hw]; exact hU)
    (rootDisplay_inBox U l hl0 hlU) (rootDisplay_total U l hlU)
    (fun p => H (assemble small s hs σ U e p))
    (by rw [rootDisplay_oneHole_false _ U l hl0 hlU]; exact hleft)
    (by rw [rootDisplay_oneHole_true]; exact hright)
  dsimp only at htransport
  simp only [rootDisplay_oneHole_false _ U l hl0 hlU, rootDisplay_oneHole_true] at htransport
  have heq := leafEnergySum_eq_physicalLeafEnergy small s hs σ U l e
    (hardMarginal small B r c L) H (hardMarginal_nonnegative small B r c L)
  change leafEnergySum _ (contextHard small B r c L _ (contextEquiv small s hs e U)
    (prefixRaw small s σ U)) (fun p => H (assemble small s hs σ U e p)) _ = _ at heq
  rw [heq] at htransport
  exact htransport

omit [LinearOrder I] [LinearOrder J] in
/-- The box-truncated hard physical completion context satisfies the retained-root
local bound, using its proved upstream soft-signature approximation. -/
theorem context_box_leaf_transport_retained {C : Type u} [Fintype C] [DecidableEq C]
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I×J => small a.1 a.2))
    (σ mC : C → ℕ) (m z : Bool → ℕ) (R : ℕ)
    (hprefix : InBox mC σ)
    (hlarge : ∀ i j, small i j=false → 2 ≤ B i j)
    (hlower : ∀ U ∈ Ms, 2 ≤ U)
    (hz : InBox m z) (htotal : (∑ i, z i)=R+1)
    (H : (Coordinates Bool Ms → ℕ) → ℝ)
    (hs : 0 < oneHole (eliminate Ms (contextHard small B r c L Ms e σ)) z false)
    (ht : 0 < oneHole (eliminate Ms (contextHard small B r c L Ms e σ)) z true) :
    let f := contextHard small B r c L Ms e σ
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let g := truncate f (bounds m Ms) (R+Ms.sum)
    let A := integerRemovalMatrix (correctionKernel Ms g) z
    (oneHole (eliminate Ms (fun p => f p*H p)) z false/s -
      oneHole (eliminate Ms (fun p => f p*H p)) z true/t)^2 ≤
      retainedRootCoefficient A s t * leafEnergySum Ms f H z := by
  apply integer_box_root_leaf_transport_retained_limit Ms
    (contextSoft small B r c L Ms e σ) _ H
    (contextSoft_tendsto small B r c L Ms e σ) m z R hlower
    _ hz htotal hs ht
  filter_upwards [Filter.eventually_ge_atTop (0:ℝ)] with a ha
  exact ⟨contextSoft_nonnegative small B r c L Ms e σ a,
    contextSoft_slices small B r c L Ms e σ mC m R hprefix a ha hlarge⟩

/-- Exact adjacent conditional means are controlled by their box-truncated actual correction
matrix and the physical leaf energy owned by this root display. The statement
contains no repair-injection, global variance, or spectral-gap hypothesis. -/
theorem adjacent_physical_box_leaf_transport_retained
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hU : 2 ≤ U) (hl0 : 1 ≤ l) (hlU : l ≤ U)
    (hlarge : ∀ i j, small i j=false → 2 ≤ B i j)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U)
    {n : ℕ} (e : Fin n ≃ Later small s) (H : SmallProfile small → ℝ)
    (hleft : 0 < eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U (l-1)))
    (hright : 0 < eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U l)) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    let a := eliminate Ms f (childProfile U (l-1))
    let b := eliminate Ms f (childProfile U l)
    let g := truncate f (bounds (fun _ : Bool => U) Ms) (U+Ms.sum)
    let A := integerRemovalMatrix (correctionKernel Ms g) (rootDisplay U l)
    let h := fun p => H (assemble small s hs σ U e p)
    (eliminate Ms (fun p => f p*h p) (childProfile U (l-1))/a -
      eliminate Ms (fun p => f p*h p) (childProfile U l)/b)^2 ≤
      retainedRootCoefficient A a b *
        physicalLeafEnergy small s hs σ U l e (hardMarginal small B r c L) H := by
  dsimp only
  have htransport := context_box_leaf_transport_retained small B r c L
    (widths (fun _ : Fin n => U))
    (contextEquiv small s hs e U) (prefixRaw small s σ U) (fun _ => U)
    (fun _ => U) (rootDisplay U l) U (prefixRaw_inBox small s σ U hσ) hlarge
    (fun w hw => by rw [widths_constant_mem U w hw]; exact hU)
    (rootDisplay_inBox U l hl0 hlU) (rootDisplay_total U l hlU)
    (fun p => H (assemble small s hs σ U e p))
    (by rw [rootDisplay_oneHole_false _ U l hl0 hlU]; exact hleft)
    (by rw [rootDisplay_oneHole_true]; exact hright)
  dsimp only at htransport
  simp only [rootDisplay_oneHole_false _ U l hl0 hlU, rootDisplay_oneHole_true] at htransport
  have heq := leafEnergySum_eq_physicalLeafEnergy small s hs σ U l e
    (hardMarginal small B r c L) H (hardMarginal_nonnegative small B r c L)
  change leafEnergySum _ (contextHard small B r c L _ (contextEquiv small s hs e U)
    (prefixRaw small s σ U)) (fun p => H (assemble small s hs σ U e p)) _ = _ at heq
  rw [heq] at htransport
  exact htransport

end Math115.RetainedRootPhysical

#print axioms Math115.RetainedRootPhysical.adjacent_physical_leaf_transport_retained

#print axioms Math115.RetainedRootPhysical.adjacent_physical_box_leaf_transport_retained
