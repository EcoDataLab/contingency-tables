/-
SPDX-License-Identifier: Apache-2.0
Uses the unchanged physical context maps and graph definitions of OpenAI
math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. This adds localized physical
leaf-edge images, global owner recovery, and their energy summation bound.
-/
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalPrefixEnergies
import OAI.Combinatorics.ContingencyTables.Transport.IntegerTruncatedTransport
import Math115.UpstreamOwnershipBridge
import Math115.TransportRefinement

/-!
# Literal transport leaf energies in the physical small graph

The local object below is the image of upstream `leafEdges`, not the induced
exchange graph on the union `leafVertices`. Only the literal leaf edges have
the unique recovered display needed for the global summation argument.

The weight is any nonnegative function, so hard-zero endpoints are allowed.
The sharpened transport survives the soft-to-hard limit with the auxiliary
kernel's box and total-degree truncation retained. The final child-variance
and global Poincare comparisons are not proved here.
-/

namespace Math115.PhysicalLeafEnergy

open OAI.ContingencyTables
open scoped BigOperators Classical Topology
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles
open ExcessContextProfiles SmallGraphProfiles FactorialSignatures
open IntegerBoxTruncation
open FirstPaperPhysicalMarginal
open FirstPaperContextTransport Filter
open PaddedCompletions CompletionCounts
open Math115.GlobalDisplayOwnership

universe u

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

abbrev LocalCoordinates (U n : ℕ) := Coordinates Bool (widths (fun _ : Fin n => U))

noncomputable def physicalLeafEdges (small : I → J → Bool)
    (s : I × J) (hs : small s.1 s.2 = true) (σ : I × J → ℕ)
    (U l : ℕ) {n : ℕ} (e : Fin n ≃ Later small s) :
    Finset (SmallProfile small × SmallProfile small) :=
  (leafEdges (widths (fun _ : Fin n => U)) (rootDisplay U l)).image
    (fun p => (assemble small s hs σ U e p.1, assemble small s hs σ U e p.2))

noncomputable def physicalLeafEnergy (small : I → J → Bool)
    (s : I × J) (hs : small s.1 s.2 = true) (σ : I × J → ℕ)
    (U l : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (f H : SmallProfile small → ℝ) : ℝ :=
  (∑ p ∈ physicalLeafEdges small s hs σ U l e, edgeTerm f H p) / 2

/-- Exact equality with the recursive literal leaf energy, including its
oriented-edge factor one half. No physical support or positivity is hidden. -/
theorem leafEnergySum_eq_physicalLeafEnergy (small : I → J → Bool)
    (s : I × J) (hs : small s.1 s.2 = true) (σ : I × J → ℕ)
    (U l : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (f H : SmallProfile small → ℝ) (hf : ∀ x, 0 ≤ f x) :
    leafEnergySum (widths (fun _ : Fin n => U))
      (fun x => f (assemble small s hs σ U e x))
      (fun x => H (assemble small s hs σ U e x)) (rootDisplay U l) =
      physicalLeafEnergy small s hs σ U l e f H := by
  rw [leafEnergySum_eq_edges _ _ _ _ (fun x => hf _)]
  unfold physicalLeafEnergy physicalLeafEdges
  rw [Finset.sum_image]
  · rfl
  · intro a _ b _ he
    apply Prod.ext
    · exact assemble_injective small s hs σ U e (congrArg Prod.fst he)
    · exact assemble_injective small s hs σ U e (congrArg Prod.snd he)

/-- The fixed physical leaf energy passes continuously to hard-zero weights;
no convergence of currents or divisions by vertex weights is involved. -/
theorem physicalLeafEnergy_tendsto {K : Type*} {filter : Filter K}
    (small : I → J → Bool) (s : I × J) (hs : small s.1 s.2 = true)
    (σ : I × J → ℕ) (U l : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (F : K → SmallProfile small → ℝ) (f H : SmallProfile small → ℝ)
    (hlim : ∀ x, Filter.Tendsto (fun t => F t x) filter (nhds (f x))) :
    Filter.Tendsto (fun t => physicalLeafEnergy small s hs σ U l e (F t) H) filter
      (nhds (physicalLeafEnergy small s hs σ U l e f H)) := by
  unfold physicalLeafEnergy
  apply Filter.Tendsto.div_const
  apply tendsto_finsetSum
  intro edge _
  exact ((hlim edge.1).min (hlim edge.2)).mul_const _

lemma leafVertices_inBox {C : Type*} [Fintype C] [DecidableEq C]
    (Ms : List ℕ) (m z : C → ℕ) (hz : InBox m z)
    (x : Coordinates C Ms → ℕ) (hx : x ∈ leafVertices Ms z) :
    InBox (bounds m Ms) x := by
  obtain ⟨q, _, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  intro k
  exact (Nat.sub_le _ _).trans (embedding_inBox Ms m z hz q k)

lemma leafVertices_total {C : Type*} [Fintype C] [DecidableEq C]
    (Ms : List ℕ) (z : C → ℕ) (R : ℕ) (hz : (∑ i, z i) = R + 1)
    (x : Coordinates C Ms → ℕ) (hx : x ∈ leafVertices Ms z) :
    (∑ i, x i) = R + Ms.sum := by
  obtain ⟨q, _, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
  have ht := active_removeOne_sum (embedding Ms z q) i (Finset.mem_filter.mp hi).2
  rw [embedding_total, hz] at ht
  omega

/-- Box/total truncation is exactly invisible on valid literal leaf energy.
The auxiliary kernel must still retain its truncation in transport bounds. -/
theorem leafEnergySum_truncate_eq {C : Type*} [Fintype C] [DecidableEq C]
    (Ms : List ℕ) (m z : C → ℕ) (R : ℕ)
    (hz : InBox m z) (htotal : (∑ i, z i) = R + 1)
    (f H : (Coordinates C Ms → ℕ) → ℝ) (hf : ∀ x, 0 ≤ f x) :
    leafEnergySum Ms (truncate f (bounds m Ms) (R + Ms.sum)) H z =
      leafEnergySum Ms f H z := by
  rw [leafEnergySum_eq_edges _ _ _ _ (truncate_nonnegative f _ _ hf),
    leafEnergySum_eq_edges _ _ _ _ hf]
  apply congrArg (fun a : ℝ => a / 2)
  apply Finset.sum_congr rfl
  intro edge hedge
  obtain ⟨hx, hy, _⟩ := leafEdges_states_adjacent Ms z edge hedge
  have heq (x) (hx : x ∈ leafVertices Ms z) :
      truncate f (bounds m Ms) (R + Ms.sum) x = f x := by
    simp only [truncate, leafVertices_inBox Ms m z hz x hx,
      leafVertices_total Ms z R htotal x hx, and_self, ↓reduceIte]
  unfold edgeTerm
  rw [heq _ hx, heq _ hy]

/-- Every literal leaf edge maps into the actual bounded physical exchange
graph; its two valid holes are already outside the fixed prefix. -/
theorem physicalLeafEdges_subset (small : I → J → Bool) (B : I → J → ℕ)
    (s : I × J) (hs : small s.1 s.2 = true) (σ : I × J → ℕ)
    (U l : ℕ) (hU : 1 ≤ U) (hl0 : 1 ≤ l) (hlU : l ≤ U)
    (hB : ∀ i j, small i j = true → B i j = U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U)
    {n : ℕ} (e : Fin n ≃ Later small s) :
    physicalLeafEdges small s hs σ U l e ⊆ physicalEdges small B := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨hx, hy, hadj⟩ := leafEdges_states_adjacent _ _ q hq
  have hmem (v : LocalCoordinates U n → ℕ)
      (hv : v ∈ leafVertices _ (rootDisplay U l)) :
      assemble small s hs σ U e v ∈ vertices small B := by
    apply context_vertex_mem small B s hs σ U hU hB hσ e v
    · exact leafVertices_subset_context U n l hlU hv
    · exact leafVertices_inBox _ _ _ (rootDisplay_inBox U l hl0 hlU) v hv
  apply Finset.mem_filter.mpr
  exact ⟨Finset.mem_product.mpr ⟨hmem _ hx, hmem _ hy⟩,
    assemble_exchange_adjacent small s hs σ U e _ _ hadj⟩

lemma physical_display_special (small : I → J → Bool)
    (s : I × J) (hs : small s.1 s.2 = true) (σ : I × J → ℕ)
    (U l : ℕ) (hlU : l ≤ U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U)
    {n : ℕ} (e : Fin n ≃ Later small s)
    (q : Assignments (widths (fun _ : Fin n => U))) :
    IsSpecialDisplay (fun _ : Cells small => U) ⟨s, hs⟩
      (assemble small s hs σ U e (embedding _ (rootDisplay U l) q)) := by
  intro a
  rw [base_pair_total small s hs σ U l hlU hσ e q a]
  split_ifs <;> simp

/-- One shared physical literal leaf edge recovers the actual exposed cell,
adjacent level, and all (and only) the genuinely fixed earlier values. -/
theorem physicalLeafEdges_owner_unique (small : I → J → Bool)
    (s t : I × J) (hs : small s.1 s.2 = true) (ht : small t.1 t.2 = true)
    (σ τ : I × J → ℕ) (U l k : ℕ) (hlU : l ≤ U) (hkU : k ≤ U)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U)
    (hτ : ∀ a : Earlier small t, τ a.val.val ≤ U)
    {n m : ℕ} (e : Fin n ≃ Later small s) (e' : Fin m ≃ Later small t)
    (p : SmallProfile small × SmallProfile small)
    (hp : p ∈ physicalLeafEdges small s hs σ U l e)
    (hp' : p ∈ physicalLeafEdges small t ht τ U k e') :
    s = t ∧ l = k ∧ ∀ a : Cells small, RowMajorBefore a.val s → σ a.val = τ a.val := by
  obtain ⟨a, ha, hpa⟩ := Finset.mem_image.mp hp
  obtain ⟨b, hb, hpb⟩ := Finset.mem_image.mp hp'
  obtain ⟨qa, hqa, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨qb, hqb, rfl⟩ := Finset.mem_image.mp hb
  obtain ⟨_, _, hij⟩ := (Finset.mem_filter.mp hqa).2
  obtain ⟨_, _, hij'⟩ := (Finset.mem_filter.mp hqb).2
  have hedge := hpa.trans hpb.symm
  simp only [leafEdgeState, assemble_removeOne] at hedge
  have hn : contextEquiv small s hs e U (.inr qa.2.1) ≠
      contextEquiv small s hs e U (.inr qa.2.2) := by
    intro he
    exact hij (Sum.inr.inj ((contextEquiv small s hs e U).injective he))
  have hn' : contextEquiv small t ht e' U (.inr qb.2.1) ≠
      contextEquiv small t ht e' U (.inr qb.2.2) := by
    intro he
    exact hij' (Sum.inr.inj ((contextEquiv small t ht e' U).injective he))
  obtain ⟨hD, hslot, hlevel⟩ := edge_owner_unique_upstream
    (fun _ : Cells small => U) ⟨s, hs⟩ ⟨t, ht⟩ _ _ _ _ _ _ hn hn'
    (physical_display_special small s hs σ U l hlU hσ e qa.1)
    (physical_display_special small t ht τ U k hkU hτ e' qb.1)
    (Or.inl ⟨congrArg Prod.fst hedge, congrArg Prod.snd hedge⟩)
  have hst : s = t := congrArg Subtype.val hslot
  have hlk : l = k := by
    simpa only [assemble_special, embedding_root, rootDisplay,
      Bool.false_eq_true, ↓reduceIte] using hlevel
  refine ⟨hst, hlk, ?_⟩
  subst t
  intro a ha
  have h := congrFun hD (a, false)
  have hleft := assemble_prefix small s hs σ U e
    (embedding _ (rootDisplay U l) qa.1) ⟨a, ha⟩ false
  have hright := assemble_prefix small s ht τ U e'
    (embedding _ (rootDisplay U k) qb.1) ⟨a, ha⟩ false
  simpa only [Bool.false_eq_true, ↓reduceIte] using hleft.symm.trans (h.trans hright)

/-- Canonical finite owners contain no irrelevant future values or choice of
suffix enumeration. The positive adjacent level is `owner.2.1.val + 1`. -/
abbrev Owner (small : I → J → Bool) (U : ℕ) :=
  Σ s : Cells small, Fin U × (Earlier small s.val → Fin (U + 1))

noncomputable def suffixEnumeration (small : I → J → Bool) (s : I × J) :
    Fin (Fintype.card (Later small s)) ≃ Later small s :=
  (Fintype.equivFin (Later small s)).symm

noncomputable def ownerEdges (small : I → J → Bool) (U : ℕ)
    (o : Owner small U) : Finset (SmallProfile small × SmallProfile small) :=
  physicalLeafEdges small o.1.val o.1.property
    (prefixExtension small o.1.val U o.2.2) U (o.2.1.val + 1)
    (suffixEnumeration small o.1.val)

noncomputable def ownerEnergy (small : I → J → Bool) (U : ℕ)
    (o : Owner small U) (f H : SmallProfile small → ℝ) : ℝ :=
  (∑ p ∈ ownerEdges small U o, edgeTerm f H p) / 2

theorem owner_unique (small : I → J → Bool) (U : ℕ)
    (a b : Owner small U) (p : SmallProfile small × SmallProfile small)
    (ha : p ∈ ownerEdges small U a) (hb : p ∈ ownerEdges small U b) : a = b := by
  rcases a with ⟨s, l, σ⟩
  rcases b with ⟨t, k, τ⟩
  obtain ⟨hst, hlk, hprefix⟩ := physicalLeafEdges_owner_unique small s.val t.val
    s.property t.property (prefixExtension small s.val U σ)
    (prefixExtension small t.val U τ) U (l.val + 1) (k.val + 1)
    (Nat.succ_le_of_lt l.isLt) (Nat.succ_le_of_lt k.isLt)
    (prefixExtension_bounded small s.val U σ)
    (prefixExtension_bounded small t.val U τ)
    (suffixEnumeration small s.val) (suffixEnumeration small t.val) p ha hb
  have hst' : s = t := Subtype.ext hst
  subst t
  have hlk' : l = k := Fin.ext (Nat.add_right_cancel hlk)
  have hστ : σ = τ := by
    funext q
    apply Fin.ext
    simpa only [prefixExtension_at] using hprefix q.val q.property
  subst k
  subst τ
  rfl

theorem ownerEdges_pairwiseDisjoint (small : I → J → Bool) (U : ℕ) :
    Set.PairwiseDisjoint (Set.univ : Set (Owner small U)) (ownerEdges small U) := by
  intro a _ b _ hne
  apply Finset.disjoint_left.mpr
  intro p ha hb
  exact hne (owner_unique small U a b p ha hb)

/-- Actual physical literal leaf energies have no depth or adjacent-level
multiplicity. This permits zero weights and counts each oriented edge once
before dividing by two, exactly as `physicalEnergy` does upstream. -/
theorem sum_ownerEnergy_le_physicalEnergy (small : I → J → Bool) (B : I → J → ℕ)
    (U : ℕ) (hU : 1 ≤ U) (hB : ∀ i j, small i j = true → B i j = U)
    (f H : SmallProfile small → ℝ) (hf : ∀ x, 0 ≤ f x) :
    (∑ o : Owner small U, ownerEnergy small U o f H) ≤ physicalEnergy small B f H := by
  have hsub : Finset.univ.biUnion (ownerEdges small U) ⊆ physicalEdges small B := by
    intro p hp
    obtain ⟨o, _, ho⟩ := Finset.mem_biUnion.mp hp
    exact physicalLeafEdges_subset small B o.1.val o.1.property
      (prefixExtension small o.1.val U o.2.2) U (o.2.1.val + 1) hU
      (by omega) (Nat.succ_le_of_lt o.2.1.isLt) hB
      (prefixExtension_bounded small o.1.val U o.2.2)
      (suffixEnumeration small o.1.val) ho
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Owner small U)))
      (ownerEdges small U) := by
    simpa only [Finset.coe_univ] using ownerEdges_pairwiseDisjoint small U
  unfold ownerEnergy physicalEnergy
  rw [← Finset.sum_div, ← Finset.sum_biUnion hdisj]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ =>
    mul_nonneg (le_min (hf p.1) (hf p.2)) (sq_nonneg _))

/-- Specialization to the literal padded-completion weights. No positivity of
individual vertices or child masses is assumed or needed for this sum. -/
theorem sum_ownerEnergy_hardMarginal_le (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ)
    (hU : 1 ≤ U) (hB : ∀ i j, small i j = true → B i j = U)
    (H : SmallProfile small → ℝ) :
    (∑ o : Owner small U, ownerEnergy small U o (hardMarginal small B r c L) H) ≤
      physicalEnergy small B (hardMarginal small B r c L) H := by
  exact sum_ownerEnergy_le_physicalEnergy small B U hU hB _ H
    (hardMarginal_nonnegative small B r c L)

/-- Finite recursive leaf energy is continuous in every weight, even when
the limiting weights have zeros. Its definition needs no division by weights. -/
theorem leafEnergySum_tendsto {K : Type*} {filter : Filter K}
    {C : Type*} [Fintype C] [DecidableEq C] (Ms : List ℕ)
    (F : K → (Coordinates C Ms → ℕ) → ℝ) (f H : (Coordinates C Ms → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) filter (nhds (f x))) (z : C → ℕ) :
    Tendsto (fun t => leafEnergySum Ms (F t) H z) filter
      (nhds (leafEnergySum Ms f H z)) := by
  unfold leafEnergySum leafClique SignedTransport.cliqueEnergy
  apply tendsto_finsetSum
  intro q _
  apply Tendsto.div_const
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  simp only [one_mul]
  exact ((oneHole_tendsto F f hlim _ i).min
    (oneHole_tendsto F f hlim _ j)).mul_const _

/-- The quarter-coefficient transport passes to the hard limit while keeping
the literal leaf energy. Only the two endpoint marginal masses stay positive. -/
theorem integer_root_leaf_transport_quarter_limit {K : Type*} {filter : Filter K}
    [filter.NeBot] (Ms : List ℕ)
    (F : K → (Coordinates Bool Ms → ℕ) → ℝ) (f H : (Coordinates Bool Ms → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) filter (nhds (f x)))
    (m z : Bool → ℕ) (R W : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hsoft : ∀ᶠ t in filter, (∀ x, 0 ≤ F t x) ∧
      PositiveSlice (F t) (bounds m Ms) (R + Ms.sum) ∧
      RemovalSlice (F t) (bounds m Ms) (R + Ms.sum))
    (hz : InBox m z) (htotal : (∑ i, z i) = R + 1)
    (hs : 0 < oneHole (eliminate Ms f) z false)
    (ht : 0 < oneHole (eliminate Ms f) z true) :
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let c := integerRemovalMatrix (auxiliaryKernel Ms f) z false true
    (oneHole (eliminate Ms (fun p => f p * H p)) z false / s -
      oneHole (eliminate Ms (fun p => f p * H p)) z true / t)^2 ≤
      (1 / s + 1 / t + (((W : ℝ) + 1)^2 / 2) * c / (s * t)) *
        leafEnergySum Ms f H z := by
  dsimp only
  have hmarg := eliminate_tendsto Ms F f hlim
  have hnum := eliminate_tendsto Ms (fun t p => F t p * H p) (fun p => f p * H p)
    (fun p => (hlim p).mul_const (H p))
  have hsm := oneHole_tendsto _ _ hmarg z false
  have htm := oneHole_tendsto _ _ hmarg z true
  have hsn := oneHole_tendsto _ _ hnum z false
  have htn := oneHole_tendsto _ _ hnum z true
  have hc := removal_tendsto _ _ (auxiliaryKernel_tendsto Ms F f hlim) z false true
  have he := leafEnergySum_tendsto Ms F f H hlim z
  have hleft := ((hsn.div hsm (ne_of_gt hs)).sub (htn.div htm (ne_of_gt ht))).pow 2
  have h1 : Tendsto (fun _ : K => (1 : ℝ)) filter (nhds 1) := tendsto_const_nhds
  have hright := (((h1.div hsm (ne_of_gt hs)).add
    (h1.div htm (ne_of_gt ht))).add
    ((hc.const_mul (((W : ℝ) + 1)^2 / 2)).div (hsm.mul htm)
      (mul_ne_zero (ne_of_gt hs) (ne_of_gt ht)))).mul he
  apply le_of_tendsto_of_tendsto hleft hright
  have hspos : ∀ᶠ t in filter, 0 < oneHole (eliminate Ms (F t)) z false :=
    hsm.eventually (lt_mem_nhds hs)
  have htpos : ∀ᶠ t in filter, 0 < oneHole (eliminate Ms (F t)) z true :=
    htm.eventually (lt_mem_nhds ht)
  filter_upwards [hsoft, hspos, htpos] with t hf hsp htp
  have hb := integer_root_leaf_transport_quarter Ms (F t) H m z R W hlower hupper
    hf.1 hf.2.1 hf.2.2 hz htotal hsp htp
  simpa only [root_linear_eq, Pi.div_apply] using hb

/-- Hard-limit localized transport with the literal boxed auxiliary kernel.
Endpoint sums and leaf energy equal the original, untruncated physical sums. -/
theorem integer_box_root_leaf_transport_quarter_limit {K : Type*} {filter : Filter K}
    [filter.NeBot] (Ms : List ℕ)
    (F : K → (Coordinates Bool Ms → ℕ) → ℝ) (f H : (Coordinates Bool Ms → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) filter (nhds (f x)))
    (m z : Bool → ℕ) (R W : ℕ)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hsoft : ∀ᶠ t in filter, (∀ x, 0 ≤ F t x) ∧
      PositiveSlice (F t) (bounds m Ms) (R + Ms.sum) ∧
      RemovalSlice (F t) (bounds m Ms) (R + Ms.sum))
    (hz : InBox m z) (htotal : (∑ i, z i) = R + 1)
    (hs : 0 < oneHole (eliminate Ms f) z false)
    (ht : 0 < oneHole (eliminate Ms f) z true) :
    let g := truncate f (bounds m Ms) (R + Ms.sum)
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let c := integerRemovalMatrix (auxiliaryKernel Ms g) z false true
    (oneHole (eliminate Ms (fun p => f p * H p)) z false / s -
      oneHole (eliminate Ms (fun p => f p * H p)) z true / t)^2 ≤
      (1 / s + 1 / t + (((W : ℝ) + 1)^2 / 2) * c / (s * t)) *
        leafEnergySum Ms f H z := by
  dsimp only
  let M := bounds m Ms
  let D := R + Ms.sum
  have hF : ∀ᶠ t in filter, (∀ x, 0 ≤ truncate (F t) M D x) ∧
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
  have h := integer_root_leaf_transport_quarter_limit Ms (fun t => truncate (F t) M D)
    (truncate f M D) H (truncate_tendsto F f M D hlim) m z R W hlower hupper hF
    hz htotal hs' ht'
  dsimp only at h
  rw [truncate_mul] at h
  simpa only [M, D, oneHole_eliminate_truncate Ms _ m z R hz htotal,
    leafEnergySum_truncate_eq Ms m z R hz htotal f H hf] using h

/-- Specialization of the boxed hard-limit theorem to the actual upstream
physical completion marginal and its proved soft-signature family. -/
theorem context_box_leaf_transport_quarter {C : Type u} [Fintype C] [DecidableEq C]
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (Ms : List ℕ)
    (e : (C ⊕ Coordinates Bool Ms) ≃ SmallView (fun a : I × J => small a.1 a.2))
    (σ mC : C → ℕ) (m z : Bool → ℕ) (R W : ℕ)
    (hprefix : InBox mC σ)
    (hlarge : ∀ i j, small i j = false → 2 ≤ B i j)
    (hlower : ∀ U ∈ Ms, 2 ≤ U) (hupper : ∀ U ∈ Ms, U ≤ W)
    (hz : InBox m z) (htotal : (∑ i, z i) = R + 1)
    (H : (Coordinates Bool Ms → ℕ) → ℝ)
    (hs : 0 < oneHole (eliminate Ms (contextHard small B r c L Ms e σ)) z false)
    (ht : 0 < oneHole (eliminate Ms (contextHard small B r c L Ms e σ)) z true) :
    let f := contextHard small B r c L Ms e σ
    let g := truncate f (bounds m Ms) (R + Ms.sum)
    let s := oneHole (eliminate Ms f) z false
    let t := oneHole (eliminate Ms f) z true
    let aux := integerRemovalMatrix (auxiliaryKernel Ms g) z false true
    (oneHole (eliminate Ms (fun p => f p * H p)) z false / s -
      oneHole (eliminate Ms (fun p => f p * H p)) z true / t)^2 ≤
      (1 / s + 1 / t + (((W : ℝ) + 1)^2 / 2) * aux / (s * t)) *
        leafEnergySum Ms f H z := by
  apply integer_box_root_leaf_transport_quarter_limit Ms
    (contextSoft small B r c L Ms e σ) _ H
    (contextSoft_tendsto small B r c L Ms e σ) m z R W hlower hupper
    _ hz htotal hs ht
  filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with a ha
  exact ⟨contextSoft_nonnegative small B r c L Ms e σ a,
    contextSoft_slices small B r c L Ms e σ mC m R hprefix a ha hlarge⟩

lemma leafEnergySum_nonnegative {C : Type*} [Fintype C] [DecidableEq C]
    (Ms : List ℕ) (f H : (Coordinates C Ms → ℕ) → ℝ) (z : C → ℕ)
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ leafEnergySum Ms f H z := by
  rw [leafEnergySum_eq_edges Ms f H z hf]
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro edge _
  exact mul_nonneg (le_min (hf _) (hf _)) (sq_nonneg _)

/-- The source's repair domination with the sharpened quadratic coefficient. -/
theorem repaired_root_transport_quarter (s t c d W E Δ : ℝ)
    (hs : 0 < s) (ht : 0 < t) (hE : 0 ≤ E)
    (hc : c ≤ d * max s t)
    (htransport : Δ^2 ≤ (1 / s + 1 / t + ((W + 1)^2 / 2) * c / (s * t)) * E) :
    min s t * Δ^2 ≤ (2 + d * (W + 1)^2 / 2) * E := by
  have hcoef := root_coefficient_bound s t ((W + 1)^2 / 2) c d hs ht (by positivity) hc
  calc
    _ ≤ min s t * ((1 / s + 1 / t + ((W + 1)^2 / 2) * c / (s * t)) * E) :=
      mul_le_mul_of_nonneg_left htransport (le_min hs.le ht.le)
    _ = (min s t * (1 / s + 1 / t + ((W + 1)^2 / 2) * c / (s * t))) * E := by ring
    _ ≤ (2 + ((W + 1)^2 / 2) * d) * E := mul_le_mul_of_nonneg_right hcoef hE
    _ = _ := by ring

/-- Actual adjacent physical conditional means satisfy the quarter-coefficient
bound with literal physical leaf energy. The auxiliary mass is repaired only
after its box and total-degree truncation has been retained through the limit. -/
theorem adjacent_physical_leaf_transport_quarter
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I × J) (hs : small s.1 s.2 = true)
    (σ : I × J → ℕ) (U l : ℕ) (hU : 2 ≤ U) (hl0 : 1 ≤ l) (hlU : l ≤ U)
    (hB : ∀ i j, small i j = true → B i j = U)
    (hlarge : ∀ i j, small i j = false → 2 ≤ B i j)
    (hσ : ∀ a : Earlier small s, σ a.val.val ≤ U) {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i + rowLargeCount small i * L) (fun j => c j + columnLargeCount small j * L),
      ∀ i j, T.val.val i j ≤ B i j)
    (H : SmallProfile small → ℝ)
    (hleft : 0 < eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U (l - 1)))
    (hright : 0 < eliminate (widths (fun _ : Fin n => U))
      (contextHard small B r c L _ (contextEquiv small s hs e U) (prefixRaw small s σ U))
      (childProfile U l)) :
    let Ms := widths (fun _ : Fin n => U)
    let f := contextHard small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
    let a := eliminate Ms f (childProfile U (l - 1))
    let b := eliminate Ms f (childProfile U l)
    let h := fun p => H (assemble small s hs σ U e p)
    min a b * (eliminate Ms (fun p => f p * h p) (childProfile U (l - 1)) / a -
      eliminate Ms (fun p => f p * h p) (childProfile U l) / b)^2 ≤
      (2 + (n : ℝ) * ((U : ℝ) + 1)^2 / 2) *
        physicalLeafEnergy small s hs σ U l e (hardMarginal small B r c L) H := by
  dsimp only
  have htransport := context_box_leaf_transport_quarter small B r c L
    (widths (fun _ : Fin n => U))
    (contextEquiv small s hs e U) (prefixRaw small s σ U) (fun _ => U)
    (fun _ => U) (rootDisplay U l) U U (prefixRaw_inBox small s σ U hσ) hlarge
    (fun w hw => by rw [widths_constant_mem U w hw]; exact hU)
    (fun w hw => le_of_eq (widths_constant_mem U w hw))
    (rootDisplay_inBox U l hl0 hlU) (rootDisplay_total U l hlU)
    (fun p => H (assemble small s hs σ U e p))
    (by rw [rootDisplay_oneHole_false _ U l hl0 hlU]; exact hleft)
    (by rw [rootDisplay_oneHole_true]; exact hright)
  dsimp only at htransport
  simp only [rootDisplay_oneHole_false _ U l hl0 hlU, rootDisplay_oneHole_true,
    rootDisplay_removal _ U l hl0] at htransport
  have haux := auxiliary_mass_le_adjacent small B r c L s hs σ U l hl0 hlU hB hσ e hcap
  dsimp only at haux
  have h := repaired_root_transport_quarter _ _ _ n U _ _ hleft hright
    (leafEnergySum_nonnegative _ _ _ _ (contextHard_nonnegative small B r c L _ _ _))
    haux htransport
  have heq := leafEnergySum_eq_physicalLeafEnergy small s hs σ U l e
    (hardMarginal small B r c L) H (hardMarginal_nonnegative small B r c L)
  change leafEnergySum _ (contextHard small B r c L _ (contextEquiv small s hs e U)
    (prefixRaw small s σ U)) (fun p => H (assemble small s hs σ U e p)) _ = _ at heq
  rw [heq] at h
  exact h

/-- Canonical weighted adjacent contrast. A zero-mass child contributes zero;
the formula does not assert a conditional mean for that child. -/
noncomputable def ownerContrast (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) (o : Owner small U)
    (H : SmallProfile small → ℝ) : ℝ :=
  let e := suffixEnumeration small o.1.val
  let Ms := widths (fun _ : Fin (Fintype.card (Later small o.1.val)) => U)
  let σ := prefixExtension small o.1.val U o.2.2
  let f := contextHard small B r c L Ms (contextEquiv small o.1.val o.1.property e U)
    (prefixRaw small o.1.val σ U)
  let h := fun p => H (assemble small o.1.val o.1.property σ U e p)
  let a := eliminate Ms f (childProfile U o.2.1.val)
  let b := eliminate Ms f (childProfile U (o.2.1.val + 1))
  min a b * (eliminate Ms (fun p => f p * h p) (childProfile U o.2.1.val) / a -
    eliminate Ms (fun p => f p * h p) (childProfile U (o.2.1.val + 1)) / b)^2

lemma ownerEnergy_nonnegative (small : I → J → Bool) (U : ℕ)
    (o : Owner small U) (f H : SmallProfile small → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ ownerEnergy small U o f H := by
  unfold ownerEnergy
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro edge _
  exact mul_nonneg (le_min (hf _) (hf _)) (sq_nonneg _)

lemma min_contrast_of_positive (s t Δ B : ℝ)
    (hs : 0 ≤ s) (ht : 0 ≤ t) (hB : 0 ≤ B)
    (hpos : 0 < s → 0 < t → min s t * Δ^2 ≤ B) :
    min s t * Δ^2 ≤ B := by
  by_cases hsp : 0 < s
  · by_cases htp : 0 < t
    · exact hpos hsp htp
    · have ht0 : t = 0 := le_antisymm (le_of_not_gt htp) ht
      simpa only [ht0, min_eq_right hs, zero_mul] using hB
  · have hs0 : s = 0 := le_antisymm (le_of_not_gt hsp) hs
    simpa only [hs0, min_eq_left ht, zero_mul] using hB

/-- Every canonical physical owner obeys the localized adjacent comparison,
including owners with one or both endpoint masses zero. -/
theorem ownerContrast_le_ownerEnergy (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) (hU : 2 ≤ U)
    (hB : ∀ i j, small i j = true → B i j = U)
    (hlarge : ∀ i j, small i j = false → 2 ≤ B i j)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i + rowLargeCount small i * L) (fun j => c j + columnLargeCount small j * L),
      ∀ i j, T.val.val i j ≤ B i j)
    (H : SmallProfile small → ℝ) (o : Owner small U) :
    ownerContrast small B r c L U o H ≤
      (2 + (Fintype.card (Later small o.1.val) : ℝ) * ((U : ℝ) + 1)^2 / 2) *
        ownerEnergy small U o (hardMarginal small B r c L) H := by
  unfold ownerContrast
  dsimp only
  apply min_contrast_of_positive
  · exact eliminate_nonnegative _ _ (contextHard_nonnegative small B r c L _ _ _) _
  · exact eliminate_nonnegative _ _ (contextHard_nonnegative small B r c L _ _ _) _
  · exact mul_nonneg (by positivity)
      (ownerEnergy_nonnegative small U o _ H (hardMarginal_nonnegative small B r c L))
  · intro hleft hright
    have h := adjacent_physical_leaf_transport_quarter small B r c L
      o.1.val o.1.property (prefixExtension small o.1.val U o.2.2)
      U (o.2.1.val + 1) hU (by omega) (Nat.succ_le_of_lt o.2.1.isLt)
      hB hlarge (prefixExtension_bounded small o.1.val U o.2.2)
      (suffixEnumeration small o.1.val) hcap H
      (by simpa only [Nat.add_sub_cancel] using hleft) hright
    simpa only [Nat.add_sub_cancel, ownerEnergy, ownerEdges, physicalLeafEnergy] using h

lemma later_card_le (small : I → J → Bool) (s : Cells small) :
    Fintype.card (Later small s.val) ≤ Fintype.card (Cells small) - 1 := by
  have hlt : Fintype.card (Later small s.val) < Fintype.card (Cells small) :=
    Fintype.card_subtype_lt (x := s) (fun h => h.ne rfl)
  omega

/-- Sum of all actual weighted adjacent contrasts, over every exposed cell,
level, and genuine prefix. Global leaf ownership removes the extra charge
for exposure depth and level. Zero-mass contexts are included explicitly. -/
theorem sum_ownerContrast_le_physicalEnergy
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) (hU : 2 ≤ U)
    (hB : ∀ i j, small i j = true → B i j = U)
    (hlarge : ∀ i j, small i j = false → 2 ≤ B i j)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i + rowLargeCount small i * L) (fun j => c j + columnLargeCount small j * L),
      ∀ i j, T.val.val i j ≤ B i j)
    (H : SmallProfile small → ℝ) :
    (∑ o : Owner small U, ownerContrast small B r c L U o H) ≤
      (2 + ((Fintype.card (Cells small) - 1 : ℕ) : ℝ) * ((U : ℝ) + 1)^2 / 2) *
        physicalEnergy small B (hardMarginal small B r c L) H := by
  let K := 2 + ((Fintype.card (Cells small) - 1 : ℕ) : ℝ) * ((U : ℝ) + 1)^2 / 2
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hlocal (o : Owner small U) :
      ownerContrast small B r c L U o H ≤
        K * ownerEnergy small U o (hardMarginal small B r c L) H := by
    apply (ownerContrast_le_ownerEnergy small B r c L U hU hB hlarge hcap H o).trans
    apply mul_le_mul_of_nonneg_right _
      (ownerEnergy_nonnegative small U o _ H (hardMarginal_nonnegative small B r c L))
    have hn : (Fintype.card (Later small o.1.val) : ℝ) ≤
        ((Fintype.card (Cells small) - 1 : ℕ) : ℝ) := by
      exact_mod_cast later_card_le small o.1
    dsimp [K]
    nlinarith [sq_nonneg ((U : ℝ) + 1)]
  calc
    _ ≤ ∑ o : Owner small U, K * ownerEnergy small U o (hardMarginal small B r c L) H :=
      Finset.sum_le_sum (fun o _ => hlocal o)
    _ = K * ∑ o : Owner small U, ownerEnergy small U o (hardMarginal small B r c L) H := by
      rw [Finset.mul_sum]
    _ ≤ K * physicalEnergy small B (hardMarginal small B r c L) H :=
      mul_le_mul_of_nonneg_left
        (sum_ownerEnergy_hardMarginal_le small B r c L U (by omega) hB H) hK

end Math115.PhysicalLeafEnergy
