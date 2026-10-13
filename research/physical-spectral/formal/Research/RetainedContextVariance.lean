import Research.RetainedPhysicalSupport
import Research.RetainedRootNonnegative
import Research.ModeAnchorStencil
import Research.PositiveSupport
import Research.SpectralRetained
import Math115.PhysicalExposureVariance

namespace Math115.RetainedContextVariance
open OAI.ContingencyTables
open scoped BigOperators Classical Topology
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles
open ExcessContextProfiles SmallGraphProfiles FactorialSignatures IntegerBoxTruncation
open FirstPaperPhysicalMarginal FirstPaperContextTransport Filter
open PaddedCompletions CompletionCounts Math115.PhysicalLeafEnergy
open Math115.RetainedRootPhysical Math115.RetainedPhysicalCap
open Research.RetainedStencilSum Research.PositiveSupport
open FiniteExposureVariance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable section

def contextWeight (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s) :=
  contextHard small B r c L (widths (fun _ : Fin n => U))
    (contextEquiv small s hs e U) (prefixRaw small s σ U)

def childMass (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s) (j : ℕ) : ℝ :=
  eliminate (widths (fun _ : Fin n => U)) (contextWeight small B r c L s hs σ U e) (childProfile U j)

def childMean (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s)
    (H : SmallProfile small → ℝ) (j : ℕ) : ℝ :=
  eliminate (widths (fun _ : Fin n => U))
    (fun p => contextWeight small B r c L s hs σ U e p * H (assemble small s hs σ U e p))
    (childProfile U j) / childMass small B r c L s hs σ U e j

def boxedWeight (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s) :=
  truncate (contextWeight small B r c L s hs σ U e)
    (bounds (fun _ : Bool => U) (widths (fun _ : Fin n => U)))
    (U+(widths (fun _ : Fin n => U)).sum)

/-- One fixed boxed kernel for the entire context. Only invalid coordinate
boundary removals are zero; exterior positive-support values remain present. -/
def correction (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s) (j : ℕ) : ℝ :=
  if 1≤j ∧ j≤U then correctionKernel (widths (fun _ : Fin n => U))
    (boxedWeight small B r c L s hs σ U e) (auxRoot U j) else 0

lemma childMass_nonnegative (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s) (j : ℕ) :
    0 ≤ childMass small B r c L s hs σ U e j :=
  eliminate_nonnegative _ _ (contextHard_nonnegative small B r c L _ _ _) _

lemma childMass_noValley (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) (hU : 2≤U)
    (hlarge : ∀ i j,small i j=false → 2≤B i j)
    (hσ : ∀ a : Earlier small s,σ a.val.val≤U) {n : ℕ} (e : Fin n ≃ Later small s) :
    NoValley (childMass small B r c L s hs σ U e) U := by
  intro a j b haj hjb hb
  exact context_child_minimum small B r c L _ (contextEquiv small s hs e U)
    (prefixRaw small s σ U) (fun _ => U) U (prefixRaw_inBox small s σ U hσ)
    hlarge (fun w hw => by rw [widths_constant_mem U w hw]; exact hU) a j b haj hjb hb

lemma correction_nonnegative (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) {n : ℕ} (e : Fin n ≃ Later small s) (j : ℕ) :
    0 ≤ correction small B r c L s hs σ U e j := by
  unfold correction
  split_ifs
  · exact physical_correction_nonnegative small B r c L s hs σ U e _
  · exact le_rfl

lemma stencil_eq_coefficient (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hl1 : 1≤l) (hlU : l≤U)
    {n : ℕ} (e : Fin n ≃ Later small s) :
    stencil (childMass small B r c L s hs σ U e) (correction small B r c L s hs σ U e) l =
      retainedRootCoefficient (integerRemovalMatrix
        (correctionKernel (widths (fun _ : Fin n => U)) (boxedWeight small B r c L s hs σ U e))
        (rootDisplay U l)) (childMass small B r c L s hs σ U e (l-1))
          (childMass small B r c L s hs σ U e l) := by
  rw [retainedRootCoefficient_shift _ U l _ _ hl1 hlU]
  unfold stencil correction
  rw [ite_eq_left (show 1≤l ∧ l≤U from ⟨hl1,hlU⟩)]
  have hleft : (1≤l-1 ∧ l-1≤U) ↔ 2≤l := by omega
  have hright : (1≤l+1 ∧ l+1≤U) ↔ l<U := by omega
  simp only [hleft,hright]
  ring

lemma stencil_nonnegative (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hU : 2≤U) (hl1 : 1≤l) (hlU : l≤U)
    (hlarge : ∀ i j,small i j=false → 2≤B i j)
    (hσ : ∀ a : Earlier small s,σ a.val.val≤U) {n : ℕ} (e : Fin n ≃ Later small s)
    (hleft : 0<childMass small B r c L s hs σ U e (l-1))
    (hright : 0<childMass small B r c L s hs σ U e l) :
    0 ≤ stencil (childMass small B r c L s hs σ U e) (correction small B r c L s hs σ U e) l := by
  rw [stencil_eq_coefficient small B r c L s hs σ U l hl1 hlU e]
  let Ms := widths (fun _ : Fin n => U)
  let F := contextSoft small B r c L Ms (contextEquiv small s hs e U) (prefixRaw small s σ U)
  let f := contextWeight small B r c L s hs σ U e
  let M := bounds (fun _ : Bool => U) Ms
  let D := U+Ms.sum
  have hz := rootDisplay_inBox U l hl1 hlU
  have ht := rootDisplay_total U l hlU
  have hsoft : ∀ᶠ t in atTop, (∀ x,0≤truncate (F t) M D x) ∧
      PositiveSlice (truncate (F t) M D) M D ∧ RemovalSlice (truncate (F t) M D) M D := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht0
    have hF := contextSoft_slices small B r c L Ms (contextEquiv small s hs e U)
      (prefixRaw small s σ U) (fun _ => U) (fun _ => U) U
      (prefixRaw_inBox small s σ U hσ) t ht0 hlarge
    exact truncate_all_slices (F t) M D
      (contextSoft_nonnegative small B r c L Ms _ _ t) hF.1 hF.2
  have h := retainedRootCoefficient_nonnegative_limit Ms (fun t => truncate (F t) M D)
    (truncate f M D)
    (truncate_tendsto F f M D (contextSoft_tendsto small B r c L Ms _ _))
    (fun _ => U) (rootDisplay U l) U
    (fun w hw => by rw [widths_constant_mem U w hw]; exact hU) hsoft hz ht
    (by rw [oneHole_eliminate_truncate Ms f (fun _=>U) (rootDisplay U l) U hz ht,
        rootDisplay_oneHole_false _ U l hl1 hlU]; exact hleft)
    (by rw [oneHole_eliminate_truncate Ms f (fun _=>U) (rootDisplay U l) U hz ht,
        rootDisplay_oneHole_true]; exact hright)
  simpa only [Ms,M,D,f,boxedWeight,childMass,oneHole_eliminate_truncate Ms f (fun _=>U)
    (rootDisplay U l) U hz ht,rootDisplay_oneHole_false _ U l hl1 hlU,
    rootDisplay_oneHole_true] using h

lemma correction_cap (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hl1 : 1≤l) (hlU : l≤U)
    (hB : ∀ i j,small i j=true → B i j=U)
    (hσ : ∀ a : Earlier small s,σ a.val.val≤U) {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j,T.val.val i j≤B i j) :
    correction small B r c L s hs σ U e l ≤
      (n:ℝ)*(Math115.RetainedRoot.quarterProduct U:ℝ)*
        max (childMass small B r c L s hs σ U e (l-1)) (childMass small B r c L s hs σ U e l) := by
  unfold correction
  rw [ite_eq_left (show 1≤l ∧ l≤U from ⟨hl1,hlU⟩)]
  simpa only [childMass,contextWeight,boxedWeight] using
    physical_correction_le_adjacent small B r c L s hs σ U l hl1 hlU hB hσ e hcap

lemma leafEnergy_nonnegative (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) {n : ℕ} (e : Fin n ≃ Later small s) (H : SmallProfile small → ℝ) :
    0 ≤ physicalLeafEnergy small s hs σ U l e (hardMarginal small B r c L) H := by
  unfold physicalLeafEnergy
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro p _
  exact mul_nonneg (le_min (hardMarginal_nonnegative small B r c L _)
    (hardMarginal_nonnegative small B r c L _)) (sq_nonneg _)

lemma adjacent_increment_bound (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U l : ℕ) (hU : 2≤U) (hl1 : 1≤l) (hlU : l≤U)
    (hlarge : ∀ i j,small i j=false → 2≤B i j)
    (hσ : ∀ a : Earlier small s,σ a.val.val≤U) {n : ℕ} (e : Fin n ≃ Later small s)
    (H : SmallProfile small → ℝ)
    (hleft : 0<childMass small B r c L s hs σ U e (l-1))
    (hright : 0<childMass small B r c L s hs σ U e l) :
    (childMean small B r c L s hs σ U e H l-childMean small B r c L s hs σ U e H (l-1))^2 ≤
      stencil (childMass small B r c L s hs σ U e) (correction small B r c L s hs σ U e) l*
        physicalLeafEnergy small s hs σ U l e (hardMarginal small B r c L) H := by
  rw [stencil_eq_coefficient small B r c L s hs σ U l hl1 hlU e]
  have ht := adjacent_physical_box_leaf_transport_retained small B r c L s hs σ U l hU hl1 hlU
    hlarge hσ e H hleft hright
  convert ht using 1 <;> dsimp only [childMean,childMass,contextWeight,boxedWeight] <;> ring

lemma stencil_shift (z c : ℕ → ℝ) (α l : ℕ) (hl : 1≤l) :
    stencil (fun j => z (α+j)) (fun j => c (α+j)) l = stencil z c (α+l) := by
  unfold stencil
  dsimp only
  rw [show α+(l-1)=α+l-1 by omega,show α+(l+1)=(α+l)+1 by omega]

/-- Actual physical context bound, using its own uniform U boxed kernel.
No context/global variance, correction cap or unimodality premise is assumed.
Zero and singleton support are included. This is the mode-anchor coefficient;
the stronger spectral theorem can replace the same exact adapter. -/
theorem context_variance_mode_bound
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) (hU : 2≤U)
    (hB : ∀ i j,small i j=true → B i j=U)
    (hlarge : ∀ i j,small i j=false → 2≤B i j)
    (hσ : ∀ a : Earlier small s,σ a.val.val≤U) {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j,T.val.val i j≤B i j) (H : SmallProfile small → ℝ) :
    variance (fun j : Fin (U+1) => childMass small B r c L s hs σ U e j.val)
      (fun j => childMean small B r c L s hs σ U e H j.val) ≤
      ((U:ℝ)*((U:ℝ)+1)+2*((n:ℝ)*(Math115.RetainedRoot.quarterProduct U:ℝ))*(U:ℝ))*
        (∑ l ∈ Finset.Icc 1 U,physicalLeafEnergy small s hs σ U l e (hardMarginal small B r c L) H) := by
  let z := childMass small B r c L s hs σ U e
  let h := childMean small B r c L s hs σ U e H
  let c0 := correction small B r c L s hs σ U e
  let E := fun l => physicalLeafEnergy small s hs σ U l e (hardMarginal small B r c L) H
  let K : ℝ := (n:ℝ)*(Math115.RetainedRoot.quarterProduct U:ℝ)
  have hK : 0≤K := by dsimp [K]; positivity
  have hz (j : ℕ) (_hj : j≤U) : 0≤z j := childMass_nonnegative small B r c L s hs σ U e j
  have hE (j : ℕ) : 0≤E j := leafEnergy_nonnegative small B r c L s hs σ U j e H
  have hsumE : 0 ≤ ∑ l ∈ Finset.Icc 1 U,E l := Finset.sum_nonneg (fun l _ => hE l)
  by_cases hne : ∃ i≤U,0<z i
  · obtain ⟨α,β,m,hsupp,hm,hpos,hleftmono,hrightmono,hvar⟩ :=
      positive_support_restriction z h U hz (childMass_noValley small B r c L s hs σ U hU hlarge hσ e) hne
    let N := β-α
    have hN : N≤U := (Nat.sub_le β α).trans hsupp.upper
    have hpath := Research.ModeAnchorStencil.retained_mode_variance_bound
      (fun i => z (α+i)) (fun i => h (α+i)) (fun i => c0 (α+i)) (fun l => E (α+l)) K N m
      hm hK hpos hleftmono hrightmono
      (fun i _ => correction_nonnegative small B r c L s hs σ U e (α+i))
      (by
        intro j hj1 hjN
        have hlU : α+j≤U := by have := hsupp.ordered; have := hsupp.upper; dsimp [N] at hjN; omega
        have hl1 : 1≤α+j := by omega
        have hc := correction_cap small B r c L s hs σ U (α+j) hl1 hlU hB hσ e hcap
        simpa only [K,z,c0,show α+(j-1)=α+j-1 by omega] using hc)
      (by
        intro l hl
        obtain ⟨hl1,hlN⟩ := Finset.mem_Icc.mp hl
        rw [stencil_shift z c0 α l hl1]
        apply stencil_nonnegative small B r c L s hs σ U (α+l) hU (by omega)
          (by have := hsupp.ordered; have := hsupp.upper; dsimp [N] at hlN; omega) hlarge hσ e
        · have hh := hpos (l-1) (by omega); simpa only [show α+(l-1)=α+l-1 by omega] using hh
        · exact hpos l hlN)
      (fun l _ => hE (α+l))
      (by
        intro l hl
        obtain ⟨hl1,hlN⟩ := Finset.mem_Icc.mp hl
        rw [stencil_shift z c0 α l hl1]
        have ht := adjacent_increment_bound small B r c L s hs σ U (α+l) hU (by omega)
          (by have := hsupp.ordered; have := hsupp.upper; dsimp [N] at hlN; omega) hlarge hσ e H
          (by have hh := hpos (l-1) (by omega); simpa only [show α+(l-1)=α+l-1 by omega] using hh)
          (hpos l hlN)
        simpa only [z,h,c0,E,show α+(l-1)=α+l-1 by omega] using ht)
    have hsE := support_energy_sum_le E U α β hsupp.ordered hsupp.upper (fun j _ _ => hE j)
    have hcoef := Research.ModeAnchorStencil.pathCoefficient_mono K N U hK hN
    change variance (fun j : Fin (U+1) => z j.val) (fun j => h j.val) ≤ _
    rw [hvar]
    exact hpath.trans (mul_le_mul hcoef hsE
      (Finset.sum_nonneg (fun l _ => hE (α+l))) (by positivity))
  · have hz0 : (fun j : Fin (U+1) => z j.val) = fun _ => 0 := by
      funext j
      have hj := hz j.val (by omega)
      have hn : ¬0<z j.val := by intro hp; exact hne ⟨j.val,by omega,hp⟩
      linarith
    change variance (fun j : Fin (U+1) => z j.val) (fun j => h j.val) ≤ _
    rw [hz0]
    simp only [variance,zero_mul,Finset.sum_const_zero]
    exact mul_nonneg (by positivity) hsumE


/-- Actual physical context bound, using its own uniform U boxed kernel.
No context/global variance, correction cap or unimodality premise is assumed.
Zero and singleton support are included. The actual positive support is built from its physical masses. -/
theorem context_variance_spectral_bound
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) (hU : 2≤U)
    (hB : ∀ i j,small i j=true → B i j=U)
    (hlarge : ∀ i j,small i j=false → 2≤B i j)
    (hσ : ∀ a : Earlier small s,σ a.val.val≤U) {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j,T.val.val i j≤B i j) (H : SmallProfile small → ℝ) :
    variance (fun j : Fin (U+1) => childMass small B r c L s hs σ U e j.val)
      (fun j => childMean small B r c L s hs σ U e H j.val) ≤
      (((min (r s.1) (c s.2):ℕ):ℝ)*(((min (r s.1) (c s.2):ℕ):ℝ)+1)+2*((n:ℝ)*(Math115.RetainedRoot.quarterProduct U:ℝ)))*
        (∑ l ∈ Finset.Icc 1 U,physicalLeafEnergy small s hs σ U l e (hardMarginal small B r c L) H) := by
  let z := childMass small B r c L s hs σ U e
  let h := childMean small B r c L s hs σ U e H
  let c0 := correction small B r c L s hs σ U e
  let E := fun l => physicalLeafEnergy small s hs σ U l e (hardMarginal small B r c L) H
  let W := min (r s.1) (c s.2)
  let K : ℝ := (n:ℝ)*(Math115.RetainedRoot.quarterProduct U:ℝ)
  have hK : 0≤K := by dsimp [K]; positivity
  have hz (j : ℕ) (_hj : j≤U) : 0≤z j := childMass_nonnegative small B r c L s hs σ U e j
  have hE (j : ℕ) : 0≤E j := leafEnergy_nonnegative small B r c L s hs σ U j e H
  have hsumE : 0 ≤ ∑ l ∈ Finset.Icc 1 U,E l := Finset.sum_nonneg (fun l _ => hE l)
  by_cases hne : ∃ i≤U,0<z i
  · obtain ⟨α,β,m,hsupp,hm,hpos,hleftmono,hrightmono,hvar⟩ :=
      positive_support_restriction z h U hz (childMass_noValley small B r c L s hs σ U hU hlarge hσ e) hne
    let N := β-α
    have hβW : β≤W := by
      exact Math115.RetainedPhysicalSupport.positive_physical_child_le_original small B r c L s hs σ U hB hσ
        ⟨β,by have := hsupp.upper; omega⟩ e hcap (hsupp.positive β hsupp.ordered le_rfl)
    have hN : N≤W := (Nat.sub_le β α).trans hβW
    by_cases hN0 : N=0
    · have hβα : β=α := by dsimp [N] at hN0; have := hsupp.ordered; omega
      have hv0 := singleton_support_variance z h U α (by simpa only [hβα] using hsupp)
      change variance (fun j : Fin (U+1) => z j.val) (fun j => h j.val) ≤ _
      rw [hv0]
      exact mul_nonneg (by positivity) hsumE
    have hN1 : 1≤N := by omega
    have hpath := Research.SpectralRetained.retained_spectral_variance_bound
      (fun i => z (α+i)) (fun i => h (α+i)) (fun i => c0 (α+i)) (fun l => E (α+l)) K N m
      hN1 hm hK hpos hleftmono hrightmono
      (fun i _ => correction_nonnegative small B r c L s hs σ U e (α+i))
      (by
        intro j hj1 hjN
        have hlU : α+j≤U := by have := hsupp.ordered; have := hsupp.upper; dsimp [N] at hjN; omega
        have hl1 : 1≤α+j := by omega
        have hc := correction_cap small B r c L s hs σ U (α+j) hl1 hlU hB hσ e hcap
        simpa only [K,z,c0,show α+(j-1)=α+j-1 by omega] using hc)
      (by
        intro l hl
        obtain ⟨hl1,hlN⟩ := Finset.mem_Icc.mp hl
        rw [stencil_shift z c0 α l hl1]
        apply stencil_nonnegative small B r c L s hs σ U (α+l) hU (by omega)
          (by have := hsupp.ordered; have := hsupp.upper; dsimp [N] at hlN; omega) hlarge hσ e
        · have hh := hpos (l-1) (by omega); simpa only [show α+(l-1)=α+l-1 by omega] using hh
        · exact hpos l hlN)
      (fun l _ => hE (α+l))
      (by
        intro l hl
        obtain ⟨hl1,hlN⟩ := Finset.mem_Icc.mp hl
        rw [stencil_shift z c0 α l hl1]
        have ht := adjacent_increment_bound small B r c L s hs σ U (α+l) hU (by omega)
          (by have := hsupp.ordered; have := hsupp.upper; dsimp [N] at hlN; omega) hlarge hσ e H
          (by have hh := hpos (l-1) (by omega); simpa only [show α+(l-1)=α+l-1 by omega] using hh)
          (hpos l hlN)
        simpa only [z,h,c0,E,show α+(l-1)=α+l-1 by omega] using ht)
    have hsE := support_energy_sum_le E U α β hsupp.ordered hsupp.upper (fun j _ _ => hE j)
    have hbase : (N:ℝ)*((N:ℝ)+1)≤(W:ℝ)*((W:ℝ)+1) := by
      exact_mod_cast Nat.mul_le_mul hN (Nat.add_le_add_right hN 1)
    have hcoef : (N:ℝ)*((N:ℝ)+1)+2*K≤(W:ℝ)*((W:ℝ)+1)+2*K := by linarith only [hbase]
    change variance (fun j : Fin (U+1) => z j.val) (fun j => h j.val) ≤ _
    rw [hvar]
    exact hpath.trans (mul_le_mul hcoef hsE
      (Finset.sum_nonneg (fun l _ => hE (α+l))) (by positivity))
  · have hz0 : (fun j : Fin (U+1) => z j.val) = fun _ => 0 := by
      funext j
      have hj := hz j.val (by omega)
      have hn : ¬0<z j.val := by intro hp; exact hne ⟨j.val,by omega,hp⟩
      linarith
    change variance (fun j : Fin (U+1) => z j.val) (fun j => h j.val) ≤ _
    rw [hz0]
    simp only [variance,zero_mul,Finset.sum_const_zero]
    exact mul_nonneg (by positivity) hsumE

/-- At a genuinely small cell, the physical support stops below U. Together
with the same U-kernel quarter cap this gives an actual U² context allowance. -/
theorem context_variance_spectral_small_bound
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) (hU : 2≤U)
    (hmargin : min (r s.1) (c s.2)<U)
    (hB : ∀ i j,small i j=true → B i j=U)
    (hlarge : ∀ i j,small i j=false → 2≤B i j)
    (hσ : ∀ a : Earlier small s,σ a.val.val≤U) {n : ℕ} (e : Fin n ≃ Later small s)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j,T.val.val i j≤B i j) (H : SmallProfile small → ℝ) :
    variance (fun j : Fin (U+1) => childMass small B r c L s hs σ U e j.val)
      (fun j => childMean small B r c L s hs σ U e H j.val) ≤
      (((n+1:ℕ):ℝ)*(U:ℝ)^2)*
        (∑ l ∈ Finset.Icc 1 U,physicalLeafEnergy small s hs σ U l e (hardMarginal small B r c L) H) := by
  have hc := context_variance_spectral_bound small B r c L s hs σ U hU hB hlarge hσ e hcap H
  have hq := Math115.RetainedRoot.quarterProduct_bound U hU
  have hbase : (((min (r s.1) (c s.2):ℕ):ℝ))*
      ((((min (r s.1) (c s.2):ℕ):ℝ))+1)≤(U:ℝ)^2 := by
    have hmul := Nat.mul_le_mul (Nat.le_of_lt hmargin) (Nat.succ_le_of_lt hmargin)
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_two] using
      (show (((min (r s.1) (c s.2)*(min (r s.1) (c s.2)+1):ℕ):ℝ))≤((U*U:ℕ):ℝ) by exact_mod_cast hmul)
  have hquarter := mul_le_mul_of_nonneg_left hq (show 0≤2*(n:ℝ) by positivity)
  have hcoef : (((min (r s.1) (c s.2):ℕ):ℝ))*
      ((((min (r s.1) (c s.2):ℕ):ℝ))+1)+2*((n:ℝ)*(Math115.RetainedRoot.quarterProduct U:ℝ)) ≤
      (((n+1:ℕ):ℝ)*(U:ℝ)^2) := by
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith only [hbase,hquarter]
  have hsum : 0≤∑ l ∈ Finset.Icc 1 U,
      physicalLeafEnergy small s hs σ U l e (hardMarginal small B r c L) H :=
    Finset.sum_nonneg (fun l _ => leafEnergy_nonnegative small B r c L s hs σ U l e H)
  exact hc.trans (mul_le_mul_of_nonneg_right hcoef hsum)

/-- The actual first-paper classification discharges the small-margin premise;
this does not rebuild or alter its original uniform-U context/kernel. -/
theorem firstPaper_context_variance_spectral_bound
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (hU : 2≤U)
    (s : I×J) (hs : firstPaperSmall r c U s.1 s.2=true) (σ : I×J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (hσ : ∀ a : Earlier (firstPaperSmall r c U) s,σ a.val.val≤U)
    {n : ℕ} (e : Fin n ≃ Later (firstPaperSmall r c U) s)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),
      ∀ i j,T.val.val i j≤B i j) (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    variance (fun j : Fin (U+1) => childMass (firstPaperSmall r c U) B r c L s hs σ U e j.val)
      (fun j => childMean (firstPaperSmall r c U) B r c L s hs σ U e H j.val) ≤
      (((n+1:ℕ):ℝ)*(U:ℝ)^2)*
        (∑ l ∈ Finset.Icc 1 U,physicalLeafEnergy (firstPaperSmall r c U) s hs σ U l e
          (hardMarginal (firstPaperSmall r c U) B r c L) H) := by
  have hmargin : min (r s.1) (c s.2)<U := by
    by_contra hn
    have hm := le_min_iff.mp (le_of_not_gt hn)
    have hf := (firstPaperSmall_false_iff r c U s.1 s.2).mpr hm
    simp only [hs] at hf
    contradiction
  exact context_variance_spectral_small_bound (firstPaperSmall r c U) B r c L s hs σ U hU
    hmargin hB hlarge hσ e hcap H

/-- The genuine source paperCapacity at arbitrary U,L discharges hB,
hlarge and the complete ordinary residual-table capacity premise. Thus this
actual context bound has no capacity, correction or variance hypothesis. -/
theorem paperCapacity_context_variance_spectral_bound
    (r : I → ℕ) (c : J → ℕ) (U L d : ℕ) (hU : 2≤U)
    (hd : Fintype.card I*Fintype.card J≤d)
    (s : I×J) (hs : firstPaperSmall r c U s.1 s.2=true) (σ : I×J → ℕ)
    (hσ : ∀ a : Earlier (firstPaperSmall r c U) s,σ a.val.val≤U)
    {n : ℕ} (e : Fin n ≃ Later (firstPaperSmall r c U) s)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    let small := firstPaperSmall r c U
    let B := paperCapacity small r d L U
    variance (fun j : Fin (U+1) => childMass small B r c L s hs σ U e j.val)
      (fun j => childMean small B r c L s hs σ U e H j.val) ≤
      (((n+1:ℕ):ℝ)*(U:ℝ)^2)*
        (∑ l ∈ Finset.Icc 1 U,physicalLeafEnergy small s hs σ U l e
          (hardMarginal small B r c L) H) := by
  dsimp only
  apply firstPaper_context_variance_spectral_bound r c U L _ hU s hs σ _ _ hσ e _ H
  · intro i j hij
    simp only [paperCapacity,hij,↓reduceIte]
  · intro i j hij
    simp only [paperCapacity,hij,Bool.false_eq_true,↓reduceIte]
    omega
  · exact paper_residual_capacity r c d L U hd

end
end Math115.RetainedContextVariance
