import Research.RetainedRepairSquare

namespace Research.UniformContextVariance
open OAI.ContingencyTables
open scoped BigOperators Classical Topology
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles
open ExcessContextProfiles SmallGraphProfiles FactorialSignatures IntegerBoxTruncation
open FirstPaperPhysicalMarginal FirstPaperContextTransport Filter
open PaddedCompletions CompletionCounts RowMajorEnumeration FiniteExposureVariance
open Math115.PhysicalLeafEnergy Math115.PhysicalExposureVariance Math115.PhysicalFullVariance
open Math115.PhysicalRepairRefinement Math115.RetainedRootPhysical Math115.RetainedPhysicalCap
open Math115.RetainedContextVariance Math115.RetainedTransversalVariance
open Research.RetainedStencilSum Research.PositiveSupport

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

theorem context_variance_of_correction_cap
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ) (s : I×J) (hs : small s.1 s.2=true)
    (σ : I×J → ℕ) (U : ℕ) (hU : 2≤U)
    (hB : ∀ i j,small i j=true → B i j=U)
    (hlarge : ∀ i j,small i j=false → 2≤B i j)
    (hσ : ∀ a : Earlier small s,σ a.val.val≤U) {n : ℕ} (e : Fin n ≃ Later small s)
    (K : ℝ) (hK : 0≤K)
    (hcorrection : ∀ l,1≤l → l≤U → correction small B r c L s hs σ U e l ≤
      K*max (childMass small B r c L s hs σ U e (l-1))
        (childMass small B r c L s hs σ U e l))
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i+rowLargeCount small i*L) (fun j => c j+columnLargeCount small j*L),
      ∀ i j,T.val.val i j≤B i j) (H : SmallProfile small → ℝ) :
    variance (fun j : Fin (U+1) => childMass small B r c L s hs σ U e j.val)
      (fun j => childMean small B r c L s hs σ U e H j.val) ≤
      (((min (r s.1) (c s.2):ℕ):ℝ)*(((min (r s.1) (c s.2):ℕ):ℝ)+1)+2*K)*
        (∑ l ∈ Finset.Icc 1 U,physicalLeafEnergy small s hs σ U l e (hardMarginal small B r c L) H) := by
  let z := childMass small B r c L s hs σ U e
  let h := childMean small B r c L s hs σ U e H
  let c0 := correction small B r c L s hs σ U e
  let E := fun l => physicalLeafEnergy small s hs σ U l e (hardMarginal small B r c L) H
  let W := min (r s.1) (c s.2)
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
        have hc := hcorrection (α+j) hl1 hlU
        simpa only [z,c0,show α+(j-1)=α+j-1 by omega] using hc)
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

/-- First-paper original margins stop positive support before U. The sole
new analytic input is a proved cap on the SAME fixed boxed correction kernel. -/
theorem firstPaper_context_variance_of_correction_cap
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (hU : 2≤U)
    (s : I×J) (hs : firstPaperSmall r c U s.1 s.2=true) (σ : I×J → ℕ)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (hσ : ∀ a : Earlier (firstPaperSmall r c U) s,σ a.val.val≤U)
    {n : ℕ} (e : Fin n ≃ Later (firstPaperSmall r c U) s)
    (K : ℝ) (hK : 0≤K)
    (hcorrection : ∀ l,1≤l → l≤U → correction (firstPaperSmall r c U) B r c L s hs σ U e l ≤
      K*max (childMass (firstPaperSmall r c U) B r c L s hs σ U e (l-1))
        (childMass (firstPaperSmall r c U) B r c L s hs σ U e l))
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j≤B i j)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    variance (fun j : Fin (U+1) => childMass (firstPaperSmall r c U) B r c L s hs σ U e j.val)
      (fun j => childMean (firstPaperSmall r c U) B r c L s hs σ U e H j.val) ≤
      ((U:ℝ)*((U:ℝ)-1)+2*K)*
        (∑ l ∈ Finset.Icc 1 U,physicalLeafEnergy (firstPaperSmall r c U) s hs σ U l e
          (hardMarginal (firstPaperSmall r c U) B r c L) H) := by
  have hm : min (r s.1) (c s.2)<U := by
    have hsel : r s.1<U ∨ c s.2<U := by simpa only [firstPaperSmall,decide_eq_true_eq] using hs
    rcases hsel with h | h
    · exact lt_of_le_of_lt (min_le_left _ _) h
    · exact lt_of_le_of_lt (min_le_right _ _) h
  have hv := context_variance_of_correction_cap (firstPaperSmall r c U) B r c L s hs σ U hU
    hB hlarge hσ e K hK hcorrection hcap H
  have hprod := Nat.mul_le_mul (show min (r s.1) (c s.2)≤U-1 by omega)
    (Nat.succ_le_of_lt hm)
  have hbase : ((min (r s.1) (c s.2):ℕ):ℝ)*(((min (r s.1) (c s.2):ℕ):ℝ)+1) ≤
      (U:ℝ)*((U:ℝ)-1) := by
    have hcast : ((min (r s.1) (c s.2):ℕ):ℝ)*(((min (r s.1) (c s.2):ℕ):ℝ)+1) ≤
        ((U-1:ℕ):ℝ)*(U:ℝ) := by exact_mod_cast hprod
    rw [Nat.cast_sub (by omega),Nat.cast_one] at hcast
    nlinarith only [hcast]
  exact hv.trans (mul_le_mul_of_nonneg_right (by linarith only [hbase])
    (Finset.sum_nonneg (fun l _ => leafEnergy_nonnegative _ B r c L s hs σ U l e H)))

/-- A proved uniform bound for literal canonical contexts and their OWN leaf owners. -/
def CanonicalContextBound (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (CT : ℝ) : Prop :=
  ∀ (s : Cells (firstPaperSmall r c U))
    (τ : Earlier (firstPaperSmall r c U) s.val → Fin (U+1))
    (H : SmallProfile (firstPaperSmall r c U) → ℝ),
    variance (fun j : Fin (U+1) => canonicalChildMass (firstPaperSmall r c U) B r c L U s τ j.val)
      (fun j => canonicalChildMean (firstPaperSmall r c U) B r c L U s τ H j.val) ≤
      CT*∑ j : Fin U,ownerEnergy (firstPaperSmall r c U) U ⟨s,j,τ⟩
        (hardMarginal (firstPaperSmall r c U) B r c L) H

/-- Explicit certificate for the literal fixed boxed kernels in every context. -/
def UniformCorrectionCap (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (K : ℝ) : Prop :=
  ∀ (s : I×J) (hs : firstPaperSmall r c U s.1 s.2=true) (σ : I×J → ℕ),
    (∀ a : Earlier (firstPaperSmall r c U) s,σ a.val.val≤U) →
    ∀ {n : ℕ} (e : Fin n ≃ Later (firstPaperSmall r c U) s) (l : ℕ),
      1≤l → l≤U → correction (firstPaperSmall r c U) B r c L s hs σ U e l ≤
        K*max (childMass (firstPaperSmall r c U) B r c L s hs σ U e (l-1))
          (childMass (firstPaperSmall r c U) B r c L s hs σ U e l)

theorem canonical_bound_of_correction_cap
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (hU : 2≤U)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j≤B i j)
    (K : ℝ) (hK : 0≤K) (hcorrection : UniformCorrectionCap r c U L B K) :
    CanonicalContextBound r c U L B ((U:ℝ)*((U:ℝ)-1)+2*K) := by
  intro s τ H
  let small := firstPaperSmall r c U
  let σ := prefixExtension small s.val U τ
  let e := suffixEnumeration small s.val
  have hσ := prefixExtension_bounded small s.val U τ
  have hv := firstPaper_context_variance_of_correction_cap r c U L B hU s.val s.property σ
    hB hlarge hσ e K hK (hcorrection s.val s.property σ hσ e) hcap H
  rw [sum_Icc_eq_fin_succ] at hv
  exact hv

theorem canonical_bound_mono (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (CT DT : ℝ) (hcontext : CanonicalContextBound r c U L B CT) (hCD : CT≤DT) :
    CanonicalContextBound r c U L B DT := by
  intro s τ H
  exact (hcontext s τ H).trans (mul_le_mul_of_nonneg_right hCD
    (Finset.sum_nonneg (fun j _ => ownerEnergy_nonnegative _ U _ _ _
      (hardMarginal_nonnegative _ B r c L))))

/-- The unchanged source square-root repair coefficient at a proved balanced CT. -/
def repairCoefficient (p : ℕ) (CT : ℝ) : ℝ := CT+(Real.sqrt ((p:ℝ)^2*CT)+1)^2

theorem word_context_variance_of_context_bound
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (CT : ℝ) (_hCT : 0≤CT)
    (hcontext : CanonicalContextBound r c U L B CT) (_hU : 2≤U)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (_hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (_hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j≤B i j)
    (k : Fin (Fintype.card (Cells (firstPaperSmall r c U))))
    (τ : Fin k.val → Fin (U+1)) (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    let small := firstPaperSmall r c U
    let w := wordWeight small B r c L U
    let G := wordObservable small U H
    let cw := fun j : Fin (U+1) => fibreWeight
      (fibreWeight w (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j
    variance (fun j => ∑ a,cw j a) (fun j => mean (cw j) G) ≤
      CT*
        ∑ j : Fin U,ownerEnergy small U ⟨enumeration small k,j,earlierWordChoices small U k τ⟩
          (hardMarginal small B r c L) H := by
  dsimp only
  let small := firstPaperSmall r c U
  let s := enumeration small k
  let η := earlierWordChoices small U k τ
  let cw := fun j : Fin (U+1) => fibreWeight
    (fibreWeight (wordWeight small B r c L U) (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j
  have hz (j : Fin (U+1)) : (∑ a,cw j a)=canonicalChildMass small B r c L U s η j.val :=
    (canonical_eliminate_eq_word_fibre small B U hB k τ j (hardMarginal small B r c L)).symm
  have hm (j : Fin (U+1)) : (∑ a,cw j a*wordObservable small U H a)=
      eliminate (widths (fun _ : Fin (Fintype.card (Later small s.val)) => U))
        (fun p => canonicalContextWeight small B r c L U s η p*
          H (assemble small s.val s.property (prefixExtension small s.val U η) U (suffixEnumeration small s.val) p))
        (childProfile U j.val) := by
    have h := canonical_eliminate_eq_word_fibre small B U hB k τ j
      (fun x => hardMarginal small B r c L x*H x)
    calc
      _ = ∑ a,fibreWeight (fibreWeight
          (fun a => wordWeight small B r c L U a*wordObservable small U H a)
          (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j a := by
        apply Finset.sum_congr rfl
        intro a _
        exact (double_fibreWeight_mul _ _ _ _ _ _ a).symm
      _ = _ := h.symm
  have hμ (j : Fin (U+1)) : mean (cw j) (wordObservable small U H)=canonicalChildMean small B r c L U s η H j.val := by
    unfold mean canonicalChildMean
    rw [hm,hz]
  change variance (fun j => ∑ a,cw j a) (fun j => mean (cw j) (wordObservable small U H)) ≤ _
  simp_rw [hz,hμ]
  exact hcontext s η H


theorem prefixContribution_of_context_bound
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (CT : ℝ) (hCT : 0≤CT)
    (hcontext : CanonicalContextBound r c U L B CT) (hU : 2≤U)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j≤B i j)
    (k : Fin (Fintype.card (Cells (firstPaperSmall r c U))))
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    let small := firstPaperSmall r c U
    prefixContribution (wordWeight small B r c L U) (wordObservable small U H) k ≤
      CT*
        ∑ τ : Earlier small (enumeration small k).val → Fin (U+1),
          ∑ j : Fin U,ownerEnergy small U ⟨enumeration small k,j,τ⟩ (hardMarginal small B r c L) H := by
  dsimp only
  let small := firstPaperSmall r c U
  let E := fun τ : Earlier small (enumeration small k).val → Fin (U+1) =>
    ∑ j : Fin U,ownerEnergy small U ⟨enumeration small k,j,τ⟩ (hardMarginal small B r c L) H
  have hsum : (∑ τ : Fin k.val → Fin (U+1),E (earlierWordChoices small U k τ))=∑ τ,E τ := by
    apply Fintype.sum_equiv (earlierWordChoices small U k)
    intro τ
    rfl
  calc
    _ ≤ ∑ τ : Fin k.val → Fin (U+1),CT*E (earlierWordChoices small U k τ) := by
      unfold prefixContribution partitionContribution
      apply Finset.sum_le_sum
      intro τ _
      exact word_context_variance_of_context_bound r c U L B CT hCT hcontext hU hB hlarge hcap k τ H
    _ = _ := by rw [←Finset.mul_sum,hsum]

theorem balanced_variance_of_context_bound
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (CT : ℝ) (hCT : 0≤CT)
    (hcontext : CanonicalContextBound r c U L B CT) (hU : 2≤U)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j≤B i j)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    let small := firstPaperSmall r c U
    variance (wordWeight small B r c L U) (wordObservable small U H) ≤
      CT*
        ∑ o : Owner small U,ownerEnergy small U o (hardMarginal small B r c L) H := by
  dsimp only
  let small := firstPaperSmall r c U
  have hw (a : Fin (Fintype.card (Cells small)) → Fin (U+1)) :
      0≤wordWeight small B r c L U a := hardMarginal_nonnegative small B r c L _
  rw [variance_eq_sum_prefixContribution (wordWeight small B r c L U) (wordObservable small U H) hw]
  calc
    _ ≤ ∑ k : Fin (Fintype.card (Cells small)),CT*
        ∑ τ : Earlier small (enumeration small k).val → Fin (U+1),
          ∑ j : Fin U,ownerEnergy small U ⟨enumeration small k,j,τ⟩ (hardMarginal small B r c L) H :=
      Finset.sum_le_sum (fun k _ => prefixContribution_of_context_bound r c U L B CT hCT hcontext hU hB hlarge hcap k H)
    _ = CT*
        ∑ s : Cells small,∑ τ : Earlier small s.val → Fin (U+1),
          ∑ j : Fin U,ownerEnergy small U ⟨s,j,τ⟩ (hardMarginal small B r c L) H := by
      rw [←Finset.mul_sum]
      congr 1
      exact (enumeration small).sum_comp
        (fun s => ∑ τ : Earlier small s.val → Fin (U+1),∑ j : Fin U,
          ownerEnergy small U ⟨s,j,τ⟩ (hardMarginal small B r c L) H)
    _ = _ := by
      congr 1
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro s _
      rw [Fintype.sum_prod_type,Finset.sum_comm]

theorem physical_transversal_variance_of_context_bound
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (CT : ℝ) (hCT : 0≤CT)
    (hcontext : CanonicalContextBound r c U L B CT) (hU : 2≤U)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j≤B i j)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    let small := firstPaperSmall r c U
    variance (wordWeight small B r c L U) (wordObservable small U H) ≤
      CT*physicalEnergy small B (hardMarginal small B r c L) H := by
  dsimp only
  exact (balanced_variance_of_context_bound r c U L B CT hCT hcontext hU hB hlarge hcap H).trans
    (mul_le_mul_of_nonneg_left (sum_ownerEnergy_hardMarginal_le _ B r c L U (by omega) hB H) hCT)

theorem physical_full_variance_of_context_bound
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (CT : ℝ) (hCT : 0≤CT)
    (hcontext : CanonicalContextBound r c U L B CT) (hU : 2≤U)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j≤B i j)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    let small := firstPaperSmall r c U
    let w := wordWeight small B r c L U
    let v := fun z : PositiveDefects small B r c L => hardMarginal small B r c L (naturalProfile z.val)
    let G := wordObservable small U H
    let K := fun z : PositiveDefects small B r c L => H (naturalProfile z.val)
    variance (Sum.elim w v) (Sum.elim G K) ≤
      repairCoefficient (Fintype.card (Cells small)) CT*fullEnergy r c U L B hB H := by
  dsimp only
  let small := firstPaperSmall r c U
  let p := Fintype.card (Cells small)
  let E := fullEnergy r c U L B hB H
  have hT : 0≤CT := hCT
  have hvar : variance (wordWeight small B r c L U) (wordObservable small U H) ≤ CT*E := by
    exact (physical_transversal_variance_of_context_bound r c U L B CT hCT hcontext hU hB hlarge hcap H).trans
      (mul_le_mul_of_nonneg_left (physicalEnergy_le_full r c U L B hB H) hT)
  have hrepair := actual_repair_energy_le r c U L B hB hcap H
  have hv := Math115.RepairVarianceRefinement.variance_repaired_energy_sqrt
    (wordWeight small B r c L U)
    (fun z : PositiveDefects small B r c L => hardMarginal small B r c L (naturalProfile z.val))
    (wordObservable small U H) (fun z => H (naturalProfile z.val))
    (repairWord r c U L B hB) (defectLabels small B r c L)
    (fun a => hardMarginal_nonnegative _ _ _ _ _ _) (fun z => le_of_lt z.property.2)
    (repairWord_weight r c U L B hB hcap) (repairWord_type_injective r c U L B hB)
    (CT) E hT (fullEnergy_nonnegative r c U L B hB H) hvar hrepair
  have hcard : (Fintype.card (Cells small×Cells small):ℝ)=(p:ℝ)^2 := by
    simp only [Fintype.card_prod,Nat.cast_mul,p,pow_two]
  rw [hcard] at hv
  exact hv

theorem physical_variance_of_context_bound
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (CT : ℝ) (hCT : 0≤CT)
    (hcontext : CanonicalContextBound r c U L B CT) (hU : 2≤U)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j≤B i j)
    (H : PhysicalStates (firstPaperSmall r c U) B r c L → ℝ) :
    let small := firstPaperSmall r c U
    variance (fun z => hardMarginal small B r c L (physicalProfile small B r c L z)) H ≤
      repairCoefficient (Fintype.card (Cells small)) CT*
        fullEnergy r c U L B hB (physicalExtension small B r c L H) := by
  dsimp only
  let small := firstPaperSmall r c U
  let G := physicalExtension small B r c L H
  have hext : ∀ z : PhysicalStates small B r c L,G (naturalProfile z.val.val)=H z :=
    physicalExtension_at small B r c L H
  have hv := variance_positive_support
    (fun z : Profiles small B => hardMarginal small B r c L (naturalProfile z.val))
    (fun z => G (naturalProfile z.val)) (fun _ => hardMarginal_nonnegative _ _ _ _ _ _)
  have hv' : variance (fun z : PhysicalStates small B r c L =>
      hardMarginal small B r c L (physicalProfile small B r c L z)) H =
      variance (fun z : Profiles small B => hardMarginal small B r c L (naturalProfile z.val)) (fun z => G (naturalProfile z.val)) := by
    simpa only [physicalProfile,hext] using hv
  rw [hv',←encoding_variance_eq small B r c L U hB G]
  exact physical_full_variance_of_context_bound r c U L B CT hCT hcontext hU hB hlarge hcap G

theorem repairCoefficient_bound (p : ℕ) (CT : ℝ) (hp : 2≤p) (hCT : 6≤CT) :
    repairCoefficient p CT ≤ 2*(p:ℝ)^2*CT := by
  exact Math115.RetainedRoot.repair_coefficient_bound p CT hp hCT

theorem state_variance_of_context_bound (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (CT : ℝ) (hCT : 6≤CT) (hU : 2≤U)
    (hp : 2≤Fintype.card (Cells (firstPaperSmall r c U)))
    (hcontext : CanonicalContextBound r c U L (Math115.ReducedSmallChain.capacity r c U L) CT)
    (H : Math115.ReducedSmallChain.States r c U L → ℝ) :
    variance (Math115.ReducedSmallChain.weight r c U L) H ≤
      (2*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^2*CT)*
        Math115.ReducedSmallChain.graphEnergy r c U L H := by
  let small := firstPaperSmall r c U
  let B := Math115.ReducedSmallChain.capacity r c U L
  have h0 : 0≤CT := by linarith
  have hB := Math115.ReducedSmallChain.capacity_small r c U L
  have hlarge : ∀ i j,small i j=false → 2≤B i j := by
    intro i j hij
    change firstPaperSmall r c U i j=false at hij
    simp only [B,Math115.ReducedSmallChain.capacity,paperCapacity,hij,Bool.false_eq_true,↓reduceIte]
    omega
  have hcap := paper_residual_capacity r c (dimensionAllowance (I:=I) (J:=J)) L U dimension_le_allowance
  have hv := physical_variance_of_context_bound r c U L B CT h0 hcontext hU hB hlarge hcap H
  exact hv.trans (mul_le_mul_of_nonneg_right
    (repairCoefficient_bound _ CT hp hCT)
    (fullEnergy_nonnegative r c U L B hB (physicalExtension small B r c L H)))

/-- A direct dependency interface: supply a PROVED actual kernel cap and a
scalar allowance. Context, ownership, repair and physical variance are derived. -/
theorem state_variance_of_uniform_correction_cap
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (hU : 2≤U)
    (hp : 2≤Fintype.card (Cells (firstPaperSmall r c U)))
    (K : ℝ) (hK : 0≤K)
    (hcorrection : UniformCorrectionCap r c U L (Math115.ReducedSmallChain.capacity r c U L) K)
    (CT : ℝ) (hCT : 6≤CT) (hallowance : (U:ℝ)*((U:ℝ)-1)+2*K≤CT)
    (H : Math115.ReducedSmallChain.States r c U L → ℝ) :
    variance (Math115.ReducedSmallChain.weight r c U L) H ≤
      (2*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^2*CT)*
        Math115.ReducedSmallChain.graphEnergy r c U L H := by
  let small := firstPaperSmall r c U
  let B := Math115.ReducedSmallChain.capacity r c U L
  have hB := Math115.ReducedSmallChain.capacity_small r c U L
  have hlarge : ∀ i j,small i j=false → 2≤B i j := by
    intro i j hij
    change firstPaperSmall r c U i j=false at hij
    simp only [B,Math115.ReducedSmallChain.capacity,paperCapacity,hij,Bool.false_eq_true,↓reduceIte]
    omega
  have hcap := paper_residual_capacity r c (dimensionAllowance (I:=I) (J:=J)) L U dimension_le_allowance
  have hcontext := canonical_bound_of_correction_cap r c U L B hU hB hlarge hcap K hK hcorrection
  have huniform := canonical_bound_mono r c U L B ((U:ℝ)*((U:ℝ)-1)+2*K) CT hcontext hallowance
  exact state_variance_of_context_bound r c U L CT hCT hU hp huniform H

end
end Research.UniformContextVariance
