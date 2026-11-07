import Research.RetainedContextVariance
import Math115.PhysicalRepairRefinement

namespace Math115.RetainedTransversalVariance
open OAI.ContingencyTables
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open BalancedEnumeration IntegerWeightedTransport FirstPaperProfiles
open ExcessContextProfiles SmallGraphProfiles FirstPaperPhysicalMarginal
open FirstPaperContextTransport PaddedCompletions CompletionCounts RowMajorEnumeration
open FiniteExposureVariance Math115.PhysicalLeafEnergy Math115.PhysicalExposureVariance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

lemma sum_Icc_eq_fin_succ (E : ℕ → ℝ) (U : ℕ) :
    (∑ l ∈ Finset.Icc 1 U,E l) = ∑ j : Fin U,E (j.val+1) := by
  apply Finset.sum_bij (fun l hl => (⟨l-1,by have := Finset.mem_Icc.mp hl; omega⟩ : Fin U))
  · intro l hl; exact Finset.mem_univ _
  · intro a ha b hb heq
    have hh := congrArg Fin.val heq
    have := Finset.mem_Icc.mp ha
    have := Finset.mem_Icc.mp hb
    dsimp only at hh
    omega
  · intro j _
    refine ⟨j.val+1,Finset.mem_Icc.mpr ⟨by omega,by omega⟩,?_⟩
    apply Fin.ext
    simp
  · intro l hl
    have hh := Finset.mem_Icc.mp hl
    dsimp only
    rw [show l-1+1=l by omega]

/-- Canonical contexts inherit the physical spectral theorem. Only cardinal
comparison of the literal suffix is used to obtain the common pU² constant. -/
theorem canonical_context_variance_le_ownerEnergies
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (hU : 2≤U)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j≤B i j)
    (s : Cells (firstPaperSmall r c U))
    (τ : Earlier (firstPaperSmall r c U) s.val → Fin (U+1))
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    let small := firstPaperSmall r c U
    variance (fun j : Fin (U+1) => canonicalChildMass small B r c L U s τ j.val)
      (fun j => canonicalChildMean small B r c L U s τ H j.val) ≤
      ((Fintype.card (Cells small):ℝ)*(U:ℝ)^2)*
        ∑ j : Fin U,ownerEnergy small U ⟨s,j,τ⟩ (hardMarginal small B r c L) H := by
  dsimp only
  let small := firstPaperSmall r c U
  let n := Fintype.card (Later small s.val)
  let σ := prefixExtension small s.val U τ
  let e := suffixEnumeration small s.val
  have hc := RetainedContextVariance.firstPaper_context_variance_spectral_bound r c U L B hU s.val s.property σ
    hB hlarge (prefixExtension_bounded small s.val U τ) e hcap H
  rw [sum_Icc_eq_fin_succ] at hc
  have hnN : n+1≤Fintype.card (Cells small) := by
    have hn := later_card_le small s
    have hp : 0<Fintype.card (Cells small) := Fintype.card_pos_iff.mpr ⟨s⟩
    dsimp only [n]
    omega
  have hnR : ((n+1:ℕ):ℝ)≤(Fintype.card (Cells small):ℝ) := by exact_mod_cast hnN
  have he (j : Fin U) : physicalLeafEnergy small s.val s.property σ U (j.val+1) e
      (hardMarginal small B r c L) H = ownerEnergy small U ⟨s,j,τ⟩ (hardMarginal small B r c L) H := rfl
  have hsum : 0≤∑ j : Fin U,ownerEnergy small U ⟨s,j,τ⟩ (hardMarginal small B r c L) H :=
    Finset.sum_nonneg (fun j _ => ownerEnergy_nonnegative small U _ _ _ (hardMarginal_nonnegative small B r c L))
  change variance (fun j : Fin (U+1) => canonicalChildMass small B r c L U s τ j.val)
    (fun j => canonicalChildMean small B r c L U s τ H j.val) ≤
    (((n+1:ℕ):ℝ)*(U:ℝ)^2)*∑ j : Fin U,physicalLeafEnergy small s.val s.property σ U (j.val+1) e
      (hardMarginal small B r c L) H at hc
  simp_rw [he] at hc
  apply hc.trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hnR (sq_nonneg (U:ℝ))) hsum

/-- The two canonical elimination identities identify literal word fibres and
their means. This reuses the source finite-prefix maps, not a variance premise. -/
theorem word_context_variance_le_ownerEnergies
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (hU : 2≤U)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
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
      ((Fintype.card (Cells small):ℝ)*(U:ℝ)^2)*
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
  exact canonical_context_variance_le_ownerEnergies r c U L B hU hB hlarge hcap s η H

theorem prefixContribution_le_ownerEnergies
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (hU : 2≤U)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j≤B i j)
    (k : Fin (Fintype.card (Cells (firstPaperSmall r c U))))
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    let small := firstPaperSmall r c U
    prefixContribution (wordWeight small B r c L U) (wordObservable small U H) k ≤
      ((Fintype.card (Cells small):ℝ)*(U:ℝ)^2)*
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
    _ ≤ ∑ τ : Fin k.val → Fin (U+1),((Fintype.card (Cells small):ℝ)*(U:ℝ)^2)*E (earlierWordChoices small U k τ) := by
      unfold prefixContribution partitionContribution
      apply Finset.sum_le_sum
      intro τ _
      exact word_context_variance_le_ownerEnergies r c U L B hU hB hlarge hcap k τ H
    _ = _ := by rw [←Finset.mul_sum,hsum]

/-- Exact source exposure telescoping and recovered owners sum the actual
context estimates. No supplied final transversal inequality is used. -/
theorem balanced_variance_le_ownerEnergies
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (hU : 2≤U)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j≤B i j)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    let small := firstPaperSmall r c U
    variance (wordWeight small B r c L U) (wordObservable small U H) ≤
      ((Fintype.card (Cells small):ℝ)*(U:ℝ)^2)*
        ∑ o : Owner small U,ownerEnergy small U o (hardMarginal small B r c L) H := by
  dsimp only
  let small := firstPaperSmall r c U
  have hw (a : Fin (Fintype.card (Cells small)) → Fin (U+1)) :
      0≤wordWeight small B r c L U a := hardMarginal_nonnegative small B r c L _
  rw [variance_eq_sum_prefixContribution (wordWeight small B r c L U) (wordObservable small U H) hw]
  calc
    _ ≤ ∑ k : Fin (Fintype.card (Cells small)),((Fintype.card (Cells small):ℝ)*(U:ℝ)^2)*
        ∑ τ : Earlier small (enumeration small k).val → Fin (U+1),
          ∑ j : Fin U,ownerEnergy small U ⟨enumeration small k,j,τ⟩ (hardMarginal small B r c L) H :=
      Finset.sum_le_sum (fun k _ => prefixContribution_le_ownerEnergies r c U L B hU hB hlarge hcap k H)
    _ = ((Fintype.card (Cells small):ℝ)*(U:ℝ)^2)*
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

/-- Actual balanced physical variance has coefficient pU² in the unchanged
uniform-U source graph. Original leaf ownership charges each edge once. -/
theorem physical_transversal_variance_spectral
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (hU : 2≤U)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j≤B i j)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    let small := firstPaperSmall r c U
    variance (wordWeight small B r c L U) (wordObservable small U H) ≤
      ((Fintype.card (Cells small):ℝ)*(U:ℝ)^2)*physicalEnergy small B (hardMarginal small B r c L) H := by
  dsimp only
  exact (balanced_variance_le_ownerEnergies r c U L B hU hB hlarge hcap H).trans
    (mul_le_mul_of_nonneg_left (sum_ownerEnergy_hardMarginal_le _ B r c L U (by omega) hB H) (by positivity))

/-- Genuine source capacities at arbitrary cutoff/padding discharge all
structural premises of the actual balanced pU² bound. -/
theorem paperCapacity_transversal_variance_spectral
    (r : I → ℕ) (c : J → ℕ) (U L d : ℕ) (hU : 2≤U)
    (hd : Fintype.card I*Fintype.card J≤d)
    (H : SmallProfile (firstPaperSmall r c U) → ℝ) :
    let small := firstPaperSmall r c U
    let B := paperCapacity small r d L U
    variance (wordWeight small B r c L U) (wordObservable small U H) ≤
      ((Fintype.card (Cells small):ℝ)*(U:ℝ)^2)*physicalEnergy small B (hardMarginal small B r c L) H := by
  dsimp only
  apply physical_transversal_variance_spectral r c U L _ hU _ _ _ H
  · intro i j hij
    simp only [paperCapacity,hij,↓reduceIte]
  · intro i j hij
    simp only [paperCapacity,hij,Bool.false_eq_true,↓reduceIte]
    omega
  · exact paper_residual_capacity r c d L U hd

end
end Math115.RetainedTransversalVariance
