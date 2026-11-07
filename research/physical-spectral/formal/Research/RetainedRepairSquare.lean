import Research.RetainedTransversalVariance

namespace Math115.RetainedRepairSquare
open OAI.ContingencyTables
open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts SmallContextCoordinates SmallContextFibres
open SmallContextEnumeration RowMajorEnumeration SmallGraphProfiles FiniteExposureVariance
open Math115.PhysicalExposureVariance Math115.PhysicalLeafEnergy Math115.PhysicalFullVariance
open Math115.PhysicalRepairRefinement Math115.RetainedTransversalVariance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

noncomputable def balancedCoefficient (p U : ℕ) : ℝ := (p:ℝ)*(U:ℝ)^2
noncomputable def fullCoefficient (p U : ℕ) : ℝ :=
  balancedCoefficient p U+(Real.sqrt ((p:ℝ)^2*balancedCoefficient p U)+1)^2

/-- Actual balanced-plus-defect variance through the unchanged source repair
word and label injection. Its transversal bound is derived, never supplied. -/
theorem physical_full_variance_spectral
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (hU : 2≤U)
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
      fullCoefficient (Fintype.card (Cells small)) U*fullEnergy r c U L B hB H := by
  dsimp only
  let small := firstPaperSmall r c U
  let p := Fintype.card (Cells small)
  let E := fullEnergy r c U L B hB H
  have hT : 0≤balancedCoefficient p U := by unfold balancedCoefficient; positivity
  have hvar : variance (wordWeight small B r c L U) (wordObservable small U H) ≤ balancedCoefficient p U*E := by
    exact (physical_transversal_variance_spectral r c U L B hU hB hlarge hcap H).trans
      (mul_le_mul_of_nonneg_left (physicalEnergy_le_full r c U L B hB H) hT)
  have hrepair := actual_repair_energy_le r c U L B hB hcap H
  have hv := RepairVarianceRefinement.variance_repaired_energy_sqrt
    (wordWeight small B r c L U)
    (fun z : PositiveDefects small B r c L => hardMarginal small B r c L (naturalProfile z.val))
    (wordObservable small U H) (fun z => H (naturalProfile z.val))
    (repairWord r c U L B hB) (defectLabels small B r c L)
    (fun a => hardMarginal_nonnegative _ _ _ _ _ _) (fun z => le_of_lt z.property.2)
    (repairWord_weight r c U L B hB hcap) (repairWord_type_injective r c U L B hB)
    (balancedCoefficient p U) E hT (fullEnergy_nonnegative r c U L B hB H) hvar hrepair
  have hcard : (Fintype.card (Cells small×Cells small):ℝ)=(p:ℝ)^2 := by
    simp only [Fintype.card_prod,Nat.cast_mul,p,pow_two]
  rw [hcard] at hv
  exact hv

/-- Exact encoding and positive-support identities give every actual physical
observable the new bound in the original graph energy. -/
theorem physical_variance_spectral
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ) (hU : 2≤U)
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j≤B i j)
    (H : PhysicalStates (firstPaperSmall r c U) B r c L → ℝ) :
    let small := firstPaperSmall r c U
    variance (fun z => hardMarginal small B r c L (physicalProfile small B r c L z)) H ≤
      fullCoefficient (Fintype.card (Cells small)) U*
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
  exact physical_full_variance_spectral r c U L B hU hB hlarge hcap G

theorem fullCoefficient_bound (p U : ℕ) (hp : 2≤p) (hU : 2≤U) :
    fullCoefficient p U≤2*(p:ℝ)^3*(U:ℝ)^2 := by
  have hpR : (2:ℝ)≤p := by exact_mod_cast hp
  have hUR : (2:ℝ)≤U := by exact_mod_cast hU
  have hT : 6≤balancedCoefficient p U := by
    unfold balancedCoefficient
    have hU2 : (4:ℝ)≤(U:ℝ)^2 := by nlinarith only [hUR,sq_nonneg ((U:ℝ)-2)]
    have hm := mul_le_mul hpR hU2 (by norm_num : (0:ℝ)≤4) (by positivity : (0:ℝ)≤p)
    norm_num at hm
    linarith only [hm]
  unfold fullCoefficient
  calc
    _ ≤ 2*(p:ℝ)^2*balancedCoefficient p U := Math115.RetainedRoot.repair_coefficient_bound p _ hp hT
    _ = _ := by unfold balancedCoefficient; ring


/-- The actual physical-state variance satisfies the U² repair envelope. Its
transversal comparison and repair energy are proved in the imported sources. -/
theorem physical_variance_square
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (hU : 2≤U) (hp : 2≤Fintype.card (Cells (firstPaperSmall r c U)))
    (hB : ∀ i j,firstPaperSmall r c U i j=true → B i j=U)
    (hlarge : ∀ i j,firstPaperSmall r c U i j=false → 2≤B i j)
    (hcap : ∀ T : ResidualTables (firstPaperSmall r c U) r c
      (fun i => r i+rowLargeCount (firstPaperSmall r c U) i*L)
      (fun j => c j+columnLargeCount (firstPaperSmall r c U) j*L),∀ i j,T.val.val i j≤B i j)
    (H : PhysicalStates (firstPaperSmall r c U) B r c L → ℝ) :
    let small := firstPaperSmall r c U
    let p := Fintype.card (Cells small)
    variance (fun z => hardMarginal small B r c L (physicalProfile small B r c L z)) H ≤
      (2*(p:ℝ)^3*(U:ℝ)^2)*fullEnergy r c U L B hB (physicalExtension small B r c L H) := by
  dsimp only
  exact (physical_variance_spectral r c U L B hU hB hlarge hcap H).trans
    (mul_le_mul_of_nonneg_right (fullCoefficient_bound _ U hp hU)
      (fullEnergy_nonnegative r c U L B hB (physicalExtension _ B r c L H)))

/-- Genuine paperCapacity supplies all capacity hypotheses at arbitrary U,L.
No residual cap, correction bound, or variance comparison is a premise. -/
theorem paperCapacity_variance_square
    (r : I → ℕ) (c : J → ℕ) (U L d : ℕ) (hU : 2≤U)
    (hd : Fintype.card I*Fintype.card J≤d)
    (hp : 2≤Fintype.card (Cells (firstPaperSmall r c U)))
    (H : PhysicalStates (firstPaperSmall r c U)
      (paperCapacity (firstPaperSmall r c U) r d L U) r c L → ℝ) :
    let small := firstPaperSmall r c U
    let B := paperCapacity small r d L U
    let hB : ∀ i j,small i j=true → B i j=U := fun i j hij => by simp [B,paperCapacity,hij]
    variance (fun z => hardMarginal small B r c L (physicalProfile small B r c L z)) H ≤
      (2*(Fintype.card (Cells small):ℝ)^3*(U:ℝ)^2)*
        fullEnergy r c U L B hB (physicalExtension small B r c L H) := by
  dsimp only
  apply physical_variance_square r c U L _ hU hp
  · intro i j hij
    simp only [paperCapacity,hij,Bool.false_eq_true,↓reduceIte]
    omega
  · exact paper_residual_capacity r c d L U hd

/-- The same source capacity and physical state graph used by the existing
chain definitions now have the concrete 2p³U² unnormalized variance bound. -/
theorem state_variance_square (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hU : 2≤U) (hp : 2≤Fintype.card (Cells (firstPaperSmall r c U)))
    (H : Math115.ReducedSmallChain.States r c U L → ℝ) :
    variance (Math115.ReducedSmallChain.weight r c U L) H ≤
      (2*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^3*(U:ℝ)^2)*
        Math115.ReducedSmallChain.graphEnergy r c U L H := by
  exact paperCapacity_variance_square r c U L
    (dimensionAllowance (I:=I) (J:=J)) hU dimension_le_allowance hp H

end
end Math115.RetainedRepairSquare

#print axioms Math115.RetainedRepairSquare.state_variance_square
#check Math115.RetainedRepairSquare.state_variance_square
