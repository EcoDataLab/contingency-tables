import Research.RetainedRepairSquare
import Research.ReciprocalZeroPhysical

namespace Math115.RetainedChainSquare
open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts SmallContextCoordinates SmallContextFibres
open SmallGraphProfiles FiniteExposureVariance CompletionTranslation RowMajorEnumeration
open Math115.PhysicalFullVariance Math115.ReducedSmallChain Math115.ReducedAllSmallChain
open Math115.RetainedRepairSquare Research.ConstantPaddingAcceptance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

/-- The actual original reference chain has the proved half-acceptance energy
comparison at padding seven; paperCapacity discharges its cap premise. -/
theorem chain_energy_lower_seven (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (hL : 7 ≤ L) (H : States r c U L → ℝ) :
    smallProposal (dimensionAllowance (I := I) (J := J)) /
        (2*(∑ z, weight r c U L z))*graphEnergy r c U L H ≤
      (chain r c U L i₀ j₀).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  let B := capacity r c U L
  let R := referenceRows r c U L B i₀
  let P := referenceColumns r c U L B j₀
  have hcap := physical_paper_capacity (firstPaperSmall r c U) r c d L U dimension_le_allowance
  have hw (z : States r c U L) : weight r c U L z = (blockCount R P z : ℝ) :=
    physical_weight_reference_block r c U L B i₀ j₀ z (hcap z)
  have hh := completionChain_energy_lower R P
    (fun z => reference_totals r c U L B i₀ j₀ z (hcap z))
    (physicalAdjacent r c U L B (capacity_small r c U L))
    (physicalAdjacent_symmetric r c U L B (capacity_small r c U L))
    (smallProposal d) ((smallProposal_bounds d (by dsimp [d, dimensionAllowance]; omega)).1.le)
    (5*d^2+1)
    (physicalAdjacent_degree_allowance r c U L B (capacity_small r c U L))
    (smallProposal_degree d (by dsimp [d, dimensionAllowance]; omega))
    (reference_edge_acceptance_seven r c U L B (capacity_small r c U L) i₀ j₀ hL hcap) H
  have hE := fullEnergy_physical_eq r c U L B (capacity_small r c U L) H
  change graphEnergy r c U L H = (∑ x, ∑ y,
    if physicalAdjacent r c U L B (capacity_small r c U L) x y then
      min (weight r c U L x) (weight r c U L y)*(H x-H y)^2 else 0)/2 at hE
  rw [hE]
  simp_rw [hw]
  exact hh

/-- Concrete normalized Poincare coefficient for the actual reference chain.
The local variance, repair, capacity, acceptance, and normalization inputs are
proved dependencies; none is assumed as an abstract comparison premise. -/
theorem chain_poincare_square (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (hU : 2 ≤ U) (hL : 7 ≤ L)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (H : States r c U L → ℝ) :
    (chain r c U L i₀ j₀).variance H ≤
      (4*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^3*(U:ℝ)^2 /
        smallProposal (dimensionAllowance (I := I) (J := J)))*
      (chain r c U L i₀ j₀).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  have h := chain_poincare_of_weighted_graph (chain r c U L i₀ j₀) (weight r c U L) H
    (weight_positive r c U L) (chain_pi r c U L i₀ j₀) (graphEnergy r c U L H)
    (2*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^3*(U:ℝ)^2) (smallProposal d)
    (by positivity) (smallProposal_bounds d (by dsimp [d, dimensionAllowance]; omega)).1
    (state_variance_square r c U L hU hp H)
    (chain_energy_lower_seven r c U L i₀ j₀ hL H)
  convert h using 1
  dsimp only [d]
  ring

/-- The actual empty-completion unit branch has its exact factor-one proposal
comparison, with no padding or acceptance hypothesis. -/
theorem unitChain_poincare_square (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)]
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U))
    (hU : 2 ≤ U) (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (H : States r c U L → ℝ) :
    (unitChain r c U L).variance H ≤
      (2*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^3*(U:ℝ)^2 /
        smallProposal (dimensionAllowance (I := I) (J := J)))*
      (unitChain r c U L).energy H := by
  let d := dimensionAllowance (I := I) (J := J)
  let K := 2*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^3*(U:ℝ)^2
  have hβ := (smallProposal_bounds d (by dsimp [d, dimensionAllowance]; omega)).1
  have hZ : 0 < ∑ z : States r c U L, weight r c U L z :=
    Finset.sum_pos (fun z _ => weight_positive r c U L z) Finset.univ_nonempty
  have hv : variance (weight r c U L) H ≤ K*graphEnergy r c U L H :=
    state_variance_square r c U L hU hp H
  rw [chain_variance_eq (unitChain r c U L) (weight r c U L) H
    (unitChain_pi_weight r c U L hempty)]
  calc
    _ ≤ (K*graphEnergy r c U L H)/(∑ z, weight r c U L z) :=
      div_le_div_of_nonneg_right hv hZ.le
    _ = (K/smallProposal d)*(unitChain r c U L).energy H := by
      rw [unitChain_energy r c U L hempty H]
      field_simp [ne_of_gt hβ, ne_of_gt hZ]
      ring

/-- The existing original branch selector includes reference and no-reference
chains at padding seven, on the same actual positive physical state space. -/
theorem selectedChain_poincare_square (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (hU : 2 ≤ U) (hL : 7 ≤ L)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (H : States r c U L → ℝ) :
    (selectedChain r c U L).variance H ≤
      (4*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^3*(U:ℝ)^2 /
        smallProposal (dimensionAllowance (I := I) (J := J)))*
      (selectedChain r c U L).energy H := by
  unfold selectedChain
  split_ifs with h
  · exact chain_poincare_square r c U L (Classical.choice h.1) (Classical.choice h.2) hU hL hp H
  · have hu := unitChain_poincare_square r c U L (missing_reference_empty r c U h) hU hp H
    have hβ := (smallProposal_bounds (dimensionAllowance (I := I) (J := J))
      (by unfold dimensionAllowance; omega)).1
    have hC : 0 ≤ 2*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^3*(U:ℝ)^2 /
        smallProposal (dimensionAllowance (I := I) (J := J)) := by positivity
    apply hu.trans
    apply mul_le_mul_of_nonneg_right _ ((unitChain r c U L).energy_nonneg H)
    have heq : 4*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^3*(U:ℝ)^2 /
        smallProposal (dimensionAllowance (I := I) (J := J)) =
        2*(2*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^3*(U:ℝ)^2 /
        smallProposal (dimensionAllowance (I := I) (J := J))) := by ring
    rw [heq]
    linarith

/-- The unchanged original dyadic proposal costs at most 64d². -/
theorem reference_square_budget (p d U : ℕ) (hd : 1 ≤ d) (hp : p ≤ d) :
    4*(p:ℝ)^3*(U:ℝ)^2/smallProposal d ≤ 256*(d:ℝ)^5*(U:ℝ)^2 := by
  have hproposal := smallProposal_bounds d hd
  have hrecip : 1/smallProposal d ≤ 64*(d:ℝ)^2 := by
    apply (div_le_iff₀ hproposal.1).mpr
    have h := (div_le_iff₀ (by positivity : (0:ℝ)<64*(d:ℝ)^2)).mp hproposal.2.1
    nlinarith only [h]
  have hpR : (p:ℝ) ≤ d := by exact_mod_cast hp
  calc
    _ = (4*(p:ℝ)^3*(U:ℝ)^2)*(1/smallProposal d) := by ring
    _ ≤ (4*(p:ℝ)^3*(U:ℝ)^2)*(64*(d:ℝ)^2) :=
      mul_le_mul_of_nonneg_left hrecip (by positivity)
    _ ≤ (4*(d:ℝ)^3*(U:ℝ)^2)*(64*(d:ℝ)^2) := by gcongr
    _ = _ := by ring

theorem selectedChain_poincare_polynomial_square (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (hU : 2 ≤ U) (hL : 7 ≤ L)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (H : States r c U L → ℝ) :
    (selectedChain r c U L).variance H ≤
      (256*(dimensionAllowance (I:=I) (J:=J):ℝ)^5*(U:ℝ)^2)*
      (selectedChain r c U L).energy H := by
  have hpd : Fintype.card (Cells (firstPaperSmall r c U)) ≤ dimensionAllowance (I:=I) (J:=J) :=
    (small_card_le_dimension (firstPaperSmall r c U)).trans dimension_le_allowance
  exact (selectedChain_poincare_square r c U L hU hL hp H).trans
    (mul_le_mul_of_nonneg_right
      (reference_square_budget _ _ U (by unfold dimensionAllowance; omega) hpd)
      ((selectedChain r c U L).energy_nonneg H))

/-- The accepted constant-padding cutoff keeps the full shape dependence. -/
noncomputable def squareCutoff : ℕ :=
  11*dimensionAllowance (I:=I) (J:=J)*(Fintype.card I+Fintype.card J-2)

omit [LinearOrder I] [LinearOrder J] in
lemma squareCutoff_at_least_two (hI : 2 ≤ Fintype.card I) (hJ : 2 ≤ Fintype.card J) :
    2 ≤ squareCutoff (I:=I) (J:=J) := by
  have hd : 1 ≤ dimensionAllowance (I:=I) (J:=J) := by unfold dimensionAllowance; omega
  have hs : 2 ≤ Fintype.card I+Fintype.card J-2 := by omega
  unfold squareCutoff
  nlinarith

/-- Compiled original selected chain at U=11d(m+n−2), L=7. This is the
actual dyadic chain's shape bound, not the separately reviewed defect trace. -/
theorem selectedChain_poincare_shape_square (r : I → ℕ) (c : J → ℕ)
    (hI : 2 ≤ Fintype.card I) (hJ : 2 ≤ Fintype.card J)
    [Nonempty (States r c (squareCutoff (I:=I) (J:=J)) 7)]
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c (squareCutoff (I:=I) (J:=J)))))
    (H : States r c (squareCutoff (I:=I) (J:=J)) 7 → ℝ) :
    (selectedChain r c (squareCutoff (I:=I) (J:=J)) 7).variance H ≤
      (30976*(dimensionAllowance (I:=I) (J:=J):ℝ)^7*
        ((Fintype.card I+Fintype.card J-2:ℕ):ℝ)^2)*
      (selectedChain r c (squareCutoff (I:=I) (J:=J)) 7).energy H := by
  have hv := selectedChain_poincare_polynomial_square r c (squareCutoff (I:=I) (J:=J)) 7
    (squareCutoff_at_least_two hI hJ) (by omega) hp H
  convert hv using 1
  unfold squareCutoff
  push_cast
  ring

omit [LinearOrder I] [LinearOrder J] in
lemma shapeWidth_three (hI : 2 ≤ Fintype.card I) (hJ : 2 ≤ Fintype.card J) :
    3*(Fintype.card I+Fintype.card J-2)+13 ≤ dimensionAllowance (I:=I) (J:=J) := by
  unfold dimensionAllowance
  -- Work in integers so the product expansion has no truncated subtraction.
  have hprod : (0:ℤ) ≤ ((Fintype.card I:ℤ)-2)*((Fintype.card J:ℤ)-2) := by
    apply mul_nonneg <;> omega
  zify
  have hs : ((Fintype.card I+Fintype.card J-2:ℕ):ℤ) =
      (Fintype.card I:ℤ)+(Fintype.card J:ℤ)-2 := by omega
  rw [hs]
  nlinarith only [hprod]

/-- Conservative all-shape d⁹ envelope for the actual original dyadic chain.
The stronger preceding theorem retains its d⁷(m+n−2)² shape dependence. -/
theorem selectedChain_poincare_d9 (r : I → ℕ) (c : J → ℕ)
    (hI : 2 ≤ Fintype.card I) (hJ : 2 ≤ Fintype.card J)
    [Nonempty (States r c (squareCutoff (I:=I) (J:=J)) 7)]
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c (squareCutoff (I:=I) (J:=J)))))
    (H : States r c (squareCutoff (I:=I) (J:=J)) 7 → ℝ) :
    (selectedChain r c (squareCutoff (I:=I) (J:=J)) 7).variance H ≤
      (3442*(dimensionAllowance (I:=I) (J:=J):ℝ)^9)*
      (selectedChain r c (squareCutoff (I:=I) (J:=J)) 7).energy H := by
  let d := dimensionAllowance (I:=I) (J:=J)
  let s := Fintype.card I+Fintype.card J-2
  have hshapeN : 3*s ≤ d := by have := shapeWidth_three hI hJ; omega
  have hshape : 3*(s:ℝ) ≤ d := by exact_mod_cast hshapeN
  have hsquare : (s:ℝ)^2 ≤ (d:ℝ)^2/9 := by nlinarith [sq_nonneg ((d:ℝ)-3*s)]
  have hscalar : 30976*(d:ℝ)^7*(s:ℝ)^2 ≤ 3442*(d:ℝ)^9 := by
    have hm := mul_le_mul_of_nonneg_left hsquare (by positivity : 0≤30976*(d:ℝ)^7)
    have hdn : 0 ≤ (d:ℝ)^9 := by positivity
    nlinarith only [hm, hdn]
  exact (selectedChain_poincare_shape_square r c hI hJ hp H).trans
    (mul_le_mul_of_nonneg_right hscalar
      ((selectedChain r c (squareCutoff (I:=I) (J:=J)) 7).energy_nonneg H))

end
end Math115.RetainedChainSquare

#print axioms Math115.RetainedChainSquare.chain_poincare_square
#print axioms Math115.RetainedChainSquare.unitChain_poincare_square
#print axioms Math115.RetainedChainSquare.selectedChain_poincare_square

#print axioms Math115.RetainedChainSquare.selectedChain_poincare_shape_square
#print axioms Math115.RetainedChainSquare.selectedChain_poincare_d9
