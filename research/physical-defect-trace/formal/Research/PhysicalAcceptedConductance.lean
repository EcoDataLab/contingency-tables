import Research.PhysicalTraceMargins

namespace Math115.PhysicalDefectTrace

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts SmallContextCoordinates SmallContextFibres
open SmallGraphProfiles FiniteExposureVariance CompletionTranslation RowMajorEnumeration
open IntegerWeightedTransport FactorialSignatures
open Math115.ReducedSmallChain Math115.ReducedAllSmallChain
open Research.ConstantPaddingAcceptance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

def referenceConductance (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (x y : States r c U L) : ℝ :=
  if physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y then
    (acceptedCount (referenceRows r c U L (capacity r c U L) i₀)
      (referenceColumns r c U L (capacity r c U L) j₀) x y:ℝ) else 0

lemma reference_weight (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (x : States r c U L) :
    weight r c U L x=(blockCount (referenceRows r c U L (capacity r c U L) i₀)
      (referenceColumns r c U L (capacity r c U L) j₀) x:ℝ) :=
  physical_weight_reference_block r c U L _ i₀ j₀ x
    (physical_paper_capacity _ r c _ L U dimension_le_allowance x)

lemma reference_totals_actual (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (x : States r c U L) :
    (∑ i,referenceRows r c U L (capacity r c U L) i₀ x i)=
      ∑ j,referenceColumns r c U L (capacity r c U L) j₀ x j :=
  reference_totals r c U L _ i₀ j₀ x
    (physical_paper_capacity _ r c _ L U dimension_le_allowance x)

lemma referenceConductance_symmetric (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (x y : States r c U L) :
    referenceConductance r c U L i₀ j₀ x y=referenceConductance r c U L i₀ j₀ y x := by
  unfold referenceConductance
  rw [physicalAdjacent_symmetric r c U L _ (capacity_small r c U L) x y]
  split_ifs
  · exact_mod_cast acceptedCount_symmetric _ _ (reference_totals_actual r c U L i₀ j₀) x y
  · rfl

lemma referenceConductance_upper (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (x y : States r c U L) :
    referenceConductance r c U L i₀ j₀ x y ≤
      if physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y then weight r c U L x else 0 := by
  unfold referenceConductance
  split_ifs
  · rw [reference_weight r c U L i₀ j₀ x]
    exact_mod_cast acceptedCount_le _ _ x y
  · exact le_rfl

/-- Completion-translation accepted conductance, with the exact source unit
acceptance branch when no reference block exists. No proposal beta is built in. -/
def acceptedConductance (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x y : States r c U L) : ℝ :=
  if h : Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U) then
    referenceConductance r c U L (Classical.choice h.1) (Classical.choice h.2) x y
  else if physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y then 1 else 0

lemma acceptedConductance_nonnegative (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x y : States r c U L) :
    0 ≤ acceptedConductance r c U L x y := by
  unfold acceptedConductance referenceConductance
  split_ifs <;> positivity

lemma acceptedConductance_symmetric (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x y : States r c U L) :
    acceptedConductance r c U L x y=acceptedConductance r c U L y x := by
  by_cases h : Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U)
  · simp only [acceptedConductance,dite_eq_left h]
    exact referenceConductance_symmetric r c U L _ _ x y
  · simp only [acceptedConductance,dite_eq_right h]
    rw [physicalAdjacent_symmetric r c U L _ (capacity_small r c U L) x y]

lemma acceptedConductance_off_edge (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x y : States r c U L)
    (hxy : ¬physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y) :
    acceptedConductance r c U L x y=0 := by
  unfold acceptedConductance referenceConductance
  split_ifs <;> simp_all

lemma acceptedConductance_supported_upper (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (x y : States r c U L) : acceptedConductance r c U L x y ≤
      if physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y then weight r c U L x else 0 := by
  by_cases h : Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U)
  · simp only [acceptedConductance,dite_eq_left h]
    exact referenceConductance_upper r c U L _ _ x y
  · simp only [acceptedConductance,dite_eq_right h]
    rw [weight_eq_one r c U L (missing_reference_empty r c U h) x]

/-- Literal minimum-endpoint source graph conductance, zero off its edges. -/
def minimumConductance (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x y : States r c U L) : ℝ :=
  if physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y then
    min (weight r c U L x) (weight r c U L y) else 0

lemma half_minimum_accepted (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (hL : 7≤L)
    (x y : States r c U L) : minimumConductance r c U L x y/2 ≤ acceptedConductance r c U L x y := by
  by_cases href : Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U)
  · simp only [acceptedConductance,dite_eq_left href]
    by_cases hxy : physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y
    · simp only [minimumConductance,referenceConductance,ite_eq_left hxy]
      have hw := reference_weight r c U L (Classical.choice href.1) (Classical.choice href.2) x
      have ha := reference_edge_acceptance_seven r c U L _ (capacity_small r c U L)
        (Classical.choice href.1) (Classical.choice href.2) hL
        (physical_paper_capacity _ r c _ L U dimension_le_allowance) x y hxy
      calc
        _ ≤ weight r c U L x/2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        _ = _ := by rw [hw]
        _ ≤ _ := ha
    · simp only [minimumConductance,referenceConductance,ite_eq_right hxy]
      norm_num
  · simp only [acceptedConductance,dite_eq_right href]
    by_cases hxy : physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y
    · simp only [minimumConductance,ite_eq_left hxy]
      rw [weight_eq_one r c U L (missing_reference_empty r c U href) x,
        weight_eq_one r c U L (missing_reference_empty r c U href) y]
      norm_num
    · simp only [minimumConductance,ite_eq_right hxy]
      norm_num

lemma acceptedConductance_row_degree (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (x : States r c U L) : (∑ y,acceptedConductance r c U L x y) ≤
      ((Finset.univ.filter (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x)).card:ℝ)*weight r c U L x := by
  calc
    _ ≤ ∑ y,if physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y then weight r c U L x else 0 :=
      Finset.sum_le_sum (fun y _ => acceptedConductance_supported_upper r c U L x y)
    _ = _ := by rw [←Finset.sum_filter]; simp

set_option maxHeartbeats 800000 in
lemma graphEnergy_minimum_matrix (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (H : States r c U L → ℝ) : graphEnergy r c U L H=
      (∑ x,∑ y,minimumConductance r c U L x y*(H x-H y)^2)/2 := by
  have he := fullEnergy_physical_eq r c U L _ (capacity_small r c U L) H
  change graphEnergy r c U L H=(∑ x,∑ y,
    if physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y then
      min (weight r c U L x) (weight r c U L y)*(H x-H y)^2 else 0)/2 at he
  rw [he]
  apply congrArg (fun t : ℝ => t/2)
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y
  · simp only [minimumConductance,ite_eq_left hxy]
  · simp only [minimumConductance,ite_eq_right hxy,zero_mul]

end
end Math115.PhysicalDefectTrace

#print axioms Math115.PhysicalDefectTrace.half_minimum_accepted
