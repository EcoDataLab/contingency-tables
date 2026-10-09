/-
SPDX-License-Identifier: Apache-2.0
The actual free-scale dyadic proposal, completion draw, and translation test.
Oracle accuracy is an input hypothesis; no efficient oracle is constructed.
-/
import Math115.PhysicalRationalKernel
import OAI.Combinatorics.ContingencyTables.Transport.CompletionKernelIdentification
import OAI.Combinatorics.ContingencyTables.Transport.CompletionFibreEquiv

namespace Math115.PhysicalCompletionOracle

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open CompletionTranslation ResidualMixture FirstSuccess
open ReducedSmallChain ReducedAllSmallChain PhysicalRationalKernel
open PhysicalStationarySuccess SmallGraphProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal
open scoped BigOperators Classical

noncomputable section

lemma mapLaw_constant {A X : Type*} [Fintype A] [Fintype X] [DecidableEq X]
    (p : RationalLaw A) (x : X) : mapLaw p (fun _ => x) = pointLaw x := by
  apply RationalLaw.ext
  funext y
  by_cases h : x = y
  · subst y
    simp [mapLaw, pointLaw, p.total]
  · simp [mapLaw, pointLaw, h, Ne.symm h]

/-- A hold has constant output. Only non-hold proposals see the oracle error. -/
theorem completionStep_variation_thinned
    {X A B : Type*} [Fintype X] [Fintype A] [Fintype B] [DecidableEq X]
    (Rows : X → Option A → ℕ) (Cols : X → Option B → ℕ)
    (proposal : X → RationalLaw (Option X))
    (μ ν : (x : X) → RationalLaw (Table (Rows x) (Cols x))) (x : X) :
    variation (completionStepLaw Rows Cols proposal μ x) (completionStepLaw Rows Cols proposal ν x) ≤
      (∑ y, (proposal x).mass (some y)) * variation (μ x) (ν x) := by
  have h := variation_bind_two (proposal x) (proposal x)
    (fun q => mapLaw (μ x) (completionDecision Rows Cols x q))
    (fun q => mapLaw (ν x) (completionDecision Rows Cols x q))
  simp only [variation_self, zero_add] at h
  have hz : variation (mapLaw (μ x) (completionDecision Rows Cols x none))
      (mapLaw (ν x) (completionDecision Rows Cols x none)) = 0 := by
    change variation (mapLaw (μ x) (fun _ => x)) (mapLaw (ν x) (fun _ => x)) = 0
    rw [mapLaw_constant, mapLaw_constant, variation_self]
  calc
    _ ≤ ∑ q, (proposal x).mass q *
        variation (mapLaw (μ x) (completionDecision Rows Cols x q))
          (mapLaw (ν x) (completionDecision Rows Cols x q)) := h
    _ = ∑ y, (proposal x).mass (some y) *
        variation (mapLaw (μ x) (completionDecision Rows Cols x (some y)))
          (mapLaw (ν x) (completionDecision Rows Cols x (some y))) := by
      rw [Fintype.sum_option, hz, mul_zero, zero_add]
    _ ≤ ∑ y, (proposal x).mass (some y) * variation (μ x) (ν x) :=
      Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left
        (variation_map (μ x) (ν x) (completionDecision Rows Cols x (some y)))
        ((proposal x).nonnegative _))
    _ = _ := (Finset.sum_mul _ _ _).symm

lemma equivLaw_uniform {A B : Type*} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (e : A ≃ B) : equivLaw e (uniformLaw (α := A)) = uniformLaw (α := B) := by
  apply RationalLaw.ext
  funext b
  change 1 / (Fintype.card A : ℚ) = 1 / (Fintype.card B : ℚ)
  rw [Fintype.card_congr e]

lemma proposalRat_nonnegative (d : ℕ) : 0 ≤ proposalRat d := by
  unfold proposalRat
  positivity

def proposalAllowance (d : ℕ) : ℚ := (5 * d^2 + 1 : ℕ) * proposalRat d

lemma proposalAllowance_nonnegative (d : ℕ) : 0 ≤ proposalAllowance d := by
  unfold proposalAllowance
  exact mul_nonneg (Nat.cast_nonneg _) (proposalRat_nonnegative d)

lemma proposalAllowance_le_half (d : ℕ) (hd : 1 ≤ d) : proposalAllowance d ≤ 1 / 2 := by
  have h : (proposalAllowance d : ℝ) ≤ 1 / 2 := by
    simpa only [proposalAllowance, Rat.cast_mul, Rat.cast_natCast, proposalRat_cast] using
      smallProposal_degree d hd
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

def degree (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x : States r c U L) : ℕ :=
  (Finset.univ.filter (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x)).card

lemma degree_le (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x : States r c U L) :
    degree r c U L x ≤ 5 * (dimensionAllowance (I := I) (J := J))^2 + 1 :=
  physicalAdjacent_degree_allowance r c U L (capacity r c U L) (capacity_small r c U L) x

lemma proposalWeight_nonnegative (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x y : States r c U L) :
    0 ≤ unitMoveRat r c U L x y := by
  unfold unitMoveRat
  split_ifs
  · exact proposalRat_nonnegative _
  · exact le_refl _

lemma proposalWeight_total (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x : States r c U L) :
    (∑ y, unitMoveRat r c U L x y) =
      (degree r c U L x : ℚ) * proposalRat (dimensionAllowance (I := I) (J := J)) := by
  unfold unitMoveRat degree
  rw [← Finset.sum_filter]
  simp

lemma proposalWeight_total_le_allowance (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x : States r c U L) :
    (∑ y, unitMoveRat r c U L x y) ≤ proposalAllowance (dimensionAllowance (I := I) (J := J)) := by
  rw [proposalWeight_total]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast degree_le r c U L x)
    (proposalRat_nonnegative _)

lemma proposalWeight_total_le_one (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x : States r c U L) :
    (∑ y, unitMoveRat r c U L x y) ≤ 1 :=
  (proposalWeight_total_le_allowance r c U L x).trans
    ((proposalAllowance_le_half _ (by unfold dimensionAllowance; omega)).trans (by norm_num))

def physicalProposalLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x : States r c U L) :
    RationalLaw (Option (States r c U L)) :=
  proposalLaw (unitMoveRat r c U L x) (proposalWeight_nonnegative r c U L x)
    (proposalWeight_total_le_one r c U L x)

abbrev ReferenceTable (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L) :=
  Table (referenceRows r c U L (capacity r c U L) i₀ z)
    (referenceColumns r c U L (capacity r c U L) j₀ z)

instance referenceTableNonempty (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L) :
    Nonempty (ReferenceTable r c U L i₀ j₀ z) :=
  table_nonempty _ _ (reference_totals r c U L (capacity r c U L) i₀ j₀ z
    (physical_paper_capacity _ r c _ L U dimension_le_allowance z))

def referenceStepLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (draw : (z : States r c U L) → RationalLaw (ReferenceTable r c U L i₀ j₀ z))
    (x : States r c U L) : RationalLaw (States r c U L) :=
  completionStepLaw (referenceRows r c U L (capacity r c U L) i₀)
    (referenceColumns r c U L (capacity r c U L) j₀) (physicalProposalLaw r c U L) draw x

/-- The literal exact proposal/draw/test experiment has the previously proved
actual rational transition law, including all holding and rejection mass. -/
theorem referenceExactStep_eq (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (x : States r c U L) :
    referenceStepLaw r c U L i₀ j₀ (fun z => uniformLaw (α := ReferenceTable r c U L i₀ j₀ z)) x =
      referenceTransitionLaw r c U L i₀ j₀ x := by
  unfold referenceStepLaw
  rw [completionStepLaw_proposal_at _ _ (physicalProposalLaw r c U L)
    (fun _ => physicalProposalLaw r c U L x) _ x rfl]
  apply uniformCompletionStep_eq _ _ (unitMoveRat r c U L x)
    (proposalWeight_nonnegative r c U L x) (proposalWeight_total_le_one r c U L x)
  intro y hy
  change referenceTransitionRat r c U L i₀ j₀ x y = _
  simp only [referenceTransitionRat, Ne.symm hy, ite_false, add_zero]
  unfold referenceMoveRat unitMoveRat
  split_ifs <;> simp

theorem referenceStep_variation_local (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (μ ν : (z : States r c U L) → RationalLaw (ReferenceTable r c U L i₀ j₀ z))
    (x : States r c U L) :
    variation (referenceStepLaw r c U L i₀ j₀ μ x) (referenceStepLaw r c U L i₀ j₀ ν x) ≤
      ((degree r c U L x : ℚ) * proposalRat (dimensionAllowance (I := I) (J := J))) *
        variation (μ x) (ν x) := by
  have h := completionStep_variation_thinned
    (referenceRows r c U L (capacity r c U L) i₀)
    (referenceColumns r c U L (capacity r c U L) j₀) (physicalProposalLaw r c U L) μ ν x
  change variation (referenceStepLaw r c U L i₀ j₀ μ x) (referenceStepLaw r c U L i₀ j₀ ν x) ≤
    (∑ y, unitMoveRat r c U L x y) * variation (μ x) (ν x) at h
  rw [proposalWeight_total] at h
  exact h

theorem referenceStep_variation_uniform (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (draw : (z : States r c U L) → RationalLaw (ReferenceTable r c U L i₀ j₀ z))
    (ζ : ℚ) (hζ : 0 ≤ ζ)
    (hdraw : ∀ z, variation (draw z) (uniformLaw (α := ReferenceTable r c U L i₀ j₀ z)) ≤ ζ)
    (x : States r c U L) :
    variation (referenceStepLaw r c U L i₀ j₀ draw x) (referenceTransitionLaw r c U L i₀ j₀ x) ≤
      proposalAllowance (dimensionAllowance (I := I) (J := J)) * ζ := by
  rw [← referenceExactStep_eq r c U L i₀ j₀ x]
  have h := referenceStep_variation_local r c U L i₀ j₀ draw
    (fun z => uniformLaw (α := ReferenceTable r c U L i₀ j₀ z)) x
  have hdegree := proposalWeight_total_le_allowance r c U L x
  rw [proposalWeight_total] at hdegree
  exact h.trans (mul_le_mul hdegree (hdraw x) (variation_nonnegative _ _)
    (proposalAllowance_nonnegative _))

def referenceFibreMap (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L) :
    ReferenceTable r c U L i₀ j₀ z ≃ Fibre r c U L z :=
  (referenceFibreEquiv r c U L (capacity r c U L) i₀ j₀ z
    (physical_paper_capacity _ r c _ L U dimension_le_allowance z)).symm

def referenceCompletionLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (draw : (z : States r c U L) → RationalLaw (ReferenceTable r c U L i₀ j₀ z))
    (z : States r c U L) : RationalLaw (Fibre r c U L z) :=
  equivLaw (referenceFibreMap r c U L i₀ j₀ z) (draw z)

theorem referenceCompletionLaw_variation (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (draw : (z : States r c U L) → RationalLaw (ReferenceTable r c U L i₀ j₀ z))
    (z : States r c U L) :
    variation (referenceCompletionLaw r c U L i₀ j₀ draw z) (uniformLaw (α := Fibre r c U L z)) =
      variation (draw z) (uniformLaw (α := ReferenceTable r c U L i₀ j₀ z)) := by
  rw [← equivLaw_uniform (referenceFibreMap r c U L i₀ j₀ z)]
  exact variation_equiv _ _ _

abbrev OracleFamily (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :=
  (i₀ : LargeRows r U) → (j₀ : LargeColumns c U) →
    (z : States r c U L) → RationalLaw (ReferenceTable r c U L i₀ j₀ z)

def selectedStepLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (oracle : OracleFamily r c U L) :
    States r c U L → RationalLaw (States r c U L) :=
  if h : Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U) then
    referenceStepLaw r c U L (Classical.choice h.1) (Classical.choice h.2)
      (oracle (Classical.choice h.1) (Classical.choice h.2))
  else unitTransitionLaw r c U L

def selectedCompletionLaw (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (oracle : OracleFamily r c U L) : (z : States r c U L) → RationalLaw (Fibre r c U L z) :=
  if h : Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U) then
    referenceCompletionLaw r c U L (Classical.choice h.1) (Classical.choice h.2)
      (oracle (Classical.choice h.1) (Classical.choice h.2))
  else fun z => uniformLaw (α := Fibre r c U L z)

theorem selectedStepLaw_variation (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (States r c U L)] (oracle : OracleFamily r c U L) (ζ : ℚ) (hζ : 0 ≤ ζ)
    (haccuracy : ∀ i₀ j₀ z, variation (oracle i₀ j₀ z)
      (uniformLaw (α := ReferenceTable r c U L i₀ j₀ z)) ≤ ζ) (x : States r c U L) :
    variation (selectedStepLaw r c U L oracle x) (selectedTransitionLaw r c U L x) ≤
      proposalAllowance (dimensionAllowance (I := I) (J := J)) * ζ := by
  unfold selectedStepLaw selectedTransitionLaw
  split_ifs with h
  · exact referenceStep_variation_uniform r c U L _ _ _ ζ hζ (haccuracy _ _) x
  · simp only [variation_self]
    exact mul_nonneg (proposalAllowance_nonnegative _) hζ

theorem selectedCompletionLaw_variation (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (oracle : OracleFamily r c U L) (ζ : ℚ) (hζ : 0 ≤ ζ)
    (haccuracy : ∀ i₀ j₀ z, variation (oracle i₀ j₀ z)
      (uniformLaw (α := ReferenceTable r c U L i₀ j₀ z)) ≤ ζ) (x : States r c U L) :
    variation (selectedCompletionLaw r c U L oracle x) (uniformLaw (α := Fibre r c U L x)) ≤ ζ := by
  unfold selectedCompletionLaw
  split_ifs with h
  · rw [referenceCompletionLaw_variation]
    exact haccuracy _ _ x
  · simpa only [variation_self] using hζ

/-- The unit branch's actual completion fibre has exactly one member. -/
theorem empty_fibre_card_one (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U)) (z : States r c U L) :
    Fintype.card (Fibre r c U L z) = 1 := by
  have h : (Fintype.card (Fibre r c U L z) : ℝ) = 1 :=
    (PhysicalStationaryLaw.fibre_card_weight r c U L z).trans (weight_eq_one r c U L hempty z)
  exact_mod_cast h

end
end Math115.PhysicalCompletionOracle
