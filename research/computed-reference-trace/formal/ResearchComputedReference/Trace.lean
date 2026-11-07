/-
SPDX-License-Identifier: Apache-2.0
The physical defect trace at an explicit fixed reference pair, specialized to
the computed large-line pair. The existing aggregate bound is retained. This
does not identify kernels at different pairs or implement a new outer sampler.
-/
import Research.AggregateDefectTrace
import OAI.Combinatorics.ContingencyTables.Rooted.LargeMarginReference

set_option maxHeartbeats 800000

namespace Math115.ComputedReferenceTrace

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts SmallContextCoordinates SmallContextFibres
open SmallGraphProfiles FiniteExposureVariance CompletionTranslation
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.AggregateDefectTrace Research.ConstantPaddingAcceptance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

lemma reference_nonnegative (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (x y : States r c U L) :
    0 ≤ referenceConductance r c U L i₀ j₀ x y := by
  unfold referenceConductance
  split_ifs <;> positivity

lemma reference_off_edge (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (x y : States r c U L)
    (hxy : ¬physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y) :
    referenceConductance r c U L i₀ j₀ x y = 0 := by
  simp only [referenceConductance, ite_eq_right hxy]

lemma reference_diagonal (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (x : States r c U L) :
    referenceConductance r c U L i₀ j₀ x x = 0 :=
  reference_off_edge r c U L i₀ j₀ x x (physicalAdjacent_irreflexive r c U L x)

/-- The actual capacity and the padding-seven acceptance theorem discharge
the conductance comparison for every fixed reference pair. -/
lemma reference_half_minimum (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (hL : 7 ≤ L)
    (x y : States r c U L) :
    minimumConductance r c U L x y / 2 ≤ referenceConductance r c U L i₀ j₀ x y := by
  by_cases hxy : physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y
  · simp only [minimumConductance, referenceConductance, ite_eq_left hxy]
    have hw := reference_weight r c U L i₀ j₀ x
    have ha := reference_edge_acceptance_seven r c U L _ (capacity_small r c U L)
      i₀ j₀ hL (physical_paper_capacity _ r c _ L U dimension_le_allowance) x y hxy
    calc
      _ ≤ weight r c U L x / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
      _ = _ := by rw [hw]
      _ ≤ _ := ha
  · simp only [minimumConductance, referenceConductance, ite_eq_right hxy]
    norm_num

lemma reference_row_degree (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (x : States r c U L) :
    (∑ y, referenceConductance r c U L i₀ j₀ x y) ≤
      ((Finset.univ.filter (physicalAdjacent r c U L (capacity r c U L)
        (capacity_small r c U L) x)).card : ℝ) * weight r c U L x := by
  calc
    _ ≤ ∑ y, if physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y
        then weight r c U L x else 0 :=
      Finset.sum_le_sum (fun y _ => referenceConductance_upper r c U L i₀ j₀ x y)
    _ = _ := by rw [← Finset.sum_filter]; simp

def referenceDD (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (d e : DefectVertices r c U L) : ℝ :=
  referenceConductance r c U L i₀ j₀ d.val e.val

def referenceCross (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (b : BalancedVertices r c U L) (d : DefectVertices r c U L) : ℝ :=
  referenceConductance r c U L i₀ j₀ b.val d.val

def referenceSplit (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (x y : BalancedVertices r c U L ⊕ DefectVertices r c U L) : ℝ :=
  referenceConductance r c U L i₀ j₀ (partitionEquiv r c U L x) (partitionEquiv r c U L y)

lemma fullConductance_reference (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) :
    Research.WeightedHarmonicTrace.fullConductance (referenceDD r c U L i₀ j₀)
      (referenceCross r c U L i₀ j₀) = referenceSplit r c U L i₀ j₀ := by
  exact Research.WeightedHarmonicTrace.fullConductance_of_blocks (referenceSplit r c U L i₀ j₀)
    (fun x y => referenceConductance_symmetric r c U L i₀ j₀ _ _)
    (fun b b' => reference_off_edge r c U L i₀ j₀ b.val b'.val
      (physicalAdjacent_no_balanced_balanced r c U L b.val b'.val b.property b'.property))

lemma reference_split_half (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (hL : 7 ≤ L) :
    ∀ x y, splitMinimum r c U L x y / 2 ≤
      Research.WeightedHarmonicTrace.fullConductance
        (referenceDD r c U L i₀ j₀) (referenceCross r c U L i₀ j₀) x y := by
  rw [fullConductance_reference]
  intro x y
  exact reference_half_minimum r c U L i₀ j₀ hL _ _

lemma reference_cross_dd_row (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (d : DefectVertices r c U L) :
    (∑ e, referenceDD r c U L i₀ j₀ d e) + (∑ b, referenceCross r c U L i₀ j₀ b d) =
      ∑ y, referenceConductance r c U L i₀ j₀ d.val y := by
  have he := (partitionEquiv r c U L).sum_comp (fun y => referenceConductance r c U L i₀ j₀ d.val y)
  rw [Fintype.sum_sum_type] at he
  have hb : (∑ b, referenceCross r c U L i₀ j₀ b d) = ∑ b : BalancedVertices r c U L,
      referenceConductance r c U L i₀ j₀ d.val b.val := by
    apply Finset.sum_congr rfl
    intro b _
    exact referenceConductance_symmetric r c U L i₀ j₀ b.val d.val
  rw [hb]
  exact (add_comm _ _).trans he

/-- The actual 4p-3 degree bound, with no degree premise on the constructor. -/
lemma reference_defect_row (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) :
    ∀ d, (∑ e, referenceDD r c U L i₀ j₀ d e) + (∑ b, referenceCross r c U L i₀ j₀ b d) ≤
      (defectAllowance r c U : ℝ) * defectWeight r c U L d := by
  intro d
  rw [reference_cross_dd_row]
  exact (reference_row_degree r c U L i₀ j₀ d.val).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast actual_defect_degree r c U L d)
      (weight_positive r c U L d.val).le)

/-- An explicit-reference family, with exact rational clock 1/[2(4p-3)]. -/
def referenceTrace (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    [Nonempty (DefectVertices r c U L)]
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U))) : FiniteChain (DefectVertices r c U L) :=
  Research.WeightedHarmonicTrace.rationalChain (defectWeight r c U L)
    (referenceDD r c U L i₀ j₀) (referenceCross r c U L i₀ j₀)
    (fun d => weight_positive r c U L d.val)
    (fun d e => reference_nonnegative r c U L i₀ j₀ d.val e.val)
    (fun d e => referenceConductance_symmetric r c U L i₀ j₀ d.val e.val)
    (fun b d => reference_nonnegative r c U L i₀ j₀ b.val d.val)
    (defectAllowance r c U) (defectAllowance_positive r c U hp)
    (reference_defect_row r c U L i₀ j₀)

lemma referenceTrace_pi (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    [Nonempty (DefectVertices r c U L)]
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U))) (d : DefectVertices r c U L) :
    (referenceTrace r c U L i₀ j₀ hp).π d =
      defectWeight r c U L d / (∑ e, defectWeight r c U L e) := rfl

lemma referenceTrace_lazy (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    [Nonempty (DefectVertices r c U L)]
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U))) (d : DefectVertices r c U L) :
    1 / 2 ≤ (referenceTrace r c U L i₀ j₀ hp).P d d :=
  (referenceTrace r c U L i₀ j₀ hp).lazy d

lemma referenceTrace_move (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    [Nonempty (DefectVertices r c U L)]
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d e : DefectVertices r c U L) (hne : d ≠ e) :
    (referenceTrace r c U L i₀ j₀ hp).P d e =
      (1 / (2 * (defectAllowance r c U : ℝ))) *
        Research.WeightedHarmonicTrace.traceConductance
          (referenceDD r c U L i₀ j₀) (referenceCross r c U L i₀ j₀) d e / defectWeight r c U L d := by
  simp only [referenceTrace, Research.WeightedHarmonicTrace.rationalChain,
    Research.WeightedHarmonicTrace.traceChain, FiniteChain.ofMoves,
    Research.WeightedHarmonicTrace.traceMove, ite_eq_right hne, add_zero]

/-- The literal transition retains conductance-weighted balanced exits. In a
zero-mass star its summand is zero, exactly as in the existing trace. -/
theorem referenceTrace_transition (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    [Nonempty (DefectVertices r c U L)]
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d e : DefectVertices r c U L) (hne : d ≠ e) :
    (referenceTrace r c U L i₀ j₀ hp).P d e =
      (referenceDD r c U L i₀ j₀ d e +
        ∑ b, referenceCross r c U L i₀ j₀ b d * referenceCross r c U L i₀ j₀ b e /
          (∑ f, referenceCross r c U L i₀ j₀ b f)) /
        (2 * (defectAllowance r c U : ℝ) * defectWeight r c U L d) := by
  rw [referenceTrace_move r c U L i₀ j₀ hp d e hne]
  unfold Research.WeightedHarmonicTrace.traceConductance Research.WeightedHarmonicTrace.starMass
  simp only [div_eq_mul_inv, mul_inv_rev, one_mul]
  ring

/-- Recover the canonical chain only at its own chosen reference pair.
There is no equality assertion between distinct reference choices. -/
theorem referenceTrace_canonical_P (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (href : Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U))
    [Nonempty (DefectVertices r c U L)]
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U))) (d e : DefectVertices r c U L) :
    (referenceTrace r c U L (Classical.choice href.1) (Classical.choice href.2) hp).P d e =
      (actualRationalTrace r c U L hp).P d e := by
  have hDD : referenceDD r c U L (Classical.choice href.1) (Classical.choice href.2) =
      ddConductance r c U L := by
    funext a b
    simp only [referenceDD, ddConductance, acceptedConductance, dite_eq_left href]
  have hCross : referenceCross r c U L (Classical.choice href.1) (Classical.choice href.2) =
      crossConductance r c U L := by
    funext b a
    simp only [referenceCross, crossConductance, acceptedConductance, dite_eq_left href]
  unfold referenceTrace actualRationalTrace rationalPhysicalTrace
  simp only [hDD, hCross]

lemma referenceTrace_canonical_pi (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (href : Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U))
    [Nonempty (DefectVertices r c U L)]
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U))) (d : DefectVertices r c U L) :
    (referenceTrace r c U L (Classical.choice href.1) (Classical.choice href.2) hp).π d =
      (actualRationalTrace r c U L hp).π d := rfl

/-- The actual full-state variance, capacity, acceptance and row bound supply
the aggregate coefficient for every fixed pair. None is a theorem premise. -/
theorem referenceTrace_poincare_aggregate (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    [Nonempty (DefectVertices r c U L)] (hU : 2 ≤ U) (hL : 7 ≤ L)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U))) (g : DefectVertices r c U L → ℝ) :
    (referenceTrace r c U L i₀ j₀ hp).variance g ≤
      (32 * (Fintype.card (Cells (firstPaperSmall r c U)) : ℝ)^3 * aggregateCT r c U) *
        (referenceTrace r c U L i₀ j₀ hp).energy g := by
  let p := Fintype.card (Cells (firstPaperSmall r c U))
  have hC : 0 ≤ 2 * (p : ℝ)^2 * aggregateCT r c U :=
    mul_nonneg (by positivity) (by have := aggregateCT_at_least_six r c U hU hp; linarith)
  have hv : (referenceTrace r c U L i₀ j₀ hp).variance g ≤
      (4 * (defectAllowance r c U : ℝ) * (2 * (p : ℝ)^2 * aggregateCT r c U)) *
        (referenceTrace r c U L i₀ j₀ hp).energy g := by
    apply Research.WeightedHarmonicTrace.rational_poincare_transfer
      (balancedWeight r c U L) (defectWeight r c U L)
      (fun b => (weight_positive r c U L b.val).le) (fun d => weight_positive r c U L d.val)
      (referenceDD r c U L i₀ j₀) (referenceCross r c U L i₀ j₀)
      (fun d e => reference_nonnegative r c U L i₀ j₀ d.val e.val)
      (fun d e => referenceConductance_symmetric r c U L i₀ j₀ d.val e.val)
      (fun b d => reference_nonnegative r c U L i₀ j₀ b.val d.val)
      (defectAllowance r c U) (defectAllowance_positive r c U hp)
      (reference_defect_row r c U L i₀ j₀) (splitMinimum r c U L) _ hC
    · intro F
      rw [split_variance_identity, split_energy_identity]
      exact state_variance_aggregate r c U L hU hp _
    · exact reference_split_half r c U L i₀ j₀ hL
  have hQ : (defectAllowance r c U : ℝ) ≤ 4 * (p : ℝ) := by
    have hh : defectAllowance r c U ≤ 4 * p := Nat.sub_le _ _
    exact_mod_cast hh
  have hc : 4 * (defectAllowance r c U : ℝ) * (2 * (p : ℝ)^2 * aggregateCT r c U) ≤
      32 * (p : ℝ)^3 * aggregateCT r c U := by
    calc
      _ ≤ 4 * (4 * (p : ℝ)) * (2 * (p : ℝ)^2 * aggregateCT r c U) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hQ (by norm_num : (0 : ℝ) ≤ 4)) hC
      _ = _ := by ring
  exact hv.trans (mul_le_mul_of_nonneg_right hc (FiniteChain.energy_nonneg _ g))

section Computed
variable {m n : ℕ}

/-- The margins and cutoff fix the actual first computed large row/column;
the reference pair does not change with the walk state. -/
def computedReferenceTrace (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (hr : 0 < (ProfilePrograms.largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (ProfilePrograms.largeIndices (U, List.ofFn c)).length)
    [Nonempty (DefectVertices r c U L)]
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U))) : FiniteChain (DefectVertices r c U L) :=
  referenceTrace r c U L (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none) hp

theorem computedReferenceTrace_poincare_aggregate (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (hr : 0 < (ProfilePrograms.largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (ProfilePrograms.largeIndices (U, List.ofFn c)).length)
    [Nonempty (DefectVertices r c U L)] (hU : 2 ≤ U) (hL : 7 ≤ L)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U))) (g : DefectVertices r c U L → ℝ) :
    (computedReferenceTrace r c U L hr hc hp).variance g ≤
      (32 * (Fintype.card (Cells (firstPaperSmall r c U)) : ℝ)^3 * aggregateCT r c U) *
        (computedReferenceTrace r c U L hr hc hp).energy g :=
  referenceTrace_poincare_aggregate r c U L
    (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none) hU hL hp g

theorem computedReferenceTrace_transition (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (hr : 0 < (ProfilePrograms.largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (ProfilePrograms.largeIndices (U, List.ofFn c)).length)
    [Nonempty (DefectVertices r c U L)]
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d e : DefectVertices r c U L) (hne : d ≠ e) :
    let i₀ := largeOptionEquiv r U hr none
    let j₀ := largeOptionEquiv c U hc none
    (computedReferenceTrace r c U L hr hc hp).P d e =
      (referenceDD r c U L i₀ j₀ d e +
        ∑ b, referenceCross r c U L i₀ j₀ b d * referenceCross r c U L i₀ j₀ b e /
          (∑ f, referenceCross r c U L i₀ j₀ b f)) /
        (2 * (defectAllowance r c U : ℝ) * defectWeight r c U L d) :=
  referenceTrace_transition r c U L
    (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none) hp d e hne

lemma computedReferenceTrace_pi (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (hr : 0 < (ProfilePrograms.largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (ProfilePrograms.largeIndices (U, List.ofFn c)).length)
    [Nonempty (DefectVertices r c U L)]
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U))) (d : DefectVertices r c U L) :
    (computedReferenceTrace r c U L hr hc hp).π d =
      defectWeight r c U L d / (∑ e, defectWeight r c U L e) := rfl

end Computed
end
end Math115.ComputedReferenceTrace
