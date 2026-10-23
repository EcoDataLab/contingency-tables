/-
SPDX-License-Identifier: Apache-2.0
Ideal incoming acceptance followed by an ideal conductance-weighted exit.
The star-total case split describes a noncomputable comparison law. It is
not an executable test for computing star totals or an adaptive word bank.
-/
import ResearchRationalClockStep.Step
import ResearchPhysicalStarRetry.Exit
import ResearchComputedReference.Trace

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open SmallContextCoordinates FirstSuccess ResidualMixture
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.ComputedReferenceTrace Math115.RationalClockStep
open Math115.PhysicalStarTrial Math115.PhysicalStarRetry
open scoped BigOperators Classical

noncomputable section

/-- Off-diagonal masses and normalization determine a whole real-valued row. -/
lemma law_cast_eq_of_offdiag {D : Type*} [Fintype D]
    (p : RationalLaw D) (P : D → ℝ) (hP : ∑ e, P e = 1) (d : D)
    (hoff : ∀ e, e ≠ d → (p.mass e : ℝ) = P e) :
    ∀ e, (p.mass e : ℝ) = P e := by
  intro e
  by_cases he : e = d
  · subst e
    have hs : (∑ e, ((p.mass e : ℝ) - P e)) = (p.mass d : ℝ) - P d := by
      apply Finset.sum_eq_single d
      · intro e _ hed
        rw [hoff e hed, sub_self]
      · simp
    rw [Finset.sum_sub_distrib, ← Rat.cast_sum, p.total, Rat.cast_one, hP] at hs
    linarith
  · exact hoff e he

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

local notation "i₀" => largeOptionEquiv r U hr none
local notation "j₀" => largeOptionEquiv c U hc none

/-- Ideal comparison kernel only: preserve defects, use a normalized positive
balanced star, and return to the supplied source defect for a zero star. -/
def idealExitKernel (d : DefectVertices r c U L) (x : States r c U L) :
    RationalLaw (DefectVertices r c U L) :=
  if hb : IsBalanced r c U L x then
    if hs : 0 < starMass r c U L hr hc ⟨x, hb⟩ then
      targetLaw r c U L hr hc ⟨x, hb⟩ hs
    else pointLaw d
  else pointLaw ⟨x, hb⟩

lemma idealExitKernel_defect (d e : DefectVertices r c U L) :
    idealExitKernel r c U L hr hc d e.val = pointLaw e := by
  simp only [idealExitKernel, dite_eq_right e.property]

lemma idealExitKernel_balanced (d : DefectVertices r c U L)
    (b : BalancedVertices r c U L) :
    idealExitKernel r c U L hr hc d b.val =
      if hs : 0 < starMass r c U L hr hc b then targetLaw r c U L hr hc b hs
      else pointLaw d := by
  simp only [idealExitKernel, dite_eq_left b.property]

/-- Zero star totals force every incident count and conductance to vanish. -/
lemma zero_star_cross (b : BalancedVertices r c U L)
    (hzero : starMass r c U L hr hc b = 0) (e : DefectVertices r c U L) :
    referenceCross r c U L i₀ j₀ b e = 0 := by
  have hle : crossRat r c U L hr hc b e ≤ starMass r c U L hr hc b :=
    Finset.single_le_sum (fun f _ => crossRat_nonnegative r c U L hr hc b f)
      (Finset.mem_univ e)
  have hz : crossRat r c U L hr hc b e = 0 :=
    le_antisymm (by simpa only [hzero] using hle) (crossRat_nonnegative r c U L hr hc b e)
  rw [← crossRat_cast r c U L hr hc b e, hz, Rat.cast_zero]

def idealJoinedLaw
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d : DefectVertices r c U L) : RationalLaw (DefectVertices r c U L) :=
  bindLaw (idealIncomingLaw r c U L hr hc hp d) (idealExitKernel r c U L hr hc d)

/-- The full-state bind decomposes into a direct defect arrival and balanced
arrivals followed by their local exit laws. -/
lemma idealJoinedLaw_mass_split
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d e : DefectVertices r c U L) :
    (idealJoinedLaw r c U L hr hc hp d).mass e =
      (idealIncomingLaw r c U L hr hc hp d).mass e.val +
      ∑ b : BalancedVertices r c U L,
        (idealIncomingLaw r c U L hr hc hp d).mass b.val *
          (idealExitKernel r c U L hr hc d b.val).mass e := by
  change (∑ x : States r c U L, (idealIncomingLaw r c U L hr hc hp d).mass x *
    (idealExitKernel r c U L hr hc d x).mass e) = _
  rw [← (partitionEquiv r c U L).sum_comp
    (fun x => (idealIncomingLaw r c U L hr hc hp d).mass x *
      (idealExitKernel r c U L hr hc d x).mass e), Fintype.sum_sum_type]
  change
    (∑ b : BalancedVertices r c U L, (idealIncomingLaw r c U L hr hc hp d).mass b.val *
      (idealExitKernel r c U L hr hc d b.val).mass e) +
    (∑ f : DefectVertices r c U L, (idealIncomingLaw r c U L hr hc hp d).mass f.val *
      (idealExitKernel r c U L hr hc d f.val).mass e) = _
  have hd : (∑ f : DefectVertices r c U L,
      (idealIncomingLaw r c U L hr hc hp d).mass f.val *
        (idealExitKernel r c U L hr hc d f.val).mass e) =
      (idealIncomingLaw r c U L hr hc hp d).mass e.val := by
    rw [Finset.sum_eq_single e]
    · simp [idealExitKernel_defect, pointLaw]
    · intro f _ hfe
      simp [idealExitKernel_defect, pointLaw, Ne.symm hfe]
    · simp
  rw [hd]
  exact add_comm _ _

/-- This identity also covers zero stars without a padding lower bound. -/
lemma balanced_arrival_exit_mass_cast (htotal : (∑ i, r i) = ∑ j, c j)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d e : DefectVertices r c U L) (hne : d ≠ e) (b : BalancedVertices r c U L) :
    ((idealIncomingLaw r c U L hr hc hp d).mass b.val : ℝ) *
        ((idealExitKernel r c U L hr hc d b.val).mass e : ℝ) =
      (referenceCross r c U L i₀ j₀ b d * referenceCross r c U L i₀ j₀ b e /
        (∑ f, referenceCross r c U L i₀ j₀ b f)) /
      (2 * (defectAllowance r c U : ℝ) * defectWeight r c U L d) := by
  have hdb : d.val ≠ b.val := by
    intro he
    exact d.property (he.symm ▸ b.property)
  have hi : ((idealIncomingLaw r c U L hr hc hp d).mass b.val : ℝ) =
      referenceCross r c U L i₀ j₀ b d /
        (2 * (defectAllowance r c U : ℝ) * defectWeight r c U L d) := by
    rw [idealIncomingLaw_mass_ne_cast r c U L hr hc htotal hp d b.val hdb,
      referenceConductance_symmetric r c U L i₀ j₀ d.val b.val]
    rfl
  rw [hi, idealExitKernel_balanced]
  split_ifs with hs
  · rw [targetLaw_mass_cast]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · have hz : starMass r c U L hr hc b = 0 :=
      le_antisymm (le_of_not_gt hs) (starMass_nonnegative r c U L hr hc b)
    have hzR : (∑ f, referenceCross r c U L i₀ j₀ b f) = 0 := by
      rw [← starMass_cast r c U L hr hc b, hz, Rat.cast_zero]
    simp only [pointLaw, ite_eq_right (Ne.symm hne), Rat.cast_zero, mul_zero, hzR, div_zero,
      zero_div]

theorem idealJoinedLaw_mass_ne (htotal : (∑ i, r i) = ∑ j, c j)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d e : DefectVertices r c U L) (hne : d ≠ e) :
    letI : Nonempty (DefectVertices r c U L) := ⟨d⟩
    ((idealJoinedLaw r c U L hr hc hp d).mass e : ℝ) =
      (computedReferenceTrace r c U L hr hc hp).P d e := by
  letI : Nonempty (DefectVertices r c U L) := ⟨d⟩
  have hde : d.val ≠ e.val := fun he => hne (Subtype.ext he)
  rw [computedReferenceTrace_transition r c U L hr hc hp d e hne,
    idealJoinedLaw_mass_split]
  simp only [Rat.cast_add, Rat.cast_sum, Rat.cast_mul]
  rw [idealIncomingLaw_mass_ne_cast r c U L hr hc htotal hp d e.val hde]
  simp_rw [balanced_arrival_exit_mass_cast r c U L hr hc htotal hp d e hne]
  change referenceDD r c U L i₀ j₀ d e /
      (2 * (defectAllowance r c U : ℝ) * defectWeight r c U L d) +
      (∑ b : BalancedVertices r c U L,
        (referenceCross r c U L i₀ j₀ b d * referenceCross r c U L i₀ j₀ b e /
          (∑ f, referenceCross r c U L i₀ j₀ b f)) /
        (2 * (defectAllowance r c U : ℝ) * defectWeight r c U L d)) = _
  rw [← Finset.sum_div, ← add_div]

/-- Normalization identifies the diagonal as well as all off-diagonal
entries. The supplied source defect provides nonempty trace support. -/
theorem idealJoinedLaw_row (htotal : (∑ i, r i) = ∑ j, c j)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d : DefectVertices r c U L) :
    letI : Nonempty (DefectVertices r c U L) := ⟨d⟩
    ∀ e : DefectVertices r c U L,
      ((idealJoinedLaw r c U L hr hc hp d).mass e : ℝ) =
        (computedReferenceTrace r c U L hr hc hp).P d e := by
  letI : Nonempty (DefectVertices r c U L) := ⟨d⟩
  exact law_cast_eq_of_offdiag (idealJoinedLaw r c U L hr hc hp d)
    ((computedReferenceTrace r c U L hr hc hp).P d)
    ((computedReferenceTrace r c U L hr hc hp).stochastic d) d
    (fun e he => idealJoinedLaw_mass_ne r c U L hr hc htotal hp d e (Ne.symm he))

end
end Math115.PhysicalTraceJoin
