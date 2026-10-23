/-
SPDX-License-Identifier: Apache-2.0
State-dependent incoming/exit kernel laws and their error comparison.
Each balanced exit has its own fixed-width word bank, conditional on the
reached state. No one common input word or adaptive reservation is built.
-/
import ResearchPhysicalTraceJoin.Ideal
import ResearchPhysicalStarBudget.Schedule

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open FirstSuccess ResidualMixture
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.ComputedReferenceTrace Math115.RationalClockStep
open Math115.PhysicalStarTrial Math115.PhysicalStarRetry
open Math115.LegacyPhysicalCompletion Math115.CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section

lemma variation_swap {X : Type*} [Fintype X] (p q : RationalLaw X) :
    variation p q = variation q p := by
  unfold variation
  congr 1
  exact Finset.sum_congr rfl (fun x _ => abs_sub_comm _ _)

/-- Exit error is charged only on positive ideal incoming support. This
avoids imposing a uniform bound on unreachable states. -/
lemma variation_bind_ideal_support
    {X D : Type*} [Fintype X] [Fintype D]
    (p q : RationalLaw X) (K L : X → RationalLaw D) (E : ℚ)
    (hsupport : ∀ x, 0 < q.mass x → variation (K x) (L x) ≤ E) :
    variation (bindLaw p K) (bindLaw q L) ≤ variation p q + E := by
  have hsum : (∑ x, q.mass x * variation (L x) (K x)) ≤ E := by
    calc
      _ ≤ ∑ x, q.mass x * E := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hx : q.mass x = 0
        · simp only [hx, zero_mul, le_refl]
        · have hxpos : 0 < q.mass x :=
            lt_of_le_of_ne (q.nonnegative x) (Ne.symm hx)
          rw [variation_swap (L x) (K x)]
          exact mul_le_mul_of_nonneg_left (hsupport x hxpos) (q.nonnegative x)
      _ = E := by rw [← Finset.sum_mul, q.total, one_mul]
  calc
    _ = variation (bindLaw q L) (bindLaw p K) := variation_swap _ _
    _ ≤ variation q p + ∑ x, q.mass x * variation (L x) (K x) :=
      variation_bind_two q p L K
    _ ≤ variation p q + E := by
      rw [variation_swap q p]
      exact add_le_add (le_refl _) hsum

lemma proposalRate_le_one (dimension : ℕ) :
    Math115.PhysicalRationalKernel.proposalRat dimension ≤ 1 := by
  unfold Math115.PhysicalRationalKernel.proposalRat
  have hp (k : ℕ) : (1 : ℚ) ≤ 2^k := by
    induction k with
    | zero => norm_num
    | succ k ih => rw [pow_succ]; nlinarith
  exact (div_le_one (by positivity)).mpr (hp _)

def exitAllowance (dimension J h : ℕ) : ℚ :=
  (1 - Math115.PhysicalRationalKernel.proposalRat dimension / 2)^J + (J : ℚ) * dyadic h

lemma exitAllowance_nonnegative (dimension J h : ℕ) : 0 ≤ exitAllowance dimension J h := by
  have hr := proposalRate_le_one dimension
  have hbase : 0 ≤ 1 - Math115.PhysicalRationalKernel.proposalRat dimension / 2 := by linarith
  unfold exitAllowance
  exact add_nonneg (pow_nonneg hbase J) (mul_nonneg (Nat.cast_nonneg J) (by unfold dyadic; positivity))

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

local notation "dimension" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => Nat.clog 2 (32 * dimension^2)
local notation "B" => capacity r c U L
local notation "i₀" => largeOptionEquiv r U hr none
local notation "j₀" => largeOptionEquiv c U hc none

/-- Exactly J*(s+q_b(h)) bits at this fixed reached balanced state b. -/
def actualBalancedExitLaw (d : DefectVertices r c U L)
    (b : BalancedVertices r c U L) (J h : ℕ) : RationalLaw (DefectVertices r c U L) :=
  mapLaw (uniformLaw (α := Fin (J * (s + bits r c U L hr hc b.val h)) → Bool))
    (flatExit r c U L hr hc b h d J)

/-- This law never tests or computes symbolic star totals. -/
def actualExitKernel (d : DefectVertices r c U L) (J h : ℕ) (x : States r c U L) :
    RationalLaw (DefectVertices r c U L) :=
  if hb : IsBalanced r c U L x then actualBalancedExitLaw r c U L hr hc d ⟨x, hb⟩ J h
  else pointLaw ⟨x, hb⟩

lemma actualExitKernel_defect (d e : DefectVertices r c U L) (J h : ℕ) :
    actualExitKernel r c U L hr hc d J h e.val = pointLaw e := by
  simp only [actualExitKernel, dite_eq_right e.property]

lemma actualExitKernel_balanced (d : DefectVertices r c U L)
    (b : BalancedVertices r c U L) (J h : ℕ) :
    actualExitKernel r c U L hr hc d J h b.val = actualBalancedExitLaw r c U L hr hc d b J h := by
  simp only [actualExitKernel, dite_eq_left b.property]

/-- A semantic bind of fresh state-dependent exit experiments. No common
fixed-width input realization or adaptive outer reservation is asserted. -/
def actualJoinedLaw (d : DefectVertices r c U L) (N hIn J hExit : ℕ) :
    RationalLaw (DefectVertices r c U L) :=
  bindLaw (incomingLaw r c U L hr hc d N hIn) (actualExitKernel r c U L hr hc d J hExit)

lemma idealIncoming_zero_star (htotal : (∑ i, r i) = ∑ j, c j)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d : DefectVertices r c U L) (b : BalancedVertices r c U L)
    (hzero : starMass r c U L hr hc b = 0) :
    (idealIncomingLaw r c U L hr hc hp d).mass b.val = 0 := by
  have hdb : d.val ≠ b.val := by
    intro he
    exact d.property (he.symm ▸ b.property)
  apply Rat.cast_injective (α := ℝ)
  rw [Rat.cast_zero, idealIncomingLaw_mass_ne_cast r c U L hr hc htotal hp d b.val hdb,
    referenceConductance_symmetric r c U L i₀ j₀ d.val b.val]
  change referenceCross r c U L i₀ j₀ b d /
    (2 * (defectAllowance r c U : ℝ) * defectWeight r c U L d) = 0
  rw [zero_star_cross r c U L hr hc b hzero d, zero_div]

/-- Zero stars still have a local actual fallback approximation; the actual
kernel does not need to recognize this branch. -/
lemma actualExitKernel_zero_star_accuracy (htotal : (∑ i, r i) = ∑ j, c j)
    (d : DefectVertices r c U L) (b : BalancedVertices r c U L) (J h : ℕ)
    (hzero : starMass r c U L hr hc b = 0) :
    variation (actualExitKernel r c U L hr hc d J h b.val)
      (idealExitKernel r c U L hr hc d b.val) ≤ (J : ℚ) * dyadic h := by
  have hn : ¬0 < starMass r c U L hr hc b := by rw [hzero]; exact lt_irrefl 0
  rw [actualExitKernel_balanced, idealExitKernel_balanced, dite_eq_right hn]
  exact flatExit_zero_star_variation r c U L hr hc htotal b h hzero d J

/-- Only positive ideal incoming support needs a uniform exit bound. -/
lemma actualExitKernel_support_accuracy (htotal : (∑ i, r i) = ∑ j, c j)
    (hL : 7 ≤ L) (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d : DefectVertices r c U L) (J h : ℕ) (x : States r c U L)
    (hx : 0 < (idealIncomingLaw r c U L hr hc hp d).mass x) :
    variation (actualExitKernel r c U L hr hc d J h x)
      (idealExitKernel r c U L hr hc d x) ≤ exitAllowance dimension J h := by
  by_cases hb : IsBalanced r c U L x
  · let b : BalancedVertices r c U L := ⟨x, hb⟩
    have hdb : d.val ≠ b.val := by
      intro he
      exact d.property (he.symm ▸ b.property)
    have hadj : physicalAdjacent r c U L B (capacity_small r c U L) d.val b.val := by
      by_contra hn
      have hm := idealIncomingLaw_mass_ne r c U L hr hc htotal hp d b.val hdb
      rw [ite_eq_right hn] at hm
      have hx' : 0 < (idealIncomingLaw r c U L hr hc hp d).mass b.val := hx
      linarith
    have hbd : physicalAdjacent r c U L B (capacity_small r c U L) b.val d.val :=
      (physicalAdjacent_symmetric r c U L B (capacity_small r c U L) d.val b.val).mp hadj
    have hstar := starMass_pos_of_edge r c U L hr hc hL b d hbd
    change variation (actualExitKernel r c U L hr hc d J h b.val)
      (idealExitKernel r c U L hr hc d b.val) ≤ _
    rw [actualExitKernel_balanced, idealExitKernel_balanced, dite_eq_left hstar]
    exact flatExit_variation_of_edge r c U L hr hc htotal hL b h d hbd J
  · let e : DefectVertices r c U L := ⟨x, hb⟩
    change variation (actualExitKernel r c U L hr hc d J h e.val)
      (idealExitKernel r c U L hr hc d e.val) ≤ _
    rw [actualExitKernel_defect, idealExitKernel_defect, variation_self]
    exact exitAllowance_nonnegative dimension J h

/-- Actual incoming/exit laws approximate the exactly identified ideal trace
row. The comparison charges exit error on ideal incoming support only. -/
theorem actualJoinedLaw_accuracy (htotal : (∑ i, r i) = ∑ j, c j)
    (hL : 7 ≤ L) (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d : DefectVertices r c U L) (N hIn J hExit : ℕ) :
    variation (actualJoinedLaw r c U L hr hc d N hIn J hExit)
      (idealJoinedLaw r c U L hr hc hp d) ≤
      (1 / 2 : ℚ)^N + dyadic hIn + exitAllowance dimension J hExit := by
  unfold actualJoinedLaw idealJoinedLaw
  have he := variation_bind_ideal_support
    (incomingLaw r c U L hr hc d N hIn) (idealIncomingLaw r c U L hr hc hp d)
    (actualExitKernel r c U L hr hc d J hExit) (idealExitKernel r c U L hr hc d)
    (exitAllowance dimension J hExit)
    (actualExitKernel_support_accuracy r c U L hr hc htotal hL hp d J hExit)
  exact he.trans (add_le_add (incomingLaw_accuracy r c U L hr hc hp d N hIn) (le_refl _))

/-- A concrete one-step law budget. Incoming precision and clock attempts
are t+2; the reached balanced state uses the checked local exit schedule.
The underlying state-dependent banks are still separate experiments. -/
theorem scheduledJoinedLaw_accuracy (htotal : (∑ i, r i) = ∑ j, c j)
    (hL : 7 ≤ L) (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d : DefectVertices r c U L) (t : ℕ) :
    variation
      (actualJoinedLaw r c U L hr hc d (t + 2) (t + 2)
        (Math115.PhysicalStarBudget.attempts dimension t)
        (Math115.PhysicalStarBudget.precision dimension t))
      (idealJoinedLaw r c U L hr hc hp d) ≤ dyadic t := by
  have he := actualJoinedLaw_accuracy r c U L hr hc htotal hL hp d
    (t + 2) (t + 2) (Math115.PhysicalStarBudget.attempts dimension t)
    (Math115.PhysicalStarBudget.precision dimension t)
  have hclock : (1 / 2 : ℚ)^(t + 2) = dyadic (t + 2) := by simp [dyadic]
  rw [hclock] at he
  have hexit : exitAllowance dimension (Math115.PhysicalStarBudget.attempts dimension t)
      (Math115.PhysicalStarBudget.precision dimension t) ≤ dyadic (t + 1) :=
    Math115.PhysicalStarBudget.exit_budget dimension t
  have hsum : dyadic (t + 2) + dyadic (t + 2) + dyadic (t + 1) = dyadic t := by
    have h0 := dyadic_succ t
    have h1 := dyadic_succ (t + 1)
    linarith
  exact he.trans ((add_le_add (le_refl _) hexit).trans hsum.le)

end
end Math115.PhysicalTraceJoin
