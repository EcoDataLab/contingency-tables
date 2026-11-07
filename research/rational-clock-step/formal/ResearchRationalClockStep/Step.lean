/-
SPDX-License-Identifier: Apache-2.0
One incoming rational-clock proposal and completion-acceptance step from
a fixed actual defect. Accepted balanced outputs are retained. This module
does not compose their subsequent exits or supply adaptive outer word banks.
-/
import ResearchRationalClock.Proposal
import ResearchPhysicalStar.Trial
import ResearchListedAcceptance.Decision

set_option maxHeartbeats 800000

namespace Math115.RationalClockStep

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles CompletionTranslation
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open CompletionCounts PaddedCompletions FirstSuccess ResidualMixture FairBits
open Math115.ReducedSmallChain Math115.PhysicalCompletionOracle
open Math115.PhysicalDefectTrace Math115.LegacyPhysicalCompletion
open Math115.ListedAcceptance Math115.PhysicalStarTrial
open Math115.RationalClockProposal Math115.CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section

/-- Off-diagonal identification for any normalized proposal law; no
separate conductance-total hypothesis is needed. -/
lemma decisionBind_mass_ne
    {X I J : Type*} [Fintype X] [Fintype I] [Fintype J] [DecidableEq X]
    (R : X → Option I → ℕ) (P : X → Option J → ℕ)
    (q : RationalLaw (Option X)) (x y : X) (hne : x ≠ y)
    (μ : RationalLaw (Table (R x) (P x))) :
    (bindLaw q (fun proposal => mapLaw μ (completionDecision R P x proposal))).mass y =
      q.mass (some y) * (∑ a : Table (R x) (P x),
        if ∀ i j, 0 ≤ (a.val i j : ℤ) + between (R x) (R y) (P x) (P y) i j
        then μ.mass a else 0) := by
  change (∑ proposal : Option X, q.mass proposal *
    ∑ a : Table (R x) (P x), if completionDecision R P x proposal a = y
      then μ.mass a else 0) = _
  simp_rw [completionDecision_eq R P x y hne]
  rw [Fintype.sum_option]
  simp only [reduceCtorEq, false_and, ite_false, Finset.sum_const_zero, mul_zero,
    zero_add, Option.some.injEq]
  have hh (z : X) : (∑ a : Table (R x) (P x),
      if z = y ∧ ∀ i j, 0 ≤ (a.val i j : ℤ) + between (R x) (R y) (P x) (P y) i j
      then μ.mass a else 0) =
      if z = y then ∑ a : Table (R x) (P x),
        if ∀ i j, 0 ≤ (a.val i j : ℤ) + between (R x) (R y) (P x) (P y) i j
        then μ.mass a else 0 else 0 := by
    by_cases hz : z = y <;> simp [hz]
  simp_rw [hh]
  simp [mul_ite]

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

local notation "B" => capacity r c U L
local notation "i₀" => largeOptionEquiv r U hr none
local notation "j₀" => largeOptionEquiv c U hc none
local notation "R₀" => referenceRows r c U L B i₀
local notation "P₀" => referenceColumns r c U L B j₀
local notation "clockWidth" => precision (denominator r c U)

def proposalLawAt (x : DefectVertices r c U L) (N : ℕ) :
    RationalLaw (Option (States r c U L)) :=
  mapLaw (uniformLaw (α := Fin (N * clockWidth) → Bool)) (physicalProposal r c U L x N)

/-- The completion word belongs to the current source x, including when the
proposal selects a balanced target. -/
def incomingStep (x : DefectVertices r c U L) (N h : ℕ)
    (word : Fin (N * clockWidth + bits r c U L hr hc x.val h) → Bool) : States r c U L :=
  let parts := splitWordEquiv (N * clockWidth) (bits r c U L hr hc x.val h) word
  match physicalProposal r c U L x N parts.1 with
  | none => x.val
  | some y =>
    if translationValid
      (((List.ofFn (coarseRows r c U L hr x.val), List.ofFn (coarseColumns r c U L hc x.val)),
        (List.ofFn (coarseRows r c U L hr y), List.ofFn (coarseColumns r c U L hc y))),
        LatticeSampler.draw
          (((List.ofFn (coarseRows r c U L hr x.val),
            List.ofFn (coarseColumns r c U L hc x.val)), h), List.ofFn parts.2))
    then y else x.val

def incomingLaw (x : DefectVertices r c U L) (N h : ℕ) : RationalLaw (States r c U L) :=
  mapLaw (uniformLaw (α := Fin (N * clockWidth + bits r c U L hr hc x.val h) → Bool))
    (incomingStep r c U L hr hc x N h)

def idealIncomingLaw (hp : 2 ≤ Fintype.card (SmallContextCoordinates.Cells (firstPaperSmall r c U)))
    (x : DefectVertices r c U L) : RationalLaw (States r c U L) :=
  bindLaw (idealPhysicalProposalLaw r c U L hp x)
    (fun proposal => mapLaw (uniformLaw (α := ReferenceTable r c U L i₀ j₀ x.val))
      (completionDecision R₀ P₀ x.val proposal))

lemma incomingStep_eq (x : DefectVertices r c U L) (N h : ℕ)
    (word : Fin (N * clockWidth + bits r c U L hr hc x.val h) → Bool) :
    incomingStep r c U L hr hc x N h word =
      let parts := splitWordEquiv (N * clockWidth) (bits r c U L hr hc x.val h) word
      completionDecision R₀ P₀ x.val (physicalProposal r c U L x N parts.1)
        (referenceCompletion r c U L hr hc x.val
          (completionDraw r c U L hr hc x.val h parts.2)) := by
  dsimp only [incomingStep]
  exact draw_completionDecision r c U L hr hc x.val
    (physicalProposal r c U L x N
      (splitWordEquiv (N * clockWidth) (bits r c U L hr hc x.val h) word).1) h
    (splitWordEquiv (N * clockWidth) (bits r c U L hr hc x.val h) word).2

/-- This uses only the current state's fixed width and the explicit split. -/
theorem incomingLaw_eq (x : DefectVertices r c U L) (N h : ℕ) :
    incomingLaw r c U L hr hc x N h =
      bindLaw (proposalLawAt r c U L x N)
        (fun proposal => mapLaw (oracleFamily r c U L hr hc h i₀ j₀ x.val)
          (completionDecision R₀ P₀ x.val proposal)) := by
  unfold incomingLaw
  have hpoint := funext (incomingStep_eq r c U L hr hc x N h)
  rw [hpoint]
  calc
    _ = bindLaw
        (mapLaw (uniformLaw (α := Fin (N * clockWidth) → Bool)) (physicalProposal r c U L x N))
        (fun proposal => mapLaw
          (mapLaw (uniformLaw (α := Fin (bits r c U L hr hc x.val h) → Bool))
            (fun word => referenceCompletion r c U L hr hc x.val
              (completionDraw r c U L hr hc x.val h word)))
          (completionDecision R₀ P₀ x.val proposal)) :=
      fixedWord_finish_law (physicalProposal r c U L x N)
        (fun word => referenceCompletion r c U L hr hc x.val
          (completionDraw r c U L hr hc x.val h word))
        (completionDecision R₀ P₀ x.val)
    _ = _ := by
      rw [referenceDraw_law r c U L hr hc x.val h]
      rfl

/-- Proposal exhaustion and source completion error add before any later
balanced-star exit. No conditioning or adaptive outer-bank claim is used. -/
theorem incomingLaw_accuracy
    (hp : 2 ≤ Fintype.card (SmallContextCoordinates.Cells (firstPaperSmall r c U)))
    (x : DefectVertices r c U L) (N h : ℕ) :
    variation (incomingLaw r c U L hr hc x N h) (idealIncomingLaw r c U L hr hc hp x) ≤
      (1 / 2 : ℚ)^N + dyadic h := by
  rw [incomingLaw_eq]
  unfold idealIncomingLaw
  have he := variation_bind_uniform (proposalLawAt r c U L x N)
    (idealPhysicalProposalLaw r c U L hp x)
    (fun proposal => mapLaw (oracleFamily r c U L hr hc h i₀ j₀ x.val)
      (completionDecision R₀ P₀ x.val proposal))
    (fun proposal => mapLaw (uniformLaw (α := ReferenceTable r c U L i₀ j₀ x.val))
      (completionDecision R₀ P₀ x.val proposal))
    (dyadic h)
    (fun proposal => (variation_map _ _ (completionDecision R₀ P₀ x.val proposal)).trans
      (oracleFamily_accuracy r c U L hr hc h i₀ j₀ x.val))
  exact he.trans (add_le_add (physicalProposal_variation r c U L hp x N) le_rfl)

/-- Distinct target mass under the ideal rational-clock proposal and source
uniform completion. Source holding is determined by the normalized law. -/
theorem idealIncomingLaw_mass_ne (htotal : (∑ i, r i) = ∑ j, c j)
    (hp : 2 ≤ Fintype.card (SmallContextCoordinates.Cells (firstPaperSmall r c U)))
    (x : DefectVertices r c U L) (y : States r c U L) (hne : x.val ≠ y) :
    (idealIncomingLaw r c U L hr hc hp x).mass y =
      if physicalAdjacent r c U L B (capacity_small r c U L) x.val y then
        (acceptedCount R₀ P₀ x.val y : ℚ) /
          ((denominator r c U : ℚ) * (blockCount R₀ P₀ x.val : ℚ))
      else 0 := by
  unfold idealIncomingLaw
  rw [decisionBind_mass_ne R₀ P₀ _ x.val y hne,
    uniformAcceptedMass, idealPhysicalProposalLaw_mass r c U L htotal hp x y]
  by_cases hxy : physicalAdjacent r c U L B (capacity_small r c U L) x.val y
  · simp only [ite_eq_left hxy, div_eq_mul_inv, mul_inv_rev]
    ring
  · simp only [ite_eq_right hxy, zero_mul]

theorem idealIncomingLaw_mass_ne_cast (htotal : (∑ i, r i) = ∑ j, c j)
    (hp : 2 ≤ Fintype.card (SmallContextCoordinates.Cells (firstPaperSmall r c U)))
    (x : DefectVertices r c U L) (y : States r c U L) (hne : x.val ≠ y) :
    ((idealIncomingLaw r c U L hr hc hp x).mass y : ℝ) =
      referenceConductance r c U L i₀ j₀ x.val y /
        (2 * (defectAllowance r c U : ℝ) * defectWeight r c U L x) := by
  change _ = referenceConductance r c U L i₀ j₀ x.val y /
    (2 * (defectAllowance r c U : ℝ) * weight r c U L x.val)
  rw [reference_weight r c U L i₀ j₀ x.val,
    idealIncomingLaw_mass_ne r c U L hr hc htotal hp x y hne]
  unfold referenceConductance
  by_cases hxy : physicalAdjacent r c U L B (capacity_small r c U L) x.val y
  · simp only [ite_eq_left hxy, denominator, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
      Nat.cast_mul, Nat.cast_ofNat, Rat.cast_ofNat]
  · simp only [ite_eq_right hxy, Rat.cast_zero, zero_div]

end
end Math115.RationalClockStep
