/-
SPDX-License-Identifier: Apache-2.0
A bounded walk driven by fresh uniform-width physical joined-step words.
The initial defect is supplied. No initialization, mixing, stationary output,
outer correction or encoded-machine cost statement is provided.
-/
import ResearchPhysicalTraceJoin.Width
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordWalk

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open FirstSuccess ResidualMixture FairBits
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.CompletionBooleanRetry Math115.CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section

/-- Flatten the existing wordWalk through the existing word-bank equivalence. -/
def flatWordWalk {X : Type*} [Fintype X] [DecidableEq X] {B : ℕ} (step : X → (Fin B → Bool) → X)
    (start : X) (T : ℕ) (word : Fin (T * B) → Bool) : X :=
  wordWalk step start T (wordBankEquiv B T word)

theorem flatWordWalk_law
    {X : Type*} [Fintype X] [DecidableEq X] {B : ℕ}
    (step : X → (Fin B → Bool) → X) (start : X) (T : ℕ) :
    mapLaw (uniformLaw (α := Fin (T * B) → Bool)) (flatWordWalk step start T) =
      walkLaw (fun x => mapLaw (uniformLaw (α := Fin B → Bool)) (step x)) start T := by
  change mapLaw (uniformLaw (α := Fin (T * B) → Bool))
    (fun bits => wordWalk step start T (wordBankEquiv B T bits)) = _
  rw [← map_equiv (wordBankEquiv B T), uniform_equiv]
  exact wordWalkLaw_eq step start T

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

local notation "dimension" => dimensionAllowance (I := Fin m) (J := Fin n)

/-- Each transition receives a disjoint block of the same proved step width.
Its source state may depend on earlier blocks. -/
def joinedWalkWord (start : DefectVertices r c U L) (N hIn J hExit T : ℕ)
    (word : Fin (T * uniformStepWidth r c U L N hIn J hExit) → Bool) :
    DefectVertices r c U L :=
  flatWordWalk (fun d => uniformJoinedWord r c U L hr hc d N hIn J hExit) start T word

/-- The exact finite-word law uses the existing independent-word walk theorem;
the literal joined-step maps are unchanged at every reached defect. -/
theorem joinedWalkWord_law (start : DefectVertices r c U L) (N hIn J hExit T : ℕ) :
    mapLaw (uniformLaw (α := Fin (T * uniformStepWidth r c U L N hIn J hExit) → Bool))
      (joinedWalkWord r c U L hr hc start N hIn J hExit T) =
      walkLaw (fun d => actualJoinedLaw r c U L hr hc d N hIn J hExit) start T := by
  unfold joinedWalkWord
  rw [flatWordWalk_law]
  have hkernel :
      (fun d : DefectVertices r c U L =>
        mapLaw (uniformLaw (α := Fin (uniformStepWidth r c U L N hIn J hExit) → Bool))
          (uniformJoinedWord r c U L hr hc d N hIn J hExit)) =
      (fun d => actualJoinedLaw r c U L hr hc d N hIn J hExit) := by
    funext d
    exact uniformJoinedWord_law r c U L hr hc d N hIn J hExit
  rw [hkernel]

/-- One-step TV errors accumulate before any terminal correction. -/
theorem joinedWalkWord_accuracy (htotal : (∑ i, r i) = ∑ j, c j)
    (hL : 7 ≤ L) (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (start : DefectVertices r c U L) (N hIn J hExit T : ℕ) :
    variation
      (mapLaw (uniformLaw (α := Fin (T * uniformStepWidth r c U L N hIn J hExit) → Bool))
        (joinedWalkWord r c U L hr hc start N hIn J hExit T))
      (walkLaw (idealJoinedLaw r c U L hr hc hp) start T) ≤
      (T : ℚ) * ((1 / 2 : ℚ)^N + dyadic hIn + exitAllowance dimension J hExit) := by
  rw [joinedWalkWord_law]
  exact walkLaw_variation
    (fun d => actualJoinedLaw r c U L hr hc d N hIn J hExit)
    (idealJoinedLaw r c U L hr hc hp)
    ((1 / 2 : ℚ)^N + dyadic hIn + exitAllowance dimension J hExit)
    (fun d => actualJoinedLaw_accuracy r c U L hr hc htotal hL hp d N hIn J hExit)
    start T

/-- The checked local schedule supplies one-step error dyadic t uniformly
over reached defects; no mixing assertion is used to obtain the walk bound. -/
theorem scheduledJoinedWalkWord_accuracy (htotal : (∑ i, r i) = ∑ j, c j)
    (hL : 7 ≤ L) (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (start : DefectVertices r c U L) (t T : ℕ) :
    variation
      (mapLaw (uniformLaw (α := Fin
        (T * uniformStepWidth r c U L (t + 2) (t + 2)
          (Math115.PhysicalStarBudget.attempts dimension t)
          (Math115.PhysicalStarBudget.precision dimension t)) → Bool))
        (joinedWalkWord r c U L hr hc start (t + 2) (t + 2)
          (Math115.PhysicalStarBudget.attempts dimension t)
          (Math115.PhysicalStarBudget.precision dimension t) T))
      (walkLaw (idealJoinedLaw r c U L hr hc hp) start T) ≤ (T : ℚ) * dyadic t := by
  rw [joinedWalkWord_law]
  exact walkLaw_variation
    (fun d => actualJoinedLaw r c U L hr hc d (t + 2) (t + 2)
      (Math115.PhysicalStarBudget.attempts dimension t)
      (Math115.PhysicalStarBudget.precision dimension t))
    (idealJoinedLaw r c U L hr hc hp) (dyadic t)
    (fun d => scheduledJoinedLaw_accuracy r c U L hr hc htotal hL hp d t) start T

end
end Math115.PhysicalTraceJoin
