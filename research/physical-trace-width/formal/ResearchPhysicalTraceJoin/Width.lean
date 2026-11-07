/-
SPDX-License-Identifier: Apache-2.0
An explicit state-independent completion-word allowance and one-step bank.
The exponent and coefficient are the existing frozen sampler's reserved-bit
bound. This module supplies no extracted machine or machine-time estimate.
-/
import ResearchPhysicalTraceJoin.Word
import ResearchPhysicalCompletionWidth.Bound

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open FirstSuccess ResidualMixture
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.LegacyPhysicalCompletion Math115.LegacyResidualCap
open Math115.CompletionRetryBudget
open Math115.PhysicalCompletionWidth
open scoped BigOperators Classical

noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

local notation "dimension" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => Nat.clog 2 (32 * dimension^2)

def commonExitWidth (J hExit : ℕ) : ℕ :=
  J * (s + uniformCompletionBits r c U L hExit)

theorem balancedExitWidth_le_common (b : BalancedVertices r c U L) (J hExit : ℕ) :
    balancedExitWidth r c U L hr hc b J hExit ≤ commonExitWidth r c U L J hExit := by
  unfold balancedExitWidth commonExitWidth
  exact Nat.mul_le_mul_left J (Nat.add_le_add_left
    (completionBits_le_uniform r c U L hr hc b.val hExit) s)

/-- The explicit allowance discharges the common-width premise of joinedWord.
The incoming and exit blocks remain disjoint. -/
def boundedJoinedWord (d : DefectVertices r c U L) (N hIn J hExit : ℕ)
    (word : Fin (incomingWidth r c U L hr hc d N hIn + commonExitWidth r c U L J hExit) → Bool) :
    DefectVertices r c U L :=
  joinedWord r c U L hr hc d N hIn J hExit (commonExitWidth r c U L J hExit)
    (fun b => balancedExitWidth_le_common r c U L hr hc b J hExit) word

theorem boundedJoinedWord_law (d : DefectVertices r c U L) (N hIn J hExit : ℕ) :
    mapLaw (uniformLaw (α :=
      Fin (incomingWidth r c U L hr hc d N hIn + commonExitWidth r c U L J hExit) → Bool))
      (boundedJoinedWord r c U L hr hc d N hIn J hExit) =
      actualJoinedLaw r c U L hr hc d N hIn J hExit :=
  joinedWord_law r c U L hr hc d N hIn J hExit (commonExitWidth r c U L J hExit)
    (fun b => balancedExitWidth_le_common r c U L hr hc b J hExit)

theorem boundedJoinedWord_accuracy (htotal : (∑ i, r i) = ∑ j, c j)
    (hL : 7 ≤ L) (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d : DefectVertices r c U L) (N hIn J hExit : ℕ) :
    variation
      (mapLaw (uniformLaw (α :=
        Fin (incomingWidth r c U L hr hc d N hIn + commonExitWidth r c U L J hExit) → Bool))
        (boundedJoinedWord r c U L hr hc d N hIn J hExit))
      (idealJoinedLaw r c U L hr hc hp d) ≤
      (1 / 2 : ℚ)^N + dyadic hIn + exitAllowance dimension J hExit := by
  rw [boundedJoinedWord_law]
  exact actualJoinedLaw_accuracy r c U L hr hc htotal hL hp d N hIn J hExit

/-- One scheduled step now has a proved explicit finite fair-bit reservation.
This is not a repeated-walk or encoded-machine cost statement. -/
theorem scheduledBoundedJoinedWord_accuracy (htotal : (∑ i, r i) = ∑ j, c j)
    (hL : 7 ≤ L) (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d : DefectVertices r c U L) (t : ℕ) :
    variation
      (mapLaw (uniformLaw (α := Fin
        (incomingWidth r c U L hr hc d (t + 2) (t + 2) +
          commonExitWidth r c U L (Math115.PhysicalStarBudget.attempts dimension t)
            (Math115.PhysicalStarBudget.precision dimension t)) → Bool))
        (boundedJoinedWord r c U L hr hc d (t + 2) (t + 2)
          (Math115.PhysicalStarBudget.attempts dimension t)
          (Math115.PhysicalStarBudget.precision dimension t)))
      (idealJoinedLaw r c U L hr hc hp d) ≤ dyadic t := by
  rw [boundedJoinedWord_law]
  exact scheduledJoinedLaw_accuracy r c U L hr hc htotal hL hp d t

/-- One fixed width for every starting defect. The final padding suffix is
unused; the original incoming/exit split is retained inside its prefix. -/
def uniformStepWidth (N hIn J hExit : ℕ) : ℕ :=
  N * Math115.RationalClockProposal.precision (Math115.RationalClockProposal.denominator r c U) +
    uniformCompletionBits r c U L hIn + commonExitWidth r c U L J hExit

theorem joinedWidth_le_uniform (d : DefectVertices r c U L) (N hIn J hExit : ℕ) :
    incomingWidth r c U L hr hc d N hIn + commonExitWidth r c U L J hExit ≤
      uniformStepWidth r c U L N hIn J hExit := by
  unfold incomingWidth uniformStepWidth
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (completionBits_le_uniform r c U L hr hc d.val hIn)
    (N * Math115.RationalClockProposal.precision (Math115.RationalClockProposal.denominator r c U)))
    (commonExitWidth r c U L J hExit)

/-- The starting defect is fixed before this fresh uniform-width word. The
padding does not compute or inspect a maximum over the physical state space. -/
def uniformJoinedWord (d : DefectVertices r c U L) (N hIn J hExit : ℕ)
    (word : Fin (uniformStepWidth r c U L N hIn J hExit) → Bool) : DefectVertices r c U L :=
  boundedJoinedWord r c U L hr hc d N hIn J hExit
    (prefixWord (joinedWidth_le_uniform r c U L hr hc d N hIn J hExit) word)

theorem uniformJoinedWord_law (d : DefectVertices r c U L) (N hIn J hExit : ℕ) :
    mapLaw (uniformLaw (α := Fin (uniformStepWidth r c U L N hIn J hExit) → Bool))
      (uniformJoinedWord r c U L hr hc d N hIn J hExit) =
      actualJoinedLaw r c U L hr hc d N hIn J hExit :=
  (padded_draw_law (joinedWidth_le_uniform r c U L hr hc d N hIn J hExit)
    (boundedJoinedWord r c U L hr hc d N hIn J hExit)).trans
      (boundedJoinedWord_law r c U L hr hc d N hIn J hExit)

theorem uniformJoinedWord_accuracy (htotal : (∑ i, r i) = ∑ j, c j)
    (hL : 7 ≤ L) (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d : DefectVertices r c U L) (N hIn J hExit : ℕ) :
    variation
      (mapLaw (uniformLaw (α := Fin (uniformStepWidth r c U L N hIn J hExit) → Bool))
        (uniformJoinedWord r c U L hr hc d N hIn J hExit))
      (idealJoinedLaw r c U L hr hc hp d) ≤
      (1 / 2 : ℚ)^N + dyadic hIn + exitAllowance dimension J hExit := by
  rw [uniformJoinedWord_law]
  exact actualJoinedLaw_accuracy r c U L hr hc htotal hL hp d N hIn J hExit

/-- The scheduled step has the same explicit width for every starting
defect. Repeated-walk execution and its reservation remain separate. -/
theorem scheduledUniformJoinedWord_accuracy (htotal : (∑ i, r i) = ∑ j, c j)
    (hL : 7 ≤ L) (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d : DefectVertices r c U L) (t : ℕ) :
    variation
      (mapLaw (uniformLaw (α := Fin
        (uniformStepWidth r c U L (t + 2) (t + 2)
          (Math115.PhysicalStarBudget.attempts dimension t)
          (Math115.PhysicalStarBudget.precision dimension t)) → Bool))
        (uniformJoinedWord r c U L hr hc d (t + 2) (t + 2)
          (Math115.PhysicalStarBudget.attempts dimension t)
          (Math115.PhysicalStarBudget.precision dimension t)))
      (idealJoinedLaw r c U L hr hc hp d) ≤ dyadic t := by
  rw [uniformJoinedWord_law]
  exact scheduledJoinedLaw_accuracy r c U L hr hc htotal hL hp d t

end
end Math115.PhysicalTraceJoin
