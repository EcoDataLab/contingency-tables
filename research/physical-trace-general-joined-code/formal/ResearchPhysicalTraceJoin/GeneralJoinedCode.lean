/-
SPDX-License-Identifier: Apache-2.0
Computational raw joined defect step and walk. The balanced exit begins
after the actual source completion block; uniform padding is a final
ignored suffix. All randomness is supplied in the existing fixed order.
-/
import ResearchPhysicalTraceJoin.GeneralStarCode
import ResearchPhysicalTraceJoin.GeneralScheduleCode

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms FairBits FirstSuccess
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalComputedProposal Math115.LegacyPhysicalCompletion
open Math115.RationalClockProposal Math115.RationalClockStep
open scoped BigOperators

def rawIncomingCodeWidth (rs cs : List ℕ) (U L N h : ℕ) (source : List ℕ × List ℕ) : ℕ :=
  N * Nat.clog 2 (rawScheduleClockDenominator rs cs U) + rawCompletionBits rs cs U L source h

def rawCommonExitCodeWidth (rs cs : List ℕ) (U L J h : ℕ) : ℕ :=
  J * (Nat.clog 2 (32 * (rawScheduleDimension rs cs)^2) + rawUniformCompletionBits rs cs U L h)

/-- Defective arrivals ignore the exit block. Balanced arrivals retry from
that fixed balanced source, with the original entering defect as fallback. -/
def rawCommonExit (rs cs : List ℕ) (U L J h : ℕ)
    (entering reached : List ℕ × List ℕ) (word : List Bool) : List ℕ × List ℕ :=
  if balancedTest (reached, U) then
    rawStarExit rs cs U L (rawScheduleDimension rs cs) h reached entering J word
  else reached

/-- The split uses actual source completion width, rather than the common
completion allowance. Incoming and exit words remain disjoint. -/
def rawBoundedJoinedStep (rs cs : List ℕ) (U L N hIn J hExit : ℕ)
    (source : List ℕ × List ℕ) (word : List Bool) : List ℕ × List ℕ :=
  let a := rawIncomingCodeWidth rs cs U L N hIn source
  let reached := rawIncomingAcceptedStep rs cs U L (rawScheduleClockDenominator rs cs U)
    N hIn source (word.take a)
  rawCommonExit rs cs U L J hExit source reached (word.drop a)

/-- Exactly the typed uniform-step wrapper: take the actual incoming bank
and common exit bank first, leaving all uniform-completion slack at the end. -/
def rawJoinedStep (rs cs : List ℕ) (U L N hIn J hExit : ℕ)
    (source : List ℕ × List ℕ) (word : List Bool) : List ℕ × List ℕ :=
  rawBoundedJoinedStep rs cs U L N hIn J hExit source
    (word.take (rawIncomingCodeWidth rs cs U L N hIn source +
      rawCommonExitCodeWidth rs cs U L J hExit))

/-- Fixed uniform-width blocks, processed in order from the current defect.
T=0 returns the original start, including for a zero-width generic bank. -/
def rawJoinedWalk (rs cs : List ℕ) (U L N hIn J hExit T : ℕ)
    (start : List ℕ × List ℕ) (word : List Bool) : List ℕ × List ℕ :=
  rawAcceptedWalk (rawJoinedStep rs cs U L N hIn J hExit) start
    (rawFixedBlocks T (rawUniformStepWidth rs cs U L N hIn J hExit) word)

noncomputable section
open scoped Classical
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

theorem rawIncomingCodeWidth_eq (d : DefectVertices r c U L) (N h : ℕ) :
    rawIncomingCodeWidth (List.ofFn r) (List.ofFn c) U L N h
      (computedStateCode r c U L d.val) = incomingWidth r c U L hr hc d N h := by
  unfold rawIncomingCodeWidth incomingWidth
  rw [rawScheduleClockDenominator_eq, rawCompletionBits_eq r c U L hr hc d.val h]
  rfl

theorem rawCommonExitCodeWidth_eq (J h : ℕ) :
    rawCommonExitCodeWidth (List.ofFn r) (List.ofFn c) U L J h = commonExitWidth r c U L J h := by
  unfold rawCommonExitCodeWidth commonExitWidth
  rw [rawScheduleDimension_eq, rawUniformCompletionBits_eq]

theorem rawCommonExit_eq (htotal : (∑ i, r i) = ∑ j, c j)
    (d : DefectVertices r c U L) (J h W : ℕ)
    (hW : ∀ b : BalancedVertices r c U L, balancedExitWidth r c U L hr hc b J h ≤ W)
    (reached : States r c U L) (word : Fin W → Bool) :
    rawCommonExit (List.ofFn r) (List.ofFn c) U L J h
      (computedStateCode r c U L d.val) (computedStateCode r c U L reached) (List.ofFn word) =
        computedStateCode r c U L
          (commonExitDraw r c U L hr hc d J h W hW reached word).val := by
  unfold rawCommonExit
  rw [rawScheduleDimension_eq]
  by_cases hb : IsBalanced r c U L reached
  · have ht := (rawBalancedTest_eq r c U L reached).mpr hb
    simp only [ht, ite_true, commonExitDraw, dite_eq_left hb]
    exact rawStarExit_eq_reserved r c U L hr hc htotal ⟨reached, hb⟩ h d J W
      (hW ⟨reached, hb⟩) word
  · have ht : balancedTest (computedStateCode r c U L reached, U) = false :=
      Bool.eq_false_iff.mpr (fun h => hb ((rawBalancedTest_eq r c U L reached).mp h))
    simp only [ht, Bool.false_eq_true, ite_false, commonExitDraw, dite_eq_right hb]

/-- Pointwise correspondence before the final uniform padding wrapper. -/
theorem rawBoundedJoinedStep_eq (htotal : (∑ i, r i) = ∑ j, c j)
    (d : DefectVertices r c U L) (N hIn J hExit : ℕ)
    (word : Fin (incomingWidth r c U L hr hc d N hIn + commonExitWidth r c U L J hExit) → Bool) :
    rawBoundedJoinedStep (List.ofFn r) (List.ofFn c) U L N hIn J hExit
      (computedStateCode r c U L d.val) (List.ofFn word) =
        computedStateCode r c U L (boundedJoinedWord r c U L hr hc d N hIn J hExit word).val := by
  let parts := splitWordEquiv (incomingWidth r c U L hr hc d N hIn)
    (commonExitWidth r c U L J hExit) word
  have hi := rawIncomingAcceptedStep_eq r c U L hr hc htotal d N hIn parts.1
  unfold rawBoundedJoinedStep
  dsimp only
  rw [rawIncomingCodeWidth_eq r c U L hr hc d N hIn, ofFn_split_take word,
    ofFn_split_drop word, rawScheduleClockDenominator_eq]
  have hmap := congrArg (fun reached => rawCommonExit (List.ofFn r) (List.ofFn c)
    U L J hExit (computedStateCode r c U L d.val) reached (List.ofFn parts.2)) hi
  exact hmap.trans (rawCommonExit_eq r c U L hr hc htotal d J hExit _
    (fun b => balancedExitWidth_le_common r c U L hr hc b J hExit)
    (incomingStep r c U L hr hc d N hIn parts.1) parts.2)

/-- Same-word correspondence to the genuine joined defect step, including
the balanced-star exit and the source-dependent internal offset. -/
theorem rawJoinedStep_eq (htotal : (∑ i, r i) = ∑ j, c j)
    (d : DefectVertices r c U L) (N hIn J hExit : ℕ)
    (word : Fin (uniformStepWidth r c U L N hIn J hExit) → Bool) :
    rawJoinedStep (List.ofFn r) (List.ofFn c) U L N hIn J hExit
      (computedStateCode r c U L d.val) (List.ofFn word) =
        computedStateCode r c U L (uniformJoinedWord r c U L hr hc d N hIn J hExit word).val := by
  unfold rawJoinedStep
  rw [rawIncomingCodeWidth_eq r c U L hr hc d N hIn, rawCommonExitCodeWidth_eq,
    DensePrograms.take_ofFn_prefix (joinedWidth_le_uniform r c U L hr hc d N hIn J hExit) word]
  exact rawBoundedJoinedStep_eq r c U L hr hc htotal d N hIn J hExit _

/-- The concrete raw step discharges the generic walk bridge's premise;
the result identifies the entire stronger-trace walk on every supplied word. -/
theorem rawJoinedWalk_eq (htotal : (∑ i, r i) = ∑ j, c j)
    (start : DefectVertices r c U L) (N hIn J hExit T : ℕ)
    (word : Fin (T * uniformStepWidth r c U L N hIn J hExit) → Bool) :
    rawJoinedWalk (List.ofFn r) (List.ofFn c) U L N hIn J hExit T
      (computedStateCode r c U L start.val) (List.ofFn word) =
        computedStateCode r c U L
          (joinedWalkWord r c U L hr hc start N hIn J hExit T word).val := by
  unfold rawJoinedWalk
  rw [rawUniformStepWidth_eq, rawFixedBlocks_ofFn]
  exact rawAcceptedWalk_eq_wordWalk
    (fun d : DefectVertices r c U L => computedStateCode r c U L d.val)
    (uniformJoinedWord r c U L hr hc · N hIn J hExit)
    (rawJoinedStep (List.ofFn r) (List.ofFn c) U L N hIn J hExit)
    (fun d block => rawJoinedStep_eq r c U L hr hc htotal d N hIn J hExit block)
    start T _

end
end Math115.PhysicalTraceJoin
