/-
SPDX-License-Identifier: Apache-2.0
Concrete corrected reference trial. Each block is taken from the same
fixed word as the typed sampler; no fresh probability argument or desired
accuracy premise is introduced by the representation correspondence.
-/
import ResearchPhysicalTraceJoin.GeneralJoinedCode
import ResearchPhysicalTraceJoin.GeneralLabelCode
import ResearchPhysicalTraceJoin.GeneralScheduleCode

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms FirstSuccess ResidualMixture FairBits
open FirstPaperProfiles CompletionCounts PhysicalCompletionFibres
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalComputedProposal Math115.PhysicalCompletionWidth
open scoped BigOperators

/-- Fresh residual completion followed by literal repair and bounded coin.
All terminal labels and completion arguments are computed from raw inputs. -/
def rawTerminalCorrectedCode (rs cs : List ℕ) (U L : ℕ)
    (state : List ℕ × List ℕ) (hTerm k : ℕ)
    (completionWord correctionWord : List Bool) : Option MatrixCode :=
  jointAutoCorrectionCode rs cs U L k state
    (rawCompletionResidual rs cs U L state hTerm completionWord) correctionWord

/-- The outer split isolates correction bits. The inner split then
isolates the walk and its independent terminal completion bank. -/
def rawCorrectedTrial (rs cs : List ℕ) (U L : ℕ)
    (start : List ℕ × List ℕ) (h k : ℕ) (word : List Bool) : Option MatrixCode :=
  let t := rawScheduleStepPrecision rs cs U L h
  let d := rawScheduleDimension rs cs
  let J := rawScheduleExitAttempts d t
  let hExit := rawScheduleExitPrecision d t
  let T := rawScheduleSteps rs cs U L h
  let W := rawUniformStepWidth rs cs U L (t+2) (t+2) J hExit
  let bank := rawTerminalScheduleWordWidth rs cs U L h
  let jointWord := word.take bank
  let correctionWord := (word.drop bank).take k
  let state := rawJoinedWalk rs cs U L (t+2) (t+2) J hExit T start
    (jointWord.take (T*W))
  rawTerminalCorrectedCode rs cs U L state (h+2) k
    (jointWord.drop (T*W)) correctionWord

open scoped Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U,List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U,List.ofFn c)).length)

theorem rawTerminalCorrectedCode_eq (d : DefectVertices r c U L) (hTerm k : ℕ)
    (completionWord : Fin (uniformCompletionBits r c U L hTerm) → Bool)
    (correctionWord : Fin k → Bool) :
    rawTerminalCorrectedCode (List.ofFn r) (List.ofFn c) U L
      (computedStateCode r c U L d.val) hTerm k
      (List.ofFn completionWord) (List.ofFn correctionWord) =
      (terminalBitCorrection r c U L k
        ⟨d,terminalCompletion r c U L hr hc d hTerm completionWord⟩ correctionWord).map
        (fun X => matrixCode X.val) := by
  unfold rawTerminalCorrectedCode
  rw [rawCompletionResidual_terminal r c U L hr hc d hTerm completionWord]
  exact jointAutoCorrectionCode_eq r c U L hr hc _ k correctionWord

/-- Pointwise equality to the whole typed corrected trial. In particular,
padding failure and coin rejection remain none on the same supplied word. -/
theorem rawCorrectedTrial_eq
    (htotal : (∑ i, r i) = ∑ j, c j)
    (start : DefectVertices r c U L) (h k : ℕ)
    (word : Fin (terminalCorrectedWordWidth r c U L h k) → Bool) :
    rawCorrectedTrial (List.ofFn r) (List.ofFn c) U L
      (computedStateCode r c U L start.val) h k (List.ofFn word) =
      (terminalCorrectedWord r c U L hr hc start h k word).map
        (fun X => matrixCode X.val) := by
  let t := terminalScheduleStepPrecision r c U L h
  let d := dimensionAllowance (I := Fin m) (J := Fin n)
  let J := Math115.PhysicalStarBudget.attempts d t
  let hExit := Math115.PhysicalStarBudget.precision d t
  let T := terminalScheduleSteps r c U L h
  let W := uniformStepWidth r c U L (t+2) (t+2) J hExit
  let outer := splitWordEquiv (terminalScheduleWordWidth r c U L h) k word
  let inner := splitWordEquiv (T*W) (uniformCompletionBits r c U L (h+2)) outer.1
  have hoTake : (List.ofFn word).take (terminalScheduleWordWidth r c U L h) =
      List.ofFn outer.1 := ofFn_split_take word
  have hoDrop : (List.ofFn word).drop (terminalScheduleWordWidth r c U L h) =
      List.ofFn outer.2 := ofFn_split_drop word
  have hiTake : (List.ofFn outer.1).take (T*W) = List.ofFn inner.1 :=
    ofFn_split_take outer.1
  have hiDrop : (List.ofFn outer.1).drop (T*W) = List.ofFn inner.2 :=
    ofFn_split_drop outer.1
  simp only [rawCorrectedTrial, rawScheduleStepPrecision_eq, rawScheduleDimension_eq,
    rawScheduleExitAttempts_eq, rawScheduleExitPrecision_eq, rawScheduleSteps_eq,
    rawUniformStepWidth_eq, rawTerminalScheduleWordWidth_eq]
  change rawTerminalCorrectedCode _ _ _ _
    (rawJoinedWalk _ _ _ _ (t+2) (t+2) J hExit T
      (computedStateCode r c U L start.val)
      (((List.ofFn word).take (terminalScheduleWordWidth r c U L h)).take (T*W)))
    (h+2) k
    (((List.ofFn word).take (terminalScheduleWordWidth r c U L h)).drop (T*W))
    (((List.ofFn word).drop (terminalScheduleWordWidth r c U L h)).take k) = _
  rw [hoTake, hoDrop, hiTake, hiDrop]
  rw [List.take_of_length_le (by simp only [List.length_ofFn, le_refl])]
  rw [rawJoinedWalk_eq r c U L hr hc htotal start (t+2) (t+2) J hExit T inner.1]
  exact rawTerminalCorrectedCode_eq r c U L hr hc _ (h+2) k inner.2 outer.2

end
end Math115.PhysicalTraceJoin
