/- Exact numerical unit packed-trial certificate assembled only from accepted
original-realizer helpers. All literal inputs, discarded reservations,
accumulators and terminal output weights remain charged. -/
import UnitRuntime.UnitParsingDegree
import UnitRuntime.ProfileEqualityDegree
import UnitRuntime.ProfileValidatorDegree
import RepairRuntime.InverseListDegree
namespace Math115.UnitRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds ProfilePrograms DensePrograms
set_option maxHeartbeats 1600000
noncomputable section

lemma typed_repairInput : Typed repairInput 1 := by
  unfold repairInput
  exact typed_pair (typed_composition typed_first typed_first) typed_second

lemma typed_rawCodeNeighbors : Typed rawCodeNeighborsRealizer 774156 := by
  unfold rawCodeNeighborsRealizer
  exact typed_composition
    (typed_pair
      (typed_composition typed_profileViews typed_codeExchangeList_refined)
      (typed_composition
        (typed_pair
          (typed_composition typed_repairInput Math115.RepairRuntimeNext.typed_forwardRepairList)
          (typed_composition typed_repairInput Math115.RepairRuntimeNext.typed_checkedInverseRepairList))
        Math115.PrinterRuntimeNext.typed_append)) Math115.PrinterRuntimeNext.typed_append

lemma typed_candidateData : Typed candidateDataRealizer 1 := Math115.DrawDegree.typed_candidateData

lemma typed_codeNeighbors : Typed codeNeighborsRealizer 1176650910843823693560 := by
  unfold codeNeighborsRealizer
  exact typed_composition
    (typed_composition (typed_pair typed_identity typed_rawCodeNeighbors)
      (Math115.RepairRuntimeNext.typed_filterWith_output
        (typed_composition typed_candidateData typed_profileTest) (by decide))) typed_profileCodeDedup

lemma typed_codeNeighborProposal : Typed codeNeighborProposalRealizer 14119810930125884322720 := by
  unfold codeNeighborProposalRealizer
  exact typed_composition
    (typed_pair (typed_composition typed_first typed_codeNeighbors) typed_second) typed_listWordChoice

lemma typed_stepCheck : Typed stepCheck 1 := by
  unfold stepCheck
  exact typed_composition (typed_composition typed_first typed_first) typed_first

lemma typed_stepViews : Typed stepViews 1 := by
  unfold stepViews
  exact typed_composition typed_stepCheck typed_profileViews

lemma typed_stepProposal : Typed stepProposalRealizer 14119810930125884322720 := by
  unfold stepProposalRealizer
  exact typed_composition (typed_pair typed_stepCheck (typed_composition typed_second typed_first))
    typed_codeNeighborProposal

/-- Includes the actual unchanged-current-view default for every unsuccessful
or malformed proposal word, rather than assuming a valid neighbor code. -/
lemma typed_stepCandidateViews : Typed stepCandidateViewsRealizer 14119810930125884322720 := by
  unfold stepCandidateViewsRealizer
  exact typed_composition (typed_pair typed_stepViews typed_stepProposal) Math115.DrawDegree.typed_default

lemma typed_actual_unitWalk : Typed Math115.LatticeUnitWalk.unitWalkRealizer 2342307195576722698527375361 :=
  Math115.DrawDegree.typed_unitWalk typed_stepCandidateViews (by decide)

lemma typed_actual_unitTrialState : Typed Math115.LatticeUnitOuter.trialStateRealizer 16753080508727822201384023094010624 := by
  unfold Math115.LatticeUnitOuter.trialStateRealizer
  exact typed_composition
    (typed_pair
      (typed_composition (typed_composition typed_first typed_first) typed_first)
      (typed_composition typed_unitTrialWordInput typed_profileWalkChunks)) typed_actual_unitWalk

/-- The exact named unit-trial field: no supplied work hypothesis, alternate
program, restricted input domain or favorable-output assumption is present. -/
theorem typed_actual_unitPackedTrial :
    Typed Math115.LatticeUnitOuter.packedTrialRealizer 272019144737569436269241336269647035188617216 := by
  unfold Math115.LatticeUnitOuter.packedTrialRealizer
  exact typed_composition
    (typed_pair
      (typed_composition
        (typed_composition typed_actual_unitTrialState Math115.DrawDegree.typed_currentParameters) typed_first)
      (typed_constant ([] : MatrixCode))) typed_outerTrial

end
end Math115.UnitRuntimeNext
