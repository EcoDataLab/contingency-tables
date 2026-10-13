import ReferenceRuntime.DenseTransitionDegree
import ReferenceRuntime.DependentChunksDegree
import ReferenceRuntime.DenseOffsetDegree

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds DensePrograms
set_option maxHeartbeats 1200000
noncomputable section

lemma typed_trialGrid : Typed trialGridRealizer 237075667532890910857291935297166550826891469991289882826586478084096 := by
  unfold trialGridRealizer
  exact typed_composition
    (typed_composition
      (typed_pair
        (typed_composition typed_first typed_first)
        (typed_composition (typed_pair typed_second typed_trialWalkBits) Math115.ListRepeatDegreeV1.typed_takeFast))
      typed_denseFlatWordWalk) typed_flatToGridData

lemma typed_trialOffsets : Typed trialOffsetsRealizer 1647153166460258930456639782777326749974678940134735338549394209345645163774476288 := by
  unfold trialOffsetsRealizer
  exact typed_composition
    (typed_pair
      (typed_composition (typed_pair typed_trialGrid (typed_composition typed_first typed_second)) typed_offsetLengths)
      (typed_composition (typed_pair typed_second typed_trialWalkBits) Math115.ListRepeatDegreeV1.typed_dropFast))
    typed_dependentChunks

/-- Original full dense trial construction: the actual supplied-word walk,
its dependent offset-word parser and complete offset matrix remain charged. -/
theorem typed_denseTrialCompletion : Typed DensePrograms.trialCompletionRealizer 85251034213171022236299660960537698717406615764205172318917605728234344305272397451247029199219325927424 := by
  unfold DensePrograms.trialCompletionRealizer
  exact typed_pair
    (typed_composition (typed_composition typed_trialGrid typed_first) typed_first)
    (typed_composition (typed_pair typed_trialGrid typed_trialOffsets) typed_offsetMatrix)

#check typed_denseTrialCompletion
#print axioms typed_denseTrialCompletion
end
end Math115.ReferenceRuntimeNext
