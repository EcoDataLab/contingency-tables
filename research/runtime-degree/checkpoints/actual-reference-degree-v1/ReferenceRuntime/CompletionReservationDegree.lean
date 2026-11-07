import ReferenceRuntime.CanonicalBitCountDegree
import ReferenceRuntime.DenseTransitionDegree

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds DensePrograms
set_option maxHeartbeats 1200000
noncomputable section

lemma typed_completionWordWidth : Typed CompletionSamplerProgram.wordWidthRealizer 83289175736860789936128 := by
  unfold CompletionSamplerProgram.wordWidthRealizer
  exact typed_composition (typed_composition typed_completionPrepare typed_second) typed_canonicalBitCount

lemma typed_completionBitCount : Typed CompletionSamplerProgram.bitCountRealizer 499735054421164739616768 := by
  unfold CompletionSamplerProgram.bitCountRealizer Realizer.snd
  exact typed_composition
    (typed_pair (typed_composition (typed_composition typed_second typed_second) typed_completionRetries)
      typed_completionWordWidth) typed_multiply

/-- The exact reserved prefix parser computes the original retry budget and
width, truncates the actual supplied word, and constructs only complete chunks. -/
theorem typed_completionReservedWords : Typed CompletionSamplerProgram.reservedWordsRealizer 6172727392210226863746318336 := by
  unfold CompletionSamplerProgram.reservedWordsRealizer
  exact typed_composition
    (typed_pair
      (typed_composition typed_first typed_completionWordWidth)
      (typed_composition
        (typed_pair typed_second (typed_composition typed_first typed_completionBitCount))
        Math115.ListRepeatDegreeV1.typed_takeFast)) typed_denseWordChunks

#check typed_completionWordWidth
#print axioms typed_completionWordWidth
#check typed_completionReservedWords
#print axioms typed_completionReservedWords
end
end Math115.ReferenceRuntimeNext
