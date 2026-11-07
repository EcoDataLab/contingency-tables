import ReferenceRuntime.DecoderDegree
import Math115.CompletionSamplerProgram

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds
open ProfilePrograms

set_option maxHeartbeats 1200000

noncomputable section

lemma typed_completionRetries : Typed CompletionSamplerProgram.retriesRealizer 6 := by
  unfold CompletionSamplerProgram.retriesRealizer
  exact typed_composition
    (typed_pair (typed_constant 4)
      (typed_composition (typed_pair typed_identity (typed_constant 2)) typed_add)) typed_multiply

lemma typed_completionPrecision : Typed CompletionSamplerProgram.precisionRealizer 12 := by
  unfold CompletionSamplerProgram.precisionRealizer
  exact typed_composition
    (typed_pair
      (typed_composition (typed_pair typed_identity (typed_constant 2)) typed_add)
      (typed_composition typed_completionRetries Math115.WordCountSeedDegrees.typed_ceilLogTwo_seed)) typed_add

lemma typed_completionSquare : Typed squareNat 6 := by
  unfold squareNat
  exact typed_composition (typed_pair typed_identity typed_identity) typed_multiply

lemma typed_completionFourthPower : Typed fourthPower 36 := by
  unfold fourthPower
  exact typed_congr _ (typed_composition typed_completionSquare typed_completionSquare)

lemma typed_completionPowerTwelve : Typed CompletionSamplerProgram.powerTwelveRealizer 1296 := by
  unfold CompletionSamplerProgram.powerTwelveRealizer
  apply typed_congr
  exact typed_composition typed_completionFourthPower
    (typed_composition (typed_pair typed_completionSquare typed_identity) typed_multiply)

lemma typed_completionDilateEntry : Typed CompletionSamplerProgram.dilateEntryRealizer 36 := by
  unfold CompletionSamplerProgram.dilateEntryRealizer Realizer.fst Realizer.snd
  exact typed_composition
    (typed_pair (typed_composition typed_first typed_first)
      (typed_composition
        (typed_pair typed_second
          (typed_composition
            (typed_pair (typed_constant 2) (typed_composition typed_first typed_second)) typed_multiply)) typed_add)) typed_multiply

lemma typed_completionDilateList : Typed CompletionSamplerProgram.dilateListRealizer 2666 := by
  unfold CompletionSamplerProgram.dilateListRealizer
  exact Math115.DrawDegree.typed_mapWith typed_completionDilateEntry (by decide)

/-- The unchanged dilation and precision preparation is total: no nonempty,
dimension, feasibility, or lower-bound premise is required. -/
theorem typed_completionPrepare : Typed CompletionSamplerProgram.prepareRealizer 3455136 := by
  unfold CompletionSamplerProgram.prepareRealizer Realizer.fst Realizer.snd
  exact typed_pair
    (typed_composition (typed_composition typed_second typed_first) typed_completionPowerTwelve)
    (typed_pair
      (typed_pair
        (typed_composition
          (typed_pair
            (typed_pair
              (typed_composition (typed_composition typed_second typed_first) typed_completionPowerTwelve)
              (typed_composition (typed_composition typed_first typed_second) Math115.WordCountSeedDegrees.typed_listLength_seed))
            (typed_composition typed_first typed_first)) typed_completionDilateList)
        (typed_composition
          (typed_pair
            (typed_pair
              (typed_composition (typed_composition typed_second typed_first) typed_completionPowerTwelve)
              (typed_composition (typed_composition typed_first typed_first) Math115.WordCountSeedDegrees.typed_listLength_seed))
            (typed_composition typed_first typed_second)) typed_completionDilateList))
      (typed_pair (typed_composition typed_second typed_first)
        (typed_composition (typed_composition typed_second typed_second) typed_completionPrecision)))

#check typed_completionPrepare
#print axioms typed_completionPrepare
end
end Math115.ReferenceRuntimeNext
