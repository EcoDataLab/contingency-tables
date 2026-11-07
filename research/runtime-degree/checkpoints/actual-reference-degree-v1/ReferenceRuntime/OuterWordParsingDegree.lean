import ReferenceRuntime.DenseTransitionDegree
import UnitRuntime.UnitParsingDegree

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds DensePrograms ProfilePrograms
set_option maxHeartbeats 1200000
noncomputable section

lemma typed_splitProfileWord : Typed splitProfileWordRealizer 8 := by
  unfold splitProfileWordRealizer
  exact typed_pair
    (typed_composition (typed_pair typed_second typed_first) Math115.ListRepeatDegreeV1.typed_takeFast)
    (typed_composition (typed_pair typed_second typed_first) Math115.ListRepeatDegreeV1.typed_dropFast)

lemma splitProfileWord_affine_output : Math115.PrinterRuntimeNext.AffineOutput splitProfileWord := by
  refine ⟨1,2,fun z => ?_⟩
  have h := weight_append (z.2.take z.1) (z.2.drop z.1)
  rw [List.take_append_drop] at h
  have hw := weight_snd z
  simp only [splitProfileWord,weight_prod,one_mul]
  omega

lemma typed_referenceWalkChunks : Typed profileWalkChunksRealizer 74112 := by
  unfold profileWalkChunksRealizer
  exact typed_composition
    (typed_pair Math115.RetryRuntimeNext.typed_actual_profileWordWidth
      (typed_composition (typed_pair typed_second Math115.RetryRuntimeNext.typed_actual_profileWalkWidth)
        Math115.ListRepeatDegreeV1.typed_takeFast)) typed_denseWordChunks

lemma typed_referenceWalkWords : Typed profileWalkWordsRealizer 1259904 := by
  unfold profileWalkWordsRealizer
  exact typed_composition
    (typed_pair (typed_composition (typed_composition typed_first typed_first) typed_second) typed_referenceWalkChunks)
    (Math115.AffineMapWithNext.typed_mapWith_affine typed_splitProfileWord (by decide) splitProfileWord_affine_output)

lemma typed_referenceProfileTerminalWord : Typed profileTerminalWordRealizer 12 := by
  unfold profileTerminalWordRealizer
  exact typed_composition (typed_pair typed_second Math115.RetryRuntimeNext.typed_actual_profileWalkWidth)
    Math115.ListRepeatDegreeV1.typed_dropFast

lemma typed_referenceTerminalWord : Typed LatticeOuterProgram.terminalWordRealizer 96 := by
  unfold LatticeOuterProgram.terminalWordRealizer
  exact typed_composition
    (typed_pair
      (typed_composition Math115.UnitRuntimeNext.typed_unitTrialWordInput typed_referenceProfileTerminalWord)
      (typed_composition (typed_composition typed_first typed_second) typed_second)) Math115.ListRepeatDegreeV1.typed_takeFast

/-- Original reference supplied-word preparation, including separate terminal
precision and width, missing/surplus bits, zero step width and arbitrary tuples. -/
theorem typed_referencePrepareTrial : Typed LatticeOuterProgram.prepareTrialRealizer 1259904 := by
  unfold LatticeOuterProgram.prepareTrialRealizer
  exact typed_pair
    (typed_pair
      (typed_pair
        (typed_composition (typed_composition typed_first typed_first) typed_first)
        (typed_composition Math115.UnitRuntimeNext.typed_unitTrialWordInput typed_referenceWalkWords))
      (typed_composition (typed_composition typed_first typed_second) typed_first)) typed_referenceTerminalWord

#check typed_referencePrepareTrial
#print axioms typed_referencePrepareTrial
end
end Math115.ReferenceRuntimeNext
