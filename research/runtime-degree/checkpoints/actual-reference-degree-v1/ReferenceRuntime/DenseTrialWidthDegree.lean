import ReferenceRuntime.DenseWidthCoreDegree

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds DensePrograms ProfilePrograms
set_option maxHeartbeats 1200000
noncomputable section

lemma typed_denseFifthPower : Typed fifthPower 216 := by
  unfold fifthPower
  exact typed_congr _ (typed_composition (typed_pair typed_completionFourthPower typed_identity) typed_multiply)

lemma typed_denseFiftiethPower : Typed fiftiethPower 279936 := by
  unfold fiftiethPower
  exact typed_congr _ (typed_composition (typed_composition typed_denseFifthPower typed_completionSquare) typed_denseFifthPower)

lemma typed_denseWidth : Typed denseWidthRealizer 1296 := by
  unfold denseWidthRealizer
  exact typed_composition
    (typed_pair
      (typed_composition (typed_composition (typed_pair (typed_constant 8) typed_identity) typed_multiply)
        Math115.WordCountSeedDegrees.typed_ceilLogTwo_seed)
      (typed_composition (typed_pair (typed_constant 8) typed_denseFifthPower) typed_multiply)) typed_add

lemma typed_trialWalkBits : Typed trialWalkBitsRealizer 10077696 := by
  unfold trialWalkBitsRealizer
  apply typed_congr
  exact typed_composition
    (typed_pair
      (typed_composition
        (typed_pair
          (typed_composition (typed_composition (typed_composition typed_first typed_first) typed_second)
            typed_denseFiftiethPower)
          (typed_composition (typed_composition (typed_composition typed_first typed_second) typed_successor)
            typed_completionSquare)) typed_multiply)
      (typed_composition (typed_composition (typed_composition typed_first typed_first) typed_second)
        typed_denseWidth)) typed_multiply

/-- Width computation includes the original flat-to-grid conversion and the
full offset-length map, in addition to the original scalar walk budget. -/
theorem typed_denseTrialWidth : Typed trialWidthRealizer 2008825309550304 := by
  unfold trialWidthRealizer
  exact typed_composition
    (typed_pair
      (typed_composition (typed_pair typed_identity (typed_constant [])) typed_trialWalkBits)
      (typed_composition
        (typed_composition
          (typed_pair (typed_composition typed_first typed_flatToGridData) typed_second) typed_offsetLengths)
        Math115.WordCountSeedDegrees.typed_listSum_seed)) typed_add

/-- The exact dense reserved-width circuit. Its large numeric iteration
budget is computed with binary arithmetic; no unary loop is substituted. -/
theorem typed_denseParameterBits : Typed denseParameterBitsRealizer 12052951857301824 := by
  unfold denseParameterBitsRealizer
  exact typed_composition
    (typed_pair
      (typed_composition
        (typed_pair
          (typed_composition (typed_composition typed_first typed_second) typed_completionFourthPower)
          (typed_composition typed_second typed_successor)) typed_multiply)
      typed_denseTrialWidth) typed_multiply

#check typed_denseTrialWidth
#print axioms typed_denseTrialWidth
#check typed_denseParameterBits
#print axioms typed_denseParameterBits
end
end Math115.ReferenceRuntimeNext
