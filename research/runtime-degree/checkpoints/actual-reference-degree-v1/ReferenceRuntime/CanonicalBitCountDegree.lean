import ReferenceRuntime.DenseTrialWidthDegree
import InputNormalization.CanonicalDegree
import ResearchBounds.ScalarOutputSizeDegree

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds DensePrograms
set_option maxHeartbeats 1200000
noncomputable section

/-- Exact charged work and encoded output for the original canonical bit-count
realizer on every raw parameter tuple. Eager canonical input preparation,
including its discarded greedy fallback, remains part of the cost. -/
theorem typed_canonicalBitCount : Typed canonicalBitCountRealizer 24105903714603648 := by
  unfold canonicalBitCountRealizer
  exact Math115.ScalarOutputDegree.typed_composition_from_output_size
    (e:=7228) (t:=12052951857301824) (s:=2)
    Math115.InputNormalization.typed_preparedCanonicalParameters
    typed_denseParameterBits (360*(X+3)^2+16)
    Math115.InputNormalization.preparedCanonicalParameters_output_degree
    Math115.InputNormalization.preparedCanonicalParameters_output

#check typed_canonicalBitCount
#print axioms typed_canonicalBitCount
end
end Math115.ReferenceRuntimeNext
