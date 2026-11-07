import ReferenceRuntime.DenseAcceptanceDegree
import AffineMapWith.Degree

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds DensePrograms
set_option maxHeartbeats 1200000
noncomputable section

lemma typed_chunkStart : Typed chunkStartRealizer 24 := by
  unfold chunkStartRealizer
  exact typed_composition
    (typed_composition
      (typed_pair (typed_composition typed_first typed_first) typed_second)
      Math115.ListRepeatDegreeV1.typed_takeFast) Math115.WordCountSeedDegrees.typed_listSum_seed

lemma typed_dependentChunk : Typed dependentChunkRealizer 384 := by
  unfold dependentChunkRealizer
  exact typed_composition
    (typed_pair
      (typed_composition (typed_pair (typed_composition typed_first typed_second) typed_chunkStart)
        Math115.ListRepeatDegreeV1.typed_dropFast)
      (typed_composition (typed_pair (typed_composition typed_first typed_first) typed_second)
        (Math115.DrawRuntimeNext.typed_getDFast 0))) Math115.ListRepeatDegreeV1.typed_takeFast

lemma dependentChunk_affine_output : Math115.PrinterRuntimeNext.AffineOutput dependentChunk := by
  refine ⟨1,0,fun z => ?_⟩
  simp only [one_mul,add_zero]
  unfold dependentChunk
  exact (weight_sublist ((List.take_sublist _ _).trans (List.drop_sublist _ _))).trans
    ((weight_snd z.1).trans (weight_fst z))

lemma typed_chunkIndices : Typed chunkIndicesRealizer 3 := by
  unfold chunkIndicesRealizer
  apply Math115.DrawRuntimeNext.typed_boundedRange (e:=2) (d:=1)
    (typed_composition typed_first Math115.WordCountSeedDegrees.typed_listLength_seed) X (by simp)
  intro z
  simpa only [Function.comp_apply,eval_X] using (list_length_le_weight z.1).trans (weight_fst z)

/-- Exact eager dependent-width parser. Each callback returns a sublist of
the actual word, even for zero or enormous encoded widths and empty input. -/
theorem typed_dependentChunks : Typed dependentChunksRealizer 2307 := by
  unfold dependentChunksRealizer
  exact typed_composition (typed_pair typed_identity typed_chunkIndices)
    (Math115.AffineMapWithNext.typed_mapWith_affine typed_dependentChunk (by decide) dependentChunk_affine_output)

#check typed_dependentChunks
#print axioms typed_dependentChunks
end
end Math115.ReferenceRuntimeNext
