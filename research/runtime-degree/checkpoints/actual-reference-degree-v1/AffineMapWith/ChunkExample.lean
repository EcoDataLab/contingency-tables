import AffineMapWith.Degree
import RetryRuntime.WordChunkDegree
namespace Math115.AffineMapWithNext
open OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds Math115.PrinterRuntimeNext Math115.RetryRuntimeNext
noncomputable section
lemma chunk_affine_output : AffineOutput (fun z : ChunkInput =>
    (z.1.2.drop (z.2*z.1.1)).take z.1.1) := by
  refine ⟨1,0,?_⟩
  rintro ⟨⟨width,bits⟩,index⟩
  have h := chunk_output_weight ((width,bits),index)
  change weight ((bits.drop (index*width)).take width) ≤ weight bits at h
  simp only [one_mul,add_zero,weight_prod]
  exact h.trans (by omega)
/-- The same literal chunk program has a much sharper eager mapWith envelope
once its independently affine sublist output bound is retained. -/
theorem typed_mapWith_chunkProgram : Typed (mapWith chunkProgram) 193 :=
  typed_mapWith_affine typed_chunkProgram (by decide) chunk_affine_output
end
end Math115.AffineMapWithNext
