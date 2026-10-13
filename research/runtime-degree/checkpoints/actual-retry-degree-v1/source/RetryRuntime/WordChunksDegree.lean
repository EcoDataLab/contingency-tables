import RetryRuntime.WordChunkDegree
import RetryRuntime.MapWithDegree
import DivisionRuntime.Degree
namespace Math115.RetryRuntimeNext
open OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds Math115.PrinterRuntimeNext
noncomputable section
/-- Literal completeWordRows DAG, retaining actual quotient including divisor0. -/
def rowProgram : Realizer (fun z : ℕ × List Bool => List.range (z.2.length/z.1)) :=
  composition (composition (pair (composition second listLength) first) quotient) range
lemma typed_rowProgram : Typed rowProgram 8 := by
  have hq : Typed (composition
      (pair (composition (second (A:=ℕ) (B:=List Bool)) listLength) first) quotient) 8 :=
    typed_composition (typed_pair
      (typed_composition typed_second (typed_listLength_seed (A:=Bool))) typed_first)
      Math115.DivisionRuntimeNext.typed_quotient
  unfold rowProgram
  exact typed_boundedRange (e:=8) (d:=1) hq X (by simp) (fun z => by
    simp only [eval_X,Function.comp_apply]
    exact (Nat.div_le_self _ _).trans ((list_length_le_weight _).trans (weight_snd z)))

/-- Literal wordChunks DAG; the eager map constructs every complete chunk. -/
def chunksProgram : Realizer (fun z : ℕ × List Bool =>
    (List.range (z.2.length/z.1)).map (fun i => (z.2.drop (i*z.1)).take z.1)) :=
  composition (pair identity rowProgram) (mapWith chunkProgram)
theorem typed_chunksProgram : Typed chunksProgram 149008 := by
  have hm : Typed (mapWith chunkProgram) 18626 :=
    typed_mapWith typed_chunkProgram (by decide)
  unfold chunksProgram
  exact typed_composition (typed_pair typed_identity typed_rowProgram) hm

lemma chunks_output_weight (z : ℕ × List Bool) :
    weight ((List.range (z.2.length/z.1)).map
      (fun i => (z.2.drop (i*z.1)).take z.1)) ≤ (weight z+1)^2 := by
  have hb := weight_map_bound (as:=List.range (z.2.length/z.1))
    (f:=fun i => (z.2.drop (i*z.1)).take z.1) (N:=weight z.2) (by
      intro i hi
      exact chunk_output_weight (z,i))
  have hr : (List.range (z.2.length/z.1)).length ≤ z.2.length := by
    simp only [List.length_range]; exact Nat.div_le_self _ _
  have hl := list_length_le_weight z.2
  have hw : weight z.2 ≤ weight z := by rw [weight_prod]; omega
  have hm := Nat.mul_le_mul hr (show weight z.2+1 ≤ weight z+1 by omega)
  nlinarith
end
end Math115.RetryRuntimeNext
