import RetryRuntime.ListRepeatDegree
namespace Math115.RetryRuntimeNext
open OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds
noncomputable section
abbrev ChunkInput := (ℕ × List Bool) × ℕ
/-- Literal wordChunk DAG from pinned BooleanChunkProgram. The complete original
module is not imported in this thin local helper; the full-import binding is separate. -/
def chunkProgram : Realizer (fun z : ChunkInput =>
    (z.1.2.drop (z.2*z.1.1)).take z.1.1) :=
  composition (pair
    (composition (pair (composition first second)
      (composition (pair second (composition first first)) multiply)) dropFast)
    (composition first first)) takeFast
/-- Charges exact multiplication, bounded list drop/take and encoded output. -/
theorem typed_chunkProgram : Typed chunkProgram 96 := by
  unfold chunkProgram
  apply typed_composition (e:=12) (t:=8) _ typed_takeFast
  apply typed_pair (e:=12) (t:=1)
  · apply typed_composition (e:=6) (t:=2) _ typed_dropFast
    apply typed_pair (e:=1) (t:=6)
    · exact typed_composition typed_first typed_second
    · exact typed_composition (typed_pair typed_second
        (typed_composition typed_first typed_first)) typed_multiply
  · exact typed_composition typed_first typed_first
lemma chunk_sublist (z : ChunkInput) :
    ((z.1.2.drop (z.2*z.1.1)).take z.1.1).Sublist z.1.2 :=
  (List.take_sublist _ _).trans (List.drop_sublist _ _)
lemma chunk_output_weight (z : ChunkInput) :
    weight ((z.1.2.drop (z.2*z.1.1)).take z.1.1) ≤ weight z.1.2 :=
  weight_sublist (chunk_sublist z)
lemma complete_rows_bound (width : ℕ) (bits : List Bool) :
    bits.length / width ≤ weight (width,bits) :=
  (Nat.div_le_self _ _).trans ((list_length_le_weight _).trans (by rw [weight_prod]; omega))
lemma supplied_prefix_bound (width bank : ℕ) (bits : List Bool) :
    (bits.take bank).length / width ≤ bits.length :=
  (Nat.div_le_self _ _).trans (by simp only [List.length_take]; exact min_le_right _ _)
lemma zero_width_rows (bits : List Bool) : List.range (bits.length / 0) = [] := by simp
end
end Math115.RetryRuntimeNext
