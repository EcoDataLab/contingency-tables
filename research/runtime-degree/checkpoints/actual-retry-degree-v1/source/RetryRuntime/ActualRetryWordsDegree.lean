import RetryRuntime.WordChunksDegree
import Math115.LatticeOuterProgram

namespace Math115.RetryRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open ProfilePrograms DensePrograms
open Math115.DegreeBounds
noncomputable section

/-- Original program declarations, with exact literal-DAG witness transport. -/
lemma typed_actual_wordChunk : Typed wordChunkRealizer 96 := typed_chunkProgram
lemma typed_actual_completeWordRows : Typed completeWordRowsRealizer 8 := typed_rowProgram

/-- Exact full-import binding: no alternate parser or chunking algorithm. -/
lemma typed_actual_wordChunks : Typed wordChunksRealizer 149008 := typed_chunksProgram

lemma typed_actual_profileWordWidth : Typed profileWordWidthRealizer 1 := by
  unfold profileWordWidthRealizer
  exact typed_composition (typed_pair
    (typed_composition (typed_composition typed_first typed_first) typed_second)
    (typed_composition typed_first typed_second)) typed_add

lemma typed_actual_profileWalkWidth : Typed profileWalkWidthRealizer 6 := by
  unfold profileWalkWidthRealizer
  exact typed_composition (typed_pair
    (typed_composition (typed_composition typed_first typed_first) typed_first)
    typed_actual_profileWordWidth) typed_multiply

lemma typed_actual_attemptWidth : Typed Math115.LatticeOuterProgram.attemptWidthRealizer 6 := by
  unfold Math115.LatticeOuterProgram.attemptWidthRealizer
  exact typed_composition (typed_pair
    (typed_composition (typed_pair (typed_composition typed_first typed_second)
      (typed_constant ([] : List Bool))) typed_actual_profileWalkWidth)
    (typed_composition typed_second typed_second)) typed_add

lemma typed_actual_retryAttemptWidth :
    Typed Math115.LatticeOuterProgram.retryAttemptWidthRealizer 6 := by
  unfold Math115.LatticeOuterProgram.retryAttemptWidthRealizer
  exact typed_composition (typed_composition (typed_composition typed_first typed_first)
    typed_first) typed_actual_attemptWidth

lemma typed_actual_retryBankWidth :
    Typed Math115.LatticeOuterProgram.retryBankWidthRealizer 36 := by
  unfold Math115.LatticeOuterProgram.retryBankWidthRealizer
  exact typed_composition (typed_pair (typed_composition typed_first typed_second)
    typed_actual_retryAttemptWidth) typed_multiply

/-- Charged cost plus encoded output for the EXACT existing supplied-word retry
parser. Arbitrary literal retry data, all natural widths/precisions/margins,
short/surplus words and divisor0 are retained. This conservative composition is
not a bound for evaluating any retry trial or the complete draw. -/
theorem typed_actual_retryWords :
    Typed Math115.LatticeOuterProgram.retryWordsRealizer 42914304 := by
  unfold Math115.LatticeOuterProgram.retryWordsRealizer
  exact typed_composition (typed_pair typed_actual_retryAttemptWidth
    (typed_composition (typed_pair typed_second typed_actual_retryBankWidth) typed_takeFast))
    typed_actual_wordChunks

theorem actual_retryWords_polynomial :
    ∃ p : Polynomial ℕ, p.natDegree ≤ 42914304 ∧
      ∀ z : Math115.LatticeOuterProgram.RetryData,
        Math115.LatticeOuterProgram.retryWordsRealizer.cost z +
          weight (Math115.LatticeOuterProgram.retryWords z) ≤ p.eval (weight z) :=
  typed_actual_retryWords

lemma actual_retryWords_output_weight (z : Math115.LatticeOuterProgram.RetryData) :
    weight (Math115.LatticeOuterProgram.retryWords z) ≤
      (weight (Math115.LatticeOuterProgram.retryAttemptWidth z,
        z.2.take (Math115.LatticeOuterProgram.retryBankWidth z))+1)^2 :=
  chunks_output_weight _
lemma actual_retryWords_length_le_attempts (z : Math115.LatticeOuterProgram.RetryData) :
    (Math115.LatticeOuterProgram.retryWords z).length ≤ z.1.2 := by
  unfold Math115.LatticeOuterProgram.retryWords wordChunks completeWordRows
  simp only [List.length_map,List.length_range,List.length_take]
  unfold Math115.LatticeOuterProgram.retryBankWidth
  by_cases h : Math115.LatticeOuterProgram.retryAttemptWidth z = 0
  · simp [h]
  · have hw : 0 < Math115.LatticeOuterProgram.retryAttemptWidth z := by omega
    exact (Nat.div_le_div_right (min_le_left _ _)).trans
      (by rw [Nat.mul_div_cancel _ hw])

lemma actual_retryWords_empty_of_short (z : Math115.LatticeOuterProgram.RetryData)
    (h : z.2.length < Math115.LatticeOuterProgram.retryAttemptWidth z) :
    Math115.LatticeOuterProgram.retryWords z = [] := by
  have hl : (z.2.take (Math115.LatticeOuterProgram.retryBankWidth z)).length <
      Math115.LatticeOuterProgram.retryAttemptWidth z := by
    simp only [List.length_take]
    exact (min_le_right _ _).trans_lt h
  simp only [Math115.LatticeOuterProgram.retryWords,wordChunks,completeWordRows,
    Nat.div_eq_of_lt hl,List.range_zero,List.map_nil]

end
end Math115.RetryRuntimeNext
