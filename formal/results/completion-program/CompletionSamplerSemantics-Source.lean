/-
SPDX-License-Identifier: Apache-2.0
Exact list-program semantics and full finite-word law for lattice completion.
The program computes dilation, precision, word width, and greedy fallback from
coarse encoded margins. No caller-provided table witness is a program input.
Accuracy is stated on its finite typed experiment, avoiding an infinite
MatrixCode Fintype. A composed outer-sampler machine exponent is not asserted.
-/
import Math115.CompletionSamplerProgram
import Math115.DenseLatticeCompletionProvedInputs

namespace Math115.CompletionSamplerSemantics

open OAI.ContingencyTables DensePrograms FirstSuccess
open DenseLatticeCompletion CompletionRetryBudget LatticeCompletionFinite
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

def parameters (d : ℕ) (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ) (h : ℕ) :
    CompletionSamplerProgram.Parameters := ((List.ofFn R, List.ofFn P), (d, h))

theorem prepare_code (d : ℕ) (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ) (h : ℕ) :
    CompletionSamplerProgram.prepare (parameters d R P h) =
      (d^12, ((marginCode (denseRows (d^12) n R),
        marginCode (denseColumns (d^12) m P)), (d, finePrecision h))) := by
  rw [show marginCode (denseRows (d^12) n R) = List.ofFn (fineMargin (d^12) (n + 1) R)
      from optionMargin_code _,
    show marginCode (denseColumns (d^12) m P) = List.ofFn (fineMargin (d^12) (m + 1) P)
      from optionMargin_code _]
  simp only [parameters, CompletionSamplerProgram.prepare, CompletionSamplerProgram.dilateList,
    CompletionSamplerProgram.dilateEntry, List.length_ofFn, List.map_ofFn]
  rfl

theorem wordWidth_code (d : ℕ) (hd : 0 < d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (h : ℕ) :
    CompletionSamplerProgram.wordWidth (parameters d R P h) =
      fineBits d R P (finePrecision h) := by
  unfold CompletionSamplerProgram.wordWidth
  rw [prepare_code]
  exact canonicalBitCount_code _ _ hd (dense_totals (d^12) R P htotal) (finePrecision h)

theorem bitCount_code (d : ℕ) (hd : 0 < d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (h : ℕ) :
    CompletionSamplerProgram.bitCount (parameters d R P h) = completionBits d R P h := by
  unfold CompletionSamplerProgram.bitCount
  rw [wordWidth_code d hd R P htotal h]
  rfl

theorem trial_code (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (h : ℕ)
    (word : Fin (fineBits d R P (finePrecision h)) → Bool) :
    CompletionSamplerProgram.trial
      (CompletionSamplerProgram.prepare (parameters d R P h), List.ofFn word) =
      (CompletionBooleanRetry.tableTrial (d^12) (dilation_positive d hd) R P
        (fineDraw d hd R P htotal (finePrecision h) word)).map (fun X => matrixCode X.val) := by
  rw [prepare_code]
  unfold CompletionSamplerProgram.trial
  rw [fineDraw_matrixCode d hd R P htotal (finePrecision h) word,
    CompletionBooleanRetry.tableTrial_eq]
  exact LatticeCompletionProgram.decode_fineTable _ _ _ _ _

theorem reservedWords_code (d : ℕ) (hd : 0 < d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (h : ℕ)
    (bits : Fin (completionBits d R P h) → Bool) :
    CompletionSamplerProgram.reservedWords (parameters d R P h, List.ofFn bits) =
      List.ofFn (fun i : Fin (retries h) =>
        List.ofFn (CompletionBooleanRetry.wordBankEquiv
          (fineBits d R P (finePrecision h)) (retries h) bits i)) := by
  unfold CompletionSamplerProgram.reservedWords
  rw [wordWidth_code d hd R P htotal h, bitCount_code d hd R P htotal h]
  rw [List.take_of_length_le (by simp only [List.length_ofFn, le_refl])]
  exact wordChunks_ofFn (fineBits_pos d hd R P (finePrecision h)) bits

theorem greedyFallback_code (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) :
    GreedyFeasibleTable.listMatrix (List.ofFn R) (List.ofFn P) =
      matrixCode (GreedyFeasibleTable.table R P htotal).val :=
  GreedyFeasibleTable.listMatrix_ofFn R P

/-- A typed view of the internally computed fallback and complete Boolean draw. -/
def programTable (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (h : ℕ)
    (bits : Fin (completionBits d R P h) → Bool) : Table R P :=
  completionDraw d hd R P htotal (GreedyFeasibleTable.table R P htotal) h bits

/-- Every actual program output is the exact encoded finite-word table,
including first success, all-failed fallback, and a success equal to fallback. -/
theorem draw_code (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (h : ℕ)
    (bits : Fin (completionBits d R P h) → Bool) :
    CompletionSamplerProgram.draw (parameters d R P h, List.ofFn bits) =
      matrixCode (programTable d hd R P htotal h bits).val := by
  unfold CompletionSamplerProgram.draw
  rw [reservedWords_code d (by omega) R P htotal h bits]
  change FirstSuccessProgram.retry CompletionSamplerProgram.trial
    ((CompletionSamplerProgram.prepare (parameters d R P h),
      GreedyFeasibleTable.listMatrix (List.ofFn R) (List.ofFn P)), _) = _
  rw [greedyFallback_code R P htotal, FirstSuccessProgram.retry_ofFn]
  have htrial :
      (fun word : Fin (fineBits d R P (finePrecision h)) → Bool =>
        CompletionSamplerProgram.trial
          (CompletionSamplerProgram.prepare (parameters d R P h), List.ofFn word)) =
      fun word => (CompletionBooleanRetry.tableTrial (d^12) (dilation_positive d hd) R P
        (fineDraw d hd R P htotal (finePrecision h) word)).map (fun X => matrixCode X.val) := by
    funext word
    exact trial_code d hd R P htotal h word
  rw [htrial]
  rw [FirstSuccessProgram.wordRetry_map
    (fun word => CompletionBooleanRetry.tableTrial (d^12) (dilation_positive d hd) R P
      (fineDraw d hd R P htotal (finePrecision h) word))
    (fun X : Table R P => matrixCode X.val) (GreedyFeasibleTable.table R P htotal)]
  unfold programTable completionDraw CompletionBooleanRetry.flatRetry
  rw [CompletionBooleanRetry.retryWords_eq_wordRetry]

/-- The executable program uses only the computed reserved prefix of a longer
word, so a state-independent Boolean allowance can be supplied directly. -/
theorem draw_prefix_code (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (h N : ℕ)
    (hN : completionBits d R P h ≤ N) (bits : Fin N → Bool) :
    CompletionSamplerProgram.draw (parameters d R P h, List.ofFn bits) =
      matrixCode (programTable d hd R P htotal h (prefixWord hN bits)).val := by
  have htake : (List.ofFn bits).take (CompletionSamplerProgram.bitCount (parameters d R P h)) =
      List.ofFn (prefixWord hN bits) := by
    rw [bitCount_code d (by omega) R P htotal h]
    exact take_ofFn_prefix hN bits
  have hreserved :
      CompletionSamplerProgram.reservedWords (parameters d R P h, List.ofFn bits) =
      CompletionSamplerProgram.reservedWords (parameters d R P h, List.ofFn (prefixWord hN bits)) := by
    unfold CompletionSamplerProgram.reservedWords
    rw [htake, bitCount_code d (by omega) R P htotal h]
    rw [List.take_of_length_le (by simp only [List.length_ofFn, le_refl])]
  calc
    _ = CompletionSamplerProgram.draw (parameters d R P h, List.ofFn (prefixWord hN bits)) := by
      unfold CompletionSamplerProgram.draw
      rw [hreserved]
    _ = _ := draw_code d hd R P htotal h (prefixWord hN bits)

theorem padded_programTable_law (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (h N : ℕ)
    (hN : completionBits d R P h ≤ N) :
    mapLaw (uniformLaw (α := Fin N → Bool))
      (fun bits => programTable d hd R P htotal h (prefixWord hN bits)) =
      mapLaw (uniformLaw (α := Fin (completionBits d R P h) → Bool))
        (programTable d hd R P htotal h) :=
  padded_draw_law hN (programTable d hd R P htotal h)

/-- Accuracy of the typed experiment identified pointwise with the polynomial
list program. PL/Cheeger, count comparison, acceptance, and dense-law TV are
all discharged by the imported proofs. -/
theorem programTable_variation (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hdimR : m + 1 ≤ d) (hdimP : n + 1 ≤ d) (hfree : m * n ≤ d - 1)
    (hR : ∀ i, (n + 1) * (3 * d) ≤ R i) (hP : ∀ j, (m + 1) * (3 * d) ≤ P j) (h : ℕ) :
    variation (mapLaw (uniformLaw (α := Fin (completionBits d R P h) → Bool))
      (programTable d hd R P htotal h))
      (LatticeCompletionAccuracy.originalUniform R P (GreedyFeasibleTable.table R P htotal)) ≤
        dyadic h :=
  DenseLatticeCompletionProvedInputs.completionDraw_variation d hd R P htotal hdimR hdimP
    hfree hR hP (GreedyFeasibleTable.table R P htotal) h

theorem padded_programTable_variation (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hdimR : m + 1 ≤ d) (hdimP : n + 1 ≤ d) (hfree : m * n ≤ d - 1)
    (hR : ∀ i, (n + 1) * (3 * d) ≤ R i) (hP : ∀ j, (m + 1) * (3 * d) ≤ P j)
    (h N : ℕ) (hN : completionBits d R P h ≤ N) :
    variation (mapLaw (uniformLaw (α := Fin N → Bool))
      (fun bits => programTable d hd R P htotal h (prefixWord hN bits)))
      (LatticeCompletionAccuracy.originalUniform R P (GreedyFeasibleTable.table R P htotal)) ≤
        dyadic h := by
  rw [padded_programTable_law]
  exact programTable_variation d hd R P htotal hdimR hdimP hfree hR hP h

/-- One contract combines the actual executable matrix output with its
normalized finite table law; no infinite-code-space law instance is needed. -/
theorem draw_semantics (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hdimR : m + 1 ≤ d) (hdimP : n + 1 ≤ d) (hfree : m * n ≤ d - 1)
    (hR : ∀ i, (n + 1) * (3 * d) ≤ R i) (hP : ∀ j, (m + 1) * (3 * d) ≤ P j) (h : ℕ) :
    (∀ bits : Fin (completionBits d R P h) → Bool,
      CompletionSamplerProgram.draw (parameters d R P h, List.ofFn bits) =
        matrixCode (programTable d hd R P htotal h bits).val) ∧
    variation (mapLaw (uniformLaw (α := Fin (completionBits d R P h) → Bool))
      (programTable d hd R P htotal h))
      (LatticeCompletionAccuracy.originalUniform R P (GreedyFeasibleTable.table R P htotal)) ≤
        dyadic h :=
  ⟨draw_code d hd R P htotal h,
    programTable_variation d hd R P htotal hdimR hdimP hfree hR hP h⟩

end
end Math115.CompletionSamplerSemantics
