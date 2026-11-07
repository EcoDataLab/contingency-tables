/-
SPDX-License-Identifier: Apache-2.0
Ordinary whole-list sampler composition. The computed dispatcher, searched
initialization, actual corrected trial, fixed-word retry, legacy fallback
and literal zero restoration agree pointwise with the proved typed sampler.
No encoded realizer or charged-time theorem is asserted here.
-/
import ResearchPhysicalTraceJoin.GeneralTrialCode
import ResearchPhysicalTraceJoin.GeneralFallbackCode
import ResearchPhysicalTraceJoin.GeneralHybridSampler
import OAI.Combinatorics.ContingencyTables.Machines.BooleanChunkProgram
import OAI.Combinatorics.ContingencyTables.Machines.FirstSuccessProgram

set_option maxHeartbeats 1200000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms FirstSuccess ResidualMixture CompletionCounts
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalComputedProposal Math115.CompletionRetryBudget
open scoped BigOperators

/-- Consecutive complete trial blocks, first success, then the literal
fallback on exhaustion. Surplus input bits cannot add extra attempts. -/
def rawCorrectedRetryCode (rs cs : List ℕ) (U L : ℕ) (start : List ℕ × List ℕ)
    (h k : ℕ) (fallback : MatrixCode) (R : ℕ) (word : List Bool) : MatrixCode :=
  let q := rawTerminalScheduleWordWidth rs cs U L h + k
  FirstSuccessProgram.retry
    (fun z : Unit × List Bool => rawCorrectedTrial rs cs U L start h k z.2)
    (((),fallback), wordChunks (q, word.take (R*q)))

/-- Search supplies the actual start. Every independent retry starts from
that same state; the computed greedy table is the all-failed fallback. -/
def rawPositiveReferenceWordCode (xs ys : List ℕ)
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (t : ℕ) (word : List Bool) : MatrixCode :=
  let reduced := match positiveTraceInitializationCode xs ys htotal with
    | none => positiveTraceFallbackCode xs ys
    | some start => rawCorrectedRetryCode (positiveMargins xs) (positiveMargins ys)
        (positiveTraceCutoff xs ys) 7 start
        (rawPositiveOuterPrecision xs ys t) (rawPositiveOuterPrecision xs ys t)
        (positiveTraceFallbackCode xs ys) (rawPositiveOuterAttempts xs ys t) word
  restoreZeroMarginMatrix xs ys reduced

/-- Width is computed from the branch and input lists alone. -/
def rawHybridWordWidth (xs ys : List ℕ) (t : ℕ) : ℕ :=
  if positiveTraceBranch xs ys = .deterministic then 0
  else if positiveTraceBranch xs ys = .reference then rawPositiveWordWidth xs ys t
  else rawPositiveLegacyWordWidth xs ys t

/-- Total ordinary list program. Equal totals are checked internally; the
resulting proof is erased by execution. Unequal totals return the empty code. -/
def rawHybridSamplerCode (xs ys : List ℕ) (t : ℕ) (word : List Bool) : MatrixCode :=
  if hs : xs.sum = ys.sum then
    have htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j := by
      simpa only [← List.sum_ofFn, ofFn_listMargin] using hs
    if positiveTraceBranch xs ys = .deterministic then
      rawPositiveDeterministicWordCode xs ys word
    else if positiveTraceBranch xs ys = .reference then
      rawPositiveReferenceWordCode xs ys htotal t word
    else rawPositiveLegacyWordCode xs ys t word
  else []

open scoped Classical
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U,List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U,List.ofFn c)).length)

/-- The existing chunk and first-success correspondence applies directly
to the actual trial. Its positive-width premise is explicit. -/
theorem rawCorrectedRetryCode_eq
    (htotal : (∑ i, r i) = ∑ j, c j)
    (start : DefectVertices r c U L) (h k : ℕ) (fallback : Table r c) (R : ℕ)
    (hq : 0 < terminalCorrectedWordWidth r c U L h k)
    (word : Fin (terminalCorrectedRetryWordWidth r c U L h k R) → Bool) :
    rawCorrectedRetryCode (List.ofFn r) (List.ofFn c) U L
      (computedStateCode r c U L start.val) h k (matrixCode fallback.val) R (List.ofFn word) =
      matrixCode (terminalCorrectedRetryWord r c U L hr hc start h k fallback R word).val := by
  unfold rawCorrectedRetryCode
  rw [rawTerminalScheduleWordWidth_eq]
  have htake : (List.ofFn word).take (R * (terminalScheduleWordWidth r c U L h + k)) =
      List.ofFn word := by
    apply List.take_of_length_le
    simp only [List.length_ofFn, terminalCorrectedRetryWordWidth, terminalCorrectedWordWidth,
      le_refl]
  rw [htake, wordChunks_ofFn hq word, FirstSuccessProgram.retry_ofFn]
  have htrial :
      (fun bits : Fin (terminalCorrectedWordWidth r c U L h k) → Bool =>
        rawCorrectedTrial (List.ofFn r) (List.ofFn c) U L
          (computedStateCode r c U L start.val) h k (List.ofFn bits)) =
      fun bits => (terminalCorrectedWord r c U L hr hc start h k bits).map
        (fun X => matrixCode X.val) := by
    funext bits
    exact rawCorrectedTrial_eq r c U L hr hc htotal start h k bits
  rw [htrial]
  rw [FirstSuccessProgram.wordRetry_map
    (terminalCorrectedWord r c U L hr hc start h k)
    (fun X : Table r c => matrixCode X.val) fallback]
  unfold terminalCorrectedRetryWord Math115.CompletionBooleanRetry.flatRetry
  rw [Math115.CompletionBooleanRetry.retryWords_eq_wordRetry]
  rfl

variable (xs ys : List ℕ)

/-- The searched start and all retry parameters are computed internally.
The pointwise statement includes first success and all-failed fallback. -/
theorem rawPositiveReferenceWordCode_eq
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) (t : ℕ)
    (word : Fin (positiveReferenceWordWidth xs ys t) → Bool) :
    rawPositiveReferenceWordCode xs ys htotal t (List.ofFn word) =
      matrixCode (positiveReferenceWord xs ys htotal hb t word).val := by
  unfold rawPositiveReferenceWordCode
  rw [positiveTraceInitializationCode_initialStart xs ys htotal hb]
  simp only [rawPositiveOuterPrecision_eq, rawPositiveOuterAttempts_eq]
  rw [positiveTraceFallbackCode_code xs ys htotal]
  have hq := rawPositiveTrialWordWidth_positive xs ys t
  rw [rawPositiveTrialWordWidth_eq] at hq
  have he := rawCorrectedRetryCode_eq (filteredMargin xs) (filteredMargin ys)
    (positiveTraceCutoff xs ys) 7
    (positiveTraceReference_conditions xs ys hb).2.2.2.1
    (positiveTraceReference_conditions xs ys hb).2.2.2.2
    (filtered_totals_equal xs ys htotal) (positiveTraceInitialStart xs ys htotal hb)
    (positiveTraceLinearPrecision xs ys t) (positiveTraceLinearPrecision xs ys t)
    (positiveTraceFallback xs ys htotal) (positiveTraceLinearAttempts xs ys t) hq word
  simp only [ofFn_filteredMargin] at he
  rw [he]
  exact restoreZeroMarginMatrix_code xs ys _

/-- The ordinary dispatcher reserves exactly the width of the selected
typed backend, including the zero-bit deterministic branch. -/
theorem rawHybridWordWidth_eq
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) (t : ℕ) :
    rawHybridWordWidth xs ys t = (hybridSampler xs ys htotal t).1 := by
  by_cases hd : positiveTraceBranch xs ys = .deterministic
  · rw [hybridSampler_deterministic xs ys htotal hd]
    simp only [rawHybridWordWidth, if_pos hd]
  by_cases hb : positiveTraceBranch xs ys = .reference
  · rw [hybridSampler_reference xs ys htotal hb]
    simp only [rawHybridWordWidth, if_neg hd, if_pos hb, rawPositiveWordWidth_eq]
  · rw [hybridSampler_legacy xs ys htotal hd hb]
    simp only [rawHybridWordWidth, if_neg hd, if_neg hb, rawPositiveLegacyWordWidth_eq]

/-- Transport the entire reserved-width sampler together, so no dependent
word is rewritten across just the width projection. -/
private theorem bundledCode_congr {A : Type*} (encode : A → MatrixCode)
    (program : List Bool → MatrixCode)
    {s s' : (q : ℕ) × ((Fin q → Bool) → A)} (he : s = s')
    (hcode : ∀ word : Fin s'.1 → Bool, program (List.ofFn word) = encode (s'.2 word)) :
    ∀ word : Fin s.1 → Bool, program (List.ofFn word) = encode (s.2 word) := by
  cases he
  exact hcode

/-- Complete pointwise correspondence on every equal-total input, including
zero margins, empty lists, t=0 and all computed branches. The ordinary
function takes only lists and bits; no semantic table is supplied. -/
theorem rawHybridSamplerCode_eq
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) (t : ℕ)
    (word : Fin (hybridSampler xs ys htotal t).1 → Bool) :
    rawHybridSamplerCode xs ys t (List.ofFn word) =
      matrixCode ((hybridSampler xs ys htotal t).2 word).val := by
  have hs : xs.sum = ys.sum := by
    simpa only [← List.sum_ofFn, ofFn_listMargin] using htotal
  unfold rawHybridSamplerCode
  rw [dif_pos hs]
  by_cases hd : positiveTraceBranch xs ys = .deterministic
  · rw [if_pos hd]
    exact bundledCode_congr (fun X : Table (listMargin xs) (listMargin ys) => matrixCode X.val)
      (rawPositiveDeterministicWordCode xs ys)
      (hybridSampler_deterministic xs ys htotal hd t)
      (fun bits => rawPositiveDeterministicWordCode_eq xs ys htotal bits) word
  rw [if_neg hd]
  by_cases hb : positiveTraceBranch xs ys = .reference
  · rw [if_pos hb]
    exact bundledCode_congr (fun X : Table (listMargin xs) (listMargin ys) => matrixCode X.val)
      (rawPositiveReferenceWordCode xs ys htotal t)
      (hybridSampler_reference xs ys htotal hb t)
      (fun bits => rawPositiveReferenceWordCode_eq xs ys htotal hb t bits) word
  · rw [if_neg hb]
    exact bundledCode_congr (fun X : Table (listMargin xs) (listMargin ys) => matrixCode X.val)
      (rawPositiveLegacyWordCode xs ys t)
      (hybridSampler_legacy xs ys htotal hd hb t)
      (fun bits => rawPositiveLegacyWordCode_eq xs ys htotal t bits) word

end
end Math115.PhysicalTraceJoin
