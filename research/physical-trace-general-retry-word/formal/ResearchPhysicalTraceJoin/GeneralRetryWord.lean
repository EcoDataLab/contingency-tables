/-
SPDX-License-Identifier: Apache-2.0
One flat finite Boolean word for independent corrected trials and fallback.
This is a typed map and its exact law, not an encoded or charged machine.
The corrected one-trial map and all its option failures are unchanged.
-/
import ResearchPhysicalTraceJoin.GeneralCorrectedRetry
import Math115.CompletionBooleanRetry

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open FirstSuccess ResidualMixture FairBits
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

/-- Exactly R disjoint copies of the complete scheduled trial and coin. -/
def terminalCorrectedRetryWordWidth (h k R : ℕ) : ℕ :=
  R * terminalCorrectedWordWidth r c U L h k

theorem terminalCorrectedRetryWordWidth_eq (h k R : ℕ) :
    terminalCorrectedRetryWordWidth r c U L h k R =
      R * (terminalScheduleWordWidth r c U L h + k) := rfl

/-- First success, with the supplied ordinary-table fallback after R
failures. In particular, a successful value equal to fallback is accepted. -/
def terminalCorrectedRetryWord (start : DefectVertices r c U L) (h k : ℕ)
    (fallback : Table r c) (R : ℕ)
    (word : Fin (terminalCorrectedRetryWordWidth r c U L h k R) → Bool) : Table r c :=
  Math115.CompletionBooleanRetry.flatRetry
    (terminalCorrectedWord r c U L hr hc start h k) fallback R word

/-- The source is split bijectively into R complete trial words. The
checked retry recursion advances only on none, never on table equality. -/
theorem terminalCorrectedRetryWord_eq_retryWords
    (start : DefectVertices r c U L) (h k : ℕ) (fallback : Table r c) (R : ℕ)
    (word : Fin (terminalCorrectedRetryWordWidth r c U L h k R) → Bool) :
    terminalCorrectedRetryWord r c U L hr hc start h k fallback R word =
      Math115.CompletionBooleanRetry.retryWords
        (terminalCorrectedWord r c U L hr hc start h k) fallback R
        (Math115.CompletionBooleanRetry.wordBankEquiv
          (terminalCorrectedWordWidth r c U L h k) R word) := rfl

/-- Zero attempts reserve zero bits and return the fallback even when the
one-trial word itself has positive width. -/
theorem terminalCorrectedRetryWord_zero (start : DefectVertices r c U L)
    (h k : ℕ) (fallback : Table r c)
    (word : Fin (terminalCorrectedRetryWordWidth r c U L h k 0) → Bool) :
    terminalCorrectedRetryWord r c U L hr hc start h k fallback 0 word = fallback := rfl

def terminalCorrectedRetryWordLaw (start : DefectVertices r c U L) (h k : ℕ)
    (fallback : Table r c) (R : ℕ) : RationalLaw (Table r c) :=
  mapLaw (uniformLaw
    (α := Fin (terminalCorrectedRetryWordWidth r c U L h k R) → Bool))
    (terminalCorrectedRetryWord r c U L hr hc start h k fallback R)

/-- Uniformity of the entire flat word supplies fresh independent trial
blocks. All padding and correction failures remain none; nothing is
conditioned on success, and the final fallback is the original supplied one. -/
theorem terminalCorrectedRetryWordLaw_eq (start : DefectVertices r c U L)
    (h k : ℕ) (fallback : Table r c) (R : ℕ) :
    terminalCorrectedRetryWordLaw r c U L hr hc start h k fallback R =
      terminalCorrectedRetryLaw r c U L hr hc start h k fallback R := by
  exact Math115.CompletionBooleanRetry.flatRetry_law
    (terminalCorrectedWord r c U L hr hc start h k) id fallback R

/-- The existing corrected-trial bound applies to the actual flat typed
word, including R=0. Initialization and encoded running time remain separate. -/
theorem terminalCorrectedRetryWord_accuracy_of_success
    [Nonempty (DefectVertices r c U L)]
    (htotal : (∑ i, r i) = ∑ j, c j) (hU : 2 ≤ U) (hL : 7 ≤ L)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (hrpos : ∀ i, 0 < r i) (hcpos : ∀ j, 0 < c j)
    (start : DefectVertices r c U L) (h k : ℕ) (fallback : Table r c) (R : ℕ)
    (s : ℚ) (hs : s ≤ 1 - (terminalIdealCorrectedLaw r c U L).mass none) :
    letI : Nonempty (Table r c) := ⟨fallback⟩
    variation (terminalCorrectedRetryWordLaw r c U L hr hc start h k fallback R)
      (uniformLaw (α := Table r c)) ≤
        (1 - s)^R + (R : ℚ) * (dyadic h + dyadic k) := by
  letI : Nonempty (Table r c) := ⟨fallback⟩
  rw [terminalCorrectedRetryWordLaw_eq]
  exact terminalCorrectedRetry_accuracy_of_success r c U L hr hc
    htotal hU hL hp hrpos hcpos start h k fallback R s hs

end
end Math115.PhysicalTraceJoin
