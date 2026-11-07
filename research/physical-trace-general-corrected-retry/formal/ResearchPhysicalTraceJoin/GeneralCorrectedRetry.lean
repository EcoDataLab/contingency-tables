/-
SPDX-License-Identifier: Apache-2.0
Fresh independent retries of the actual corrected one-trial law, with a
supplied defect start and feasible fallback. No initializer, encoded retry
word, other shape branch, or running-time bound is constructed here.
-/
import ResearchPhysicalTraceJoin.GeneralCorrectedWord

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open FirstSuccess ResidualMixture FairBits
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalStationarySuccess Math115.CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hrLarge : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hcLarge : 0 < (largeIndices (U, List.ofFn c)).length)

/-- Each retry uses an independent complete corrected trial law. -/
def terminalCorrectedRetryLaw (start : DefectVertices r c U L) (h k : ℕ)
    (fallback : Table r c) (R : ℕ) : RationalLaw (Table r c) :=
  retryLaw (terminalCorrectedWordLaw r c U L hrLarge hcLarge start h k) id fallback R

/-- A helper exposing a proved lower bound on IDEAL success. Approximation
of entire actual trials is discharged by the scheduled word theorem. -/
theorem terminalCorrectedRetry_accuracy_of_success [Nonempty (DefectVertices r c U L)]
    (htotal : (∑ i, r i) = ∑ j, c j) (hU : 2 ≤ U) (hL : 7 ≤ L)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (start : DefectVertices r c U L) (h k : ℕ) (fallback : Table r c) (R : ℕ)
    (s : ℚ) (hs : s ≤ 1 - (terminalIdealCorrectedLaw r c U L).mass none) :
    letI : Nonempty (Table r c) := ⟨fallback⟩
    variation (terminalCorrectedRetryLaw r c U L hrLarge hcLarge start h k fallback R)
      (uniformLaw (α := Table r c)) ≤
        (1 - s)^R + (R : ℚ) * (dyadic h + dyadic k) := by
  letI : Nonempty (Table r c) := ⟨fallback⟩
  have hequal (X : Table r c) :
      successMass (terminalIdealCorrectedLaw r c U L) id X =
        (inverseSupportAllowance r c U : ℚ) / Fintype.card (DefectJoint r c U L) := by
    simpa only [terminalIdealCorrectedLaw, successMass, id_eq, Option.some.injEq,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] using
      terminalCorrected_mass r c U L (by omega) hr hc X
  have hf : failureMass (terminalIdealCorrectedLaw r c U L) id =
      (terminalIdealCorrectedLaw r c U L).mass none := by simp [failureMass]
  exact approximate_retry_variation_of_success
    (terminalCorrectedWordLaw r c U L hrLarge hcLarge start h k)
    (terminalIdealCorrectedLaw r c U L) id _ hequal fallback R
    (dyadic h + dyadic k) s
    (terminalCorrectedWord_accuracy r c U L hrLarge hcLarge htotal hU hL hp start h k)
    (by rwa [hf])

local notation "dimension" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "cutoff" => 11 * dimension * (m + n - 2)
local notation "p" => Fintype.card (Cells (firstPaperSmall r c cutoff))

/-- At the actual sharper scales the success allowance is derived from the
actual inverse count and padding count. No desired error or success premise
is supplied. The only fallback is an actual ordinary table. -/
theorem actualShape_terminalCorrectedRetry_accuracy
    (hrLarge : 0 < (largeIndices (cutoff, List.ofFn r)).length)
    (hcLarge : 0 < (largeIndices (cutoff, List.ofFn c)).length)
    (hm : 2 ≤ m) (hn : 2 ≤ n)
    (htotal : (∑ i, r i) = ∑ j, c j)
    (hp : 2 ≤ p) (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (start : DefectVertices r c cutoff 7) (h k : ℕ) (fallback : Table r c) (R : ℕ) :
    letI : Nonempty (Table r c) := ⟨fallback⟩
    variation (terminalCorrectedRetryLaw r c cutoff 7 hrLarge hcLarge start h k fallback R)
      (uniformLaw (α := Table r c)) ≤
        (1 - (inverseSupportAllowance r c cutoff : ℚ) /
          ((2 * (p * (p - 1)) : ℕ) : ℚ))^R + (R : ℚ) * (dyadic h + dyadic k) := by
  letI : Nonempty (Table r c) := ⟨fallback⟩
  letI : Nonempty (DefectVertices r c cutoff 7) := ⟨start⟩
  have hd : 11 ≤ dimension := Math115.PhysicalRepairRefinement.dimension_at_least_eleven
  have hU : 2 ≤ cutoff := by
    have hmul := Nat.mul_le_mul (show 1 ≤ 11 * dimension by omega)
      (show 2 ≤ m + n - 2 by omega)
    simpa only [one_mul] using hmul
  have hs : (inverseSupportAllowance r c cutoff : ℚ) /
      ((2 * (p * (p - 1)) : ℕ) : ℚ) ≤
        1 - (terminalIdealCorrectedLaw r c cutoff 7).mass none := by
    simpa only [terminalIdealCorrectedLaw] using
      actualShape_terminalCorrected_success_lower r c hr hc
  exact terminalCorrectedRetry_accuracy_of_success r c cutoff 7 hrLarge hcLarge
    htotal hU (by omega) hp hr hc start h k fallback R _ hs

end
end Math115.PhysicalTraceJoin
