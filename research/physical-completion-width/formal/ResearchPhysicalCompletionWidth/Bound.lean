/-
SPDX-License-Identifier: Apache-2.0
An explicit state-independent completion-word allowance.
The exponent and coefficient are the existing frozen sampler's reserved-bit
bound. This module supplies no extracted machine or machine-time estimate.
-/
import ResearchComparison.LegacyPhysicalCompletion
import ResearchComparison.ResidualCap

set_option maxHeartbeats 800000

namespace Math115.PhysicalCompletionWidth

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open FirstSuccess ResidualMixture
open Math115.ReducedSmallChain
open Math115.LegacyPhysicalCompletion Math115.LegacyResidualCap
open Math115.CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section

lemma coarseIndexCount_le {m : ℕ} (r : Fin m → ℕ) (U : ℕ)
    (hr : 0 < (largeIndices (U, List.ofFn r)).length) : tailCount r U + 1 ≤ m := by
  have he := Fintype.card_congr (largeOptionEquiv r U hr)
  have hs : Fintype.card (LargeRows r U) ≤ m :=
    (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin m)
  rw [Fintype.card_option, Fintype.card_fin] at he
  unfold tailCount
  omega

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

local notation "dimension" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "requestDimension" => dimensionAllowance
  (I := Fin (tailCount r U + 1)) (J := Fin (tailCount c U + 1))
local notation "B" => capacity r c U L

/-- Padded original total; no maximum over physical states is computed. -/
def residualMassBound : ℕ :=
  (∑ i, r i) + L * (largeRowCount r U * largeColumnCount c U)

include hr hc in
lemma coarseDimension_le : requestDimension ≤ dimension := by
  have hrow := coarseIndexCount_le r U hr
  have hcol := coarseIndexCount_le c U hc
  unfold dimensionAllowance
  simp only [Fintype.card_fin]
  exact Nat.add_le_add_left
    (Nat.mul_le_mul (Nat.add_le_add_right hrow 1) (Nat.add_le_add_right hcol 1)) 10

/-- The computed request reindexes all nonzero residual rows. Positivity of
the actual physical state forces the omitted rows' residuals to vanish. -/
lemma coarseRows_total (z : States r c U L) :
    (∑ i, coarseRows r c U L hr z i) =
      ∑ i, residualRows (firstPaperSmall r c U) B r c L z i := by
  calc
    _ = ∑ i : Option (Fin (tailCount r U)), listedRows r c U L B hr z i :=
      (finSuccEquiv (tailCount r U)).sum_comp (listedRows r c U L B hr z)
    _ = ∑ i : LargeRows r U, residualRows (firstPaperSmall r c U) B r c L z i.val :=
      (largeOptionEquiv r U hr).sum_comp
        (fun i : LargeRows r U => residualRows (firstPaperSmall r c U) B r c L z i.val)
    _ = _ := by
      convert sum_subtype_eq_of_zero (fun i => U ≤ r i)
        (residualRows (firstPaperSmall r c U) B r c L z)
        (physical_residual_row_zero r c U L B z
          (physical_paper_capacity _ r c _ L U dimension_le_allowance z)) using 1
      congr 2
      exact Subsingleton.elim _ _

lemma coarseRows_total_le_massBound (z : States r c U L) :
    (∑ i, coarseRows r c U L hr z i) ≤ residualMassBound r c U L := by
  rw [coarseRows_total]
  calc
    _ ≤ (∑ i, r i) + markedCount (firstPaperSmall r c U) * L :=
      residual_total_bound (firstPaperSmall r c U) B r c L z
    _ = residualMassBound r c U L := by
      unfold residualMassBound
      rw [rectangle_marked_count, Nat.mul_comm _ L]

def uniformCompletionBits (h : ℕ) : ℕ :=
  Math115.CompletionRandomBudget.budgetCoefficient *
    (Math115.CompletionRandomBudget.combinedSize dimension (residualMassBound r c U L) h)^85

include hc in
/-- Dimension, total and logarithmic request-size bounds are all proved for
the actual coarse residual request. Arbitrary U,L and zero margins remain. -/
lemma requestSize_le (z : States r c U L) (h : ℕ) :
    Math115.CompletionRandomBudget.combinedSize requestDimension
      (∑ i, coarseRows r c U L hr z i) h ≤
    Math115.CompletionRandomBudget.combinedSize dimension (residualMassBound r c U L) h := by
  have hd := coarseDimension_le r c U hr hc
  have hm := coarseRows_total_le_massBound r c U L hr z
  have hl := Nat.clog_mono_right 2 (Nat.add_le_add_right hm 2)
  unfold Math115.CompletionRandomBudget.combinedSize Math115.CompletionRandomBudget.binarySize
  omega

/-- The frozen sampler's existing coefficient and exponent supply a common
completion width before any physical state is sampled. -/
theorem completionBits_le_uniform (z : States r c U L) (h : ℕ) :
    bits r c U L hr hc z h ≤ uniformCompletionBits r c U L h := by
  have hb := Math115.LatticeSampler.reservedBits_combined
    (coarseRows r c U L hr z) (coarseColumns r c U L hc z) h
  change bits r c U L hr hc z h ≤ Math115.CompletionRandomBudget.budgetCoefficient *
    (Math115.CompletionRandomBudget.combinedSize requestDimension
      (∑ i, coarseRows r c U L hr z i) h)^85 at hb
  exact hb.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
    (requestSize_le r c U L hr hc z h) 85))

end
end Math115.PhysicalCompletionWidth
