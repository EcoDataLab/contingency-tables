import Math115.CompletionRandomBudgetArithmetic
import Math115.CompletionOuterSchedule

namespace Math115.CompletionRandomBudget

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open CompletionOuterSchedule CompletionRetryBudget
open SmallGraphProfiles SmallContextCoordinates CompletionCounts
open scoped BigOperators


noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
local notation "d" => dimensionAllowance (I := I) (J := J)

omit [LinearOrder I] [LinearOrder J] in
lemma physicalSmallCount_le_dimension (r : I → ℕ) (c : J → ℕ) :
    physicalSmallCount r c ≤ d := by
  exact (show Fintype.card (Cells (firstPaperSmall r c (IdealOracleScales.cutoff (I := I) (J := J)))) ≤
      Fintype.card I * Fintype.card J by
        simpa only [Fintype.card_prod] using Fintype.card_subtype_le
          (fun a : I × J => firstPaperSmall r c
            (IdealOracleScales.cutoff (I := I) (J := J)) a.1 a.2 = true)).trans dimension_le_allowance

omit [LinearOrder I] [LinearOrder J] in
lemma completionReservation_eq_reserved (r : I → ℕ) (t : ℕ) :
    completionReservation d (∑ i, r i) t = PhysicalLatticeCompletion.reservedCompletionBits (J := J) r t := by
  have hC : fineMarginBound d (∑ i, r i) = PhysicalLatticeCompletion.fineRowBound (J := J) r := by
    unfold fineMarginBound PhysicalLatticeCompletion.fineRowBound
      IdealOracleScales.padding IdealOracleScales.idealL
    ring
  unfold completionReservation PhysicalLatticeCompletion.reservedCompletionBits
    PhysicalLatticeCompletion.reservedFineBits fineBinaryBound PhysicalLatticeCompletion.fineBinaryLength
  rw [hC]

/-- The same reservation expression as the reference Boolean module's
outerBits after specializing the ideal scales. -/
def physicalTotalReservedBits (r : I → ℕ) (c : J → ℕ) (h : ℕ) : ℕ :=
  totalReservedBits d (physicalSmallCount r c) (∑ i, r i) h

omit [LinearOrder I] [LinearOrder J] in
/-- Exposes the actual state-independent common widths, without importing
PhysicalReferenceBoolean and creating a dependency cycle. Its outerBits
matches this right side after unfolding stepBits and attemptBits. -/
lemma physicalTotalReservedBits_eq_reservation (r : I → ℕ) (c : J → ℕ) (h : ℕ) :
    let p := physicalSmallCount r c
    let base := physicalMassBase (J := J) r
    physicalTotalReservedBits r c h = restartCount p h *
      (walkCount p d base h * (proposalReservation d +
        PhysicalLatticeCompletion.reservedCompletionBits (J := J) r (stepPrecision p d base h)) +
        PhysicalLatticeCompletion.reservedCompletionBits (J := J) r (terminalPrecision p h)) := by
  have hb : (∑ i, r i) + 3 * d ^ 2 + 5 * d ^ 3 + 3 = physicalMassBase (J := J) r := by
    unfold physicalMassBase IdealOracleScales.padding IdealOracleScales.cutoff
      IdealOracleScales.idealL IdealOracleScales.idealU
    ring
  dsimp only [physicalTotalReservedBits, totalReservedBits]
  simp only [hb, completionReservation_eq_reserved]

theorem physicalTotalReservedBits_separated (r : I → ℕ) (c : J → ℕ) (h : ℕ) :
    physicalTotalReservedBits r c h ≤ budgetCoefficient * d ^ 20 * (h + 3) *
      (combinedSize d (∑ i, r i) h) ^ 64 :=
  totalReservedBits_separated d (physicalSmallCount r c) (∑ i, r i) h
    IdealOracleScales.dimension_at_least_eleven (physicalSmallCount_le_dimension r c)

theorem physicalTotalReservedBits_combined (r : I → ℕ) (c : J → ℕ) (h : ℕ) :
    physicalTotalReservedBits r c h ≤ budgetCoefficient * (combinedSize d (∑ i, r i) h) ^ 85 :=
  totalReservedBits_combined d (physicalSmallCount r c) (∑ i, r i) h
    IdealOracleScales.dimension_at_least_eleven (physicalSmallCount_le_dimension r c)

end
end Math115.CompletionRandomBudget
