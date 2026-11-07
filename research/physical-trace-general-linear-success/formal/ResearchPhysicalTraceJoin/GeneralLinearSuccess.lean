/-
SPDX-License-Identifier: Apache-2.0
A linear reciprocal success allowance for the corrected physical trace.
This refines the outer retry budget; it does not change the spectral gap.
-/
import ResearchPhysicalTraceJoin.ZeroMarginCorrected

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open SmallGraphProfiles FirstPaperProfiles CompletionCounts SmallContextCoordinates
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open scoped BigOperators Classical
noncomputable section

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U : ℕ)

/-- Inclusion-exclusion for the union of the small rows and columns. -/
theorem smallCell_card_incidence :
    Fintype.card (Cells (firstPaperSmall r c U)) +
      Fintype.card (RepairSmallRows r U) * Fintype.card (RepairSmallColumns c U) =
    n * Fintype.card (RepairSmallRows r U) +
      m * Fintype.card (RepairSmallColumns c U) := by
  let rows := Finset.univ.filter (fun i : Fin m => r i < U)
  let cols := Finset.univ.filter (fun j : Fin n => c j < U)
  let R : Finset (Fin m × Fin n) := rows ×ˢ Finset.univ
  let C : Finset (Fin m × Fin n) := Finset.univ ×ˢ cols
  have hu : R ∪ C = Finset.univ.filter
      (fun ij : Fin m × Fin n => firstPaperSmall r c U ij.1 ij.2 = true) := by
    ext ij
    simp [R, C, rows, cols, firstPaperSmall]
  have hi : R ∩ C = rows ×ˢ cols := by
    ext ij
    simp [R, C, rows, cols]
  have h := Finset.card_union_add_card_inter R C
  rw [hu, hi] at h
  simpa only [Cells, Fintype.card_subtype, R, C, Finset.card_product,
    Finset.card_univ, Fintype.card_fin, RepairSmallRows, RepairSmallColumns,
    rows, cols, Nat.mul_comm] using h

private theorem incidence_allowance_twice (m n a b p : ℕ)
    (hcount : p + a * b = n * a + m * b) :
    p - 1 ≤ 2 * max (a * (n * a - 1)) (b * (m * b - 1)) := by
  let K := max (a * (n * a - 1)) (b * (m * b - 1))
  have haK : a * (n * a - 1) ≤ K := le_max_left _ _
  have hbK : b * (m * b - 1) ≤ K := le_max_right _ _
  by_cases ha : a = 0
  · subst a
    by_cases hb : b = 0
    · subst b; simp_all
    have hb1 : 1 ≤ b := by omega
    have hmul := Nat.mul_le_mul_right (m * b - 1) hb1
    simp only [one_mul] at hmul
    simp only [Nat.mul_zero, zero_mul, Nat.add_zero, Nat.zero_add] at hcount
    omega
  by_cases hb : b = 0
  · subst b
    have ha1 : 1 ≤ a := by omega
    have hmul := Nat.mul_le_mul_right (n * a - 1) ha1
    simp only [one_mul] at hmul
    simp only [Nat.mul_zero, zero_mul, Nat.add_zero, Nat.zero_add] at hcount
    omega
  have ha1 : 1 ≤ a := by omega
  have hb1 : 1 ≤ b := by omega
  have hma := Nat.mul_le_mul_right (n * a - 1) ha1
  have hmb := Nat.mul_le_mul_right (m * b - 1) hb1
  simp only [one_mul] at hma hmb
  have hab : 1 ≤ a * b := Nat.mul_pos (by omega) (by omega)
  omega

/-- The geometric correction numerator is at least half of p-1. -/
theorem inverseSupportAllowance_twice :
    Fintype.card (Cells (firstPaperSmall r c U)) - 1 ≤
      2 * inverseSupportAllowance r c U := by
  exact incidence_allowance_twice m n _ _ _ (smallCell_card_incidence r c U)

/-- Linear inverse-success allowance, derived without a success hypothesis.
The branch supplies p>=2 and the exact count formula supplies the numerator. -/
theorem positiveTraceCorrectionSuccess_linear (xs ys : List ℕ)
    (hb : positiveTraceBranch xs ys = .reference) :
    let p := Fintype.card (Cells (firstPaperSmall (filteredMargin xs)
      (filteredMargin ys) (positiveTraceCutoff xs ys)))
    1 / (4 * (p : ℚ)) ≤ positiveTraceCorrectionSuccess xs ys := by
  let r := filteredMargin xs
  let c := filteredMargin ys
  let U := positiveTraceCutoff xs ys
  let p := Fintype.card (Cells (firstPaperSmall r c U))
  let K := inverseSupportAllowance r c U
  have hp : 2 ≤ p := (positiveTraceReference_conditions xs ys hb).2.2.1
  have hK : p - 1 ≤ 2 * K := inverseSupportAllowance_twice r c U
  have hpQ : (0 : ℚ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1Q : (0 : ℚ) < p - 1 := by
    have h : (1 : ℚ) < p := by exact_mod_cast (show 1 < p by omega)
    linarith
  have hKQ : (p : ℚ) - 1 ≤ 2 * (K : ℚ) := by
    have h := (Nat.cast_le (α := ℚ)).mpr hK
    simpa only [Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one, Nat.cast_mul,
      Nat.cast_ofNat] using h
  change 1 / (4 * (p : ℚ)) ≤ (K : ℚ) / ((2 * (p * (p - 1)) : ℕ) : ℚ)
  rw [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_mul,
    Nat.cast_sub (show 1 ≤ p by omega), Nat.cast_one]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

end
end Math115.PhysicalTraceJoin
