/-
SPDX-License-Identifier: Apache-2.0
Scalar public-size bounds for the new ideal-scale reservation. This module
imports the compiled arithmetic/encoding core only, and has no sampler or
physical public-machine dependency. The precision parameter is numeric h.
Literal input-length bounds retain equal row/column totals explicitly.
-/
import Math115.CompletionEncodingSize

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace Math115.CompletionPublicSize
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped
open scoped BigOperators

/-- Reservation coefficient after the direct public-parameter comparison. -/
def bankCoefficient : ℕ := CompletionRandomBudget.budgetCoefficient * 5^85

def wordMeasureCoefficient : ℕ := bankCoefficient + 91

lemma clog_mass_add_two_le (M : ℕ) : Nat.clog 2 (M + 2) ≤ Nat.clog 2 (M + 1) + 1 := by
  have hm : M + 2 ≤ 2 * (M + 1) := by omega
  have hmono := Nat.clog_mono_right 2 hm
  have hprod := CompletionRandomBudget.clog_product_bound 2 (M + 1)
  have htwo : Nat.clog 2 2 = 1 := by decide
  omega

lemma samplingSize_at_least_two {m n : ℕ} (r : Fin m → ℕ) (h : ℕ) (hh : 1 ≤ h) :
    2 ≤ Algorithms.samplingSize n r h := by unfold Algorithms.samplingSize; omega

lemma combinedSize_public_bound {m n : ℕ} (r : Fin m → ℕ) (h : ℕ) (hh : 1 ≤ h) :
    CompletionRandomBudget.combinedSize
      (CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)) (∑ i, r i) h ≤
        5 * (Algorithms.samplingSize n r h)^2 := by
  let S := Algorithms.samplingSize n r h
  have hs : 2 ≤ S := samplingSize_at_least_two r h hh
  have hm : m + 1 ≤ S := by dsimp [S, Algorithms.samplingSize]; omega
  have hn : n + 1 ≤ S := by dsimp [S, Algorithms.samplingSize]; omega
  have hprod := Nat.mul_le_mul hm hn
  have hd : CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n) ≤ 10 + S^2 := by
    simpa only [CompletionCounts.dimensionAllowance, Fintype.card_fin, pow_two] using
      Nat.add_le_add_left hprod 10
  have hb := clog_mass_add_two_le (∑ i, r i)
  have hsmall : CompletionRandomBudget.binarySize (∑ i, r i) + h + 3 ≤ S + 3 := by
    dsimp [S, Algorithms.samplingSize, CompletionRandomBudget.binarySize]
    omega
  have hmid : CompletionRandomBudget.combinedSize
      (CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)) (∑ i, r i) h ≤ S^2 + S + 13 := by
    unfold CompletionRandomBudget.combinedSize
    omega
  exact hmid.trans (by nlinarith)

/-- This is a fair-bit bank bound, not an execution-time exponent. The
small-cell count is a supplied scalar bounded by the actual dimension. -/
lemma reservation_public_bound {m n : ℕ} (r : Fin m → ℕ) (p h : ℕ)
    (hp : p ≤ CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)) (hh : 1 ≤ h) :
    CompletionRandomBudget.totalReservedBits
      (CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)) p (∑ i, r i) h ≤
        bankCoefficient * (Algorithms.samplingSize n r h)^170 := by
  have hbound := CompletionRandomBudget.totalReservedBits_combined
    (CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)) p (∑ i, r i) h
    IdealOracleScales.dimension_at_least_eleven hp
  have hpowers := Nat.pow_le_pow_left (combinedSize_public_bound (n := n) r h hh) 85
  calc
    _ ≤ CompletionRandomBudget.budgetCoefficient *
        (CompletionRandomBudget.combinedSize
          (CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)) (∑ i, r i) h)^85 := hbound
    _ ≤ CompletionRandomBudget.budgetCoefficient * (5 * (Algorithms.samplingSize n r h)^2)^85 :=
      Nat.mul_le_mul_left _ hpowers
    _ = _ := by
      unfold bankCoefficient
      rw [mul_pow, ← pow_mul, show (2 : ℕ) * 85 = 170 by decide, mul_assoc]

/-- The literal-symbol tree input weight (18 per symbol plus a terminator)
and the whole bank fit a public polynomial. Equal totals are essential to
bound both row and column input words in terms of the row total. -/
lemma literal_input_and_bank_public_bound {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (htotal : ∑ i, r i = ∑ j, c j) (p h : ℕ)
    (hp : p ≤ CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)) (hh : 1 ≤ h) :
    18 * (Algorithms.encodeSamplingInput r c h).length + 1 +
      CompletionRandomBudget.totalReservedBits
        (CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)) p (∑ i, r i) h ≤
          wordMeasureCoefficient * (Algorithms.samplingSize n r h)^170 := by
  let S := Algorithms.samplingSize n r h
  have hs : 1 ≤ S := (by have hx := samplingSize_at_least_two (n := n) r h hh; dsimp only [S]; omega)
  have hlen := Algorithms.encodeSamplingInput_length r c htotal h
  have hbank := reservation_public_bound (n := n) r p h hp hh
  have hpow : S^2 ≤ S^170 := Nat.pow_le_pow_right hs (by decide : 2 ≤ 170)
  have hone : 1 ≤ S^170 := one_le_pow₀ hs
  calc
    _ ≤ 18 * (5 * S^2) + S^170 + bankCoefficient * S^170 :=
      Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hlen) hone) hbank
    _ ≤ 18 * (5 * S^170) + S^170 + bankCoefficient * S^170 := by
      exact Nat.add_le_add_right
        (Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 5 hpow)) _) _
    _ = _ := by dsimp only [S]; unfold wordMeasureCoefficient; rw [Nat.add_mul]; omega

end Math115.CompletionPublicSize
