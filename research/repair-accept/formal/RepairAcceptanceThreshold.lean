import RepairAcceptanceCoin
import OAI.Combinatorics.ContingencyTables.Transport.FiniteRationalThreshold

namespace Math115.RepairAcceptanceCoin

open OAI.ContingencyTables.ResidualMixture OAI.ContingencyTables.FirstSuccess
open OAI.ContingencyTables.FairBits
open scoped BigOperators

/-- A computable natural-number quotient, requiring no integer-rejection loop. -/
def acceptanceThreshold (k c ell : ℕ) : ℕ := (2 ^ k * c) / ell

theorem acceptanceThreshold_eq_rationalThreshold (k c ell : ℕ) :
    acceptanceThreshold k c ell = rationalThreshold k ((c : ℚ) / ell) := by
  unfold acceptanceThreshold rationalThreshold
  rw [show (2 : ℚ) ^ k * ((c : ℚ) / ell) = ((2 ^ k * c : ℕ) : ℚ) / ell by
    push_cast
    ring, Nat.floor_div_eq_div]

theorem acceptanceRatio_nonnegative (c ell : ℕ) : 0 ≤ (c : ℚ) / ell := by positivity

theorem acceptanceRatio_le_one {c ell : ℕ} (hell : 0 < ell) (hc : c ≤ ell) :
    (c : ℚ) / ell ≤ 1 := by
  apply (div_le_iff₀ (show (0 : ℚ) < ell by exact_mod_cast hell)).mpr
  exact_mod_cast (by simpa using hc)

/-- After reading exactly `k` fair bits, test their decoded integer once. -/
def integerTerminal {A : Type*} (a : A) (k c ell : ℕ) (j : Fin (2 ^ k)) : Option A :=
  if j.val < acceptanceThreshold k c ell then some a else none

/-- The executable little-endian decoder underlying the pinned word equivalence. -/
def decodeBits (k : ℕ) (bits : Fin k → Bool) : Fin (2 ^ k) :=
  finFunctionFinEquiv (fun i => finTwoEquiv.symm (bits i))

theorem decodeBits_eq_binaryWordEquiv (k : ℕ) (bits : Fin k → Bool) :
    decodeBits k bits = binaryWordEquiv k bits := rfl

def bitTerminal {A : Type*} (a : A) (k c ell : ℕ)
    (bits : Fin k → Bool) : Option A :=
  integerTerminal a k c ell (decodeBits k bits)

variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def finiteBitLaw (a : A) (k c ell : ℕ) : RationalLaw (Option A) :=
  mapLaw (uniformLaw (α := Fin k → Bool)) (bitTerminal a k c ell)

/-- Exact counting of the codewords assigned to successful output `a`. -/
theorem integerTerminal_mass_some (a b : A) (k c ell : ℕ)
    (hell : 0 < ell) (hc : c ≤ ell) :
    (mapLaw (uniformLaw (α := Fin (2 ^ k))) (integerTerminal a k c ell)).mass (some b) =
      if b = a then rationalThresholdMass k ((c : ℚ) / ell) else 0 := by
  by_cases hba : b = a
  · subst b
    have hq0 := acceptanceRatio_nonnegative c ell
    have hq1 := acceptanceRatio_le_one hell hc
    have htest (j : Fin (2 ^ k)) : integerTerminal a k c ell j = some a ↔
        j.val < rationalThreshold k ((c : ℚ) / ell) := by
      by_cases hj : j.val < rationalThreshold k ((c : ℚ) / ell)
      <;> simp [integerTerminal, acceptanceThreshold_eq_rationalThreshold, hj]
    change (∑ j : Fin (2 ^ k), if integerTerminal a k c ell j = some a then
      (1 : ℚ) / Fintype.card (Fin (2 ^ k)) else 0) = _
    simp only [htest, ite_true, Fintype.card_fin]
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
    change ((Finset.univ.filter (fun j : Fin (2 ^ k) =>
      j.val < rationalThreshold k ((c : ℚ) / ell))).card : ℚ) *
      (1 / ((2 ^ k : ℕ) : ℚ)) = _
    rw [rationalThreshold_count k _ hq0 hq1]
    unfold rationalThresholdMass
    simp only [Nat.cast_pow, Nat.cast_ofNat, div_eq_mul_inv, one_mul]
  · change (∑ j : Fin (2 ^ k), if integerTerminal a k c ell j = some b then
      (1 : ℚ) / Fintype.card (Fin (2 ^ k)) else 0) = _
    simp [integerTerminal, hba, Ne.symm hba]

theorem finiteBitLaw_mass_some (a b : A) (k c ell : ℕ)
    (hell : 0 < ell) (hc : c ≤ ell) :
    (finiteBitLaw a k c ell).mass (some b) =
      if b = a then rationalThresholdMass k ((c : ℚ) / ell) else 0 := by
  have he := map_equiv (binaryWordEquiv k) (uniformLaw (α := Fin k → Bool))
    (integerTerminal a k c ell)
  rw [uniform_equiv] at he
  unfold finiteBitLaw bitTerminal
  simp only [decodeBits_eq_binaryWordEquiv]
  rw [← he]
  exact integerTerminal_mass_some a b k c ell hell hc

theorem finiteBitLaw_mass_none (a : A) (k c ell : ℕ)
    (hell : 0 < ell) (hc : c ≤ ell) :
    (finiteBitLaw a k c ell).mass none = 1 - rationalThresholdMass k ((c : ℚ) / ell) := by
  have ht := (finiteBitLaw a k c ell).total
  simp only [Fintype.sum_option, finiteBitLaw_mass_some a _ k c ell hell hc] at ht
  simp at ht
  linarith

/-- The actual mapped bit-word experiment has precisely the rounded coin law. -/
theorem finiteBitLaw_eq_coinLaw (a : A) (k c ell : ℕ)
    (hell : 0 < ell) (hc : c ≤ ell) :
    finiteBitLaw a k c ell = coinLaw a (rationalThresholdMass k ((c : ℚ) / ell))
      (rationalThreshold_error k _ (acceptanceRatio_nonnegative c ell)).1
      ((rationalThreshold_error k _ (acceptanceRatio_nonnegative c ell)).2.1.trans
        (acceptanceRatio_le_one hell hc)) := by
  apply RationalLaw.ext
  funext z
  cases z with
  | none => exact finiteBitLaw_mass_none a k c ell hell hc
  | some b => exact finiteBitLaw_mass_some a b k c ell hell hc

/-- Per terminal, fixed `k`-bit rounding loses less than `2⁻ᵏ` in total variation. -/
theorem finiteBitLaw_variation_lt (a : A) (k c ell : ℕ)
    (hell : 0 < ell) (hc : c ≤ ell) :
    variation (finiteBitLaw a k c ell)
      (coinLaw a ((c : ℚ) / ell) (acceptanceRatio_nonnegative c ell)
        (acceptanceRatio_le_one hell hc)) < 1 / (2 : ℚ) ^ k := by
  rw [finiteBitLaw_eq_coinLaw a k c ell hell hc, coinLaw_variation]
  have herr := rationalThreshold_error k ((c : ℚ) / ell) (acceptanceRatio_nonnegative c ell)
  rw [abs_of_nonpos (sub_nonpos.mpr herr.2.1)]
  linarith [herr.2.2]

theorem finiteBitLaw_variation_le (a : A) (k c ell : ℕ)
    (hell : 0 < ell) (hc : c ≤ ell) :
    variation (finiteBitLaw a k c ell)
      (coinLaw a ((c : ℚ) / ell) (acceptanceRatio_nonnegative c ell)
        (acceptanceRatio_le_one hell hc)) ≤ 1 / (2 : ℚ) ^ k :=
  (finiteBitLaw_variation_lt a k c ell hell hc).le

end Math115.RepairAcceptanceCoin
