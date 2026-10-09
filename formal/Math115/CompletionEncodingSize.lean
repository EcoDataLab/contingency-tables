/-
SPDX-License-Identifier: Apache-2.0
Encoded margin size, numeric target precision, and reserved-bank weight.
Only arithmetic and TreeTyped interfaces are imported. The final cost theorem
is parameterized by a supplied deterministic realizer; it does not instantiate
or claim a compiled physical sampler or a particular machine-time degree.
-/
import Math115.CompletionRandomBudgetArithmetic
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostMeasure
import OAI.Combinatorics.ContingencyTables.Machines.PublicInputLength

set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace Math115.CompletionEncodingSize
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped
open scoped BigOperators

abbrev Margins := List ℕ × List ℕ
abbrev WordInput := (Margins × ℕ) × List Bool

def dimension (a : Margins) : ℕ := 10 + (a.1.length + 1) * (a.2.length + 1)
def massTotal (a : Margins) : ℕ := a.1.sum
/-- Precision is numeric h, not its binary length. -/
def measure (a : Margins) (h : ℕ) : ℕ := weight a + h + 3

def bankCoefficient : ℕ := CompletionRandomBudget.budgetCoefficient * 2^85

noncomputable def inputEnvelope : Polynomial ℕ :=
  4 * Polynomial.X + Polynomial.C (4 * bankCoefficient) * Polynomial.X^170

lemma pow_two_add_le (u v : ℕ) : 2^u + 2^v ≤ 2^(1 + u + v) := by
  have hu : 1 ≤ 2^u := one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))
  have hv : 1 ≤ 2^v := one_le_pow₀ (by decide : 1 ≤ (2 : ℕ))
  have ha : 2^u ≤ 2^u * 2^v := by simpa using Nat.mul_le_mul_left (2^u) hv
  have hb : 2^v ≤ 2^u * 2^v := by simpa using Nat.mul_le_mul_right (2^v) hu
  calc
    _ ≤ 2 * (2^u * 2^v) := by omega
    _ = _ := by simp only [pow_add, pow_one]; ring

lemma nat_succ_le_pow_weight (x : ℕ) : x + 1 ≤ 2^(weight x) := by
  have hx := Nat.lt_size_self x
  exact (Nat.succ_le_of_lt hx).trans (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ))
    (size_le_weight x))

lemma sum_add_two_le_pow_weight (xs : List ℕ) : xs.sum + 2 ≤ 2^(weight xs) := by
  induction xs with
  | nil => norm_num [weight_nil]
  | cons x xs ih =>
    have hx := nat_succ_le_pow_weight x
    have ht : xs.sum + 1 ≤ 2^(weight xs) := by omega
    calc
      _ ≤ 2^(weight x) + 2^(weight xs) := by simp only [List.sum_cons]; omega
      _ ≤ 2^(1 + weight x + weight xs) := pow_two_add_le _ _
      _ = _ := by rw [weight_cons]

lemma clog_sum_add_two_le_weight (xs : List ℕ) : Nat.clog 2 (xs.sum + 2) ≤ weight xs :=
  Nat.clog_le_of_le_pow (sum_add_two_le_pow_weight xs)

lemma margin_weight_at_least_three (a : Margins) : 3 ≤ weight a := by
  have hr := weight_pos a.1
  have hc := weight_pos a.2
  rw [weight_prod]
  omega

lemma measure_at_least_six (a : Margins) (h : ℕ) : 6 ≤ measure a h := by
  have he := margin_weight_at_least_three a
  unfold measure
  omega

lemma dimension_at_least_eleven (a : Margins) : 11 ≤ dimension a := by
  have hp : 1 ≤ (a.1.length + 1) * (a.2.length + 1) := Nat.mul_pos (by omega) (by omega)
  unfold dimension
  omega

lemma dimension_le_weight_square (a : Margins) : dimension a ≤ 10 + (weight a)^2 := by
  have hr := list_length_le_weight a.1
  have hc := list_length_le_weight a.2
  have hR : a.1.length + 1 ≤ weight a := by rw [weight_prod]; omega
  have hC : a.2.length + 1 ≤ weight a := by rw [weight_prod]; omega
  have hp := Nat.mul_le_mul hR hC
  simpa only [dimension, pow_two] using Nat.add_le_add_left hp 10

lemma binary_mass_le_weight (a : Margins) : CompletionRandomBudget.binarySize (massTotal a) ≤ weight a := by
  have h := clog_sum_add_two_le_weight a.1
  unfold CompletionRandomBudget.binarySize massTotal
  rw [weight_prod]
  omega

lemma combinedSize_le_twice_measure_square (a : Margins) (h : ℕ) :
    CompletionRandomBudget.combinedSize (dimension a) (massTotal a) h ≤ 2 * (measure a h)^2 := by
  have hd := dimension_le_weight_square a
  have hb := binary_mass_le_weight a
  have hs := measure_at_least_six a h
  have he : weight a ≤ measure a h := by unfold measure; omega
  have he2 := Nat.pow_le_pow_left he 2
  unfold CompletionRandomBudget.combinedSize
  have hmid : dimension a + CompletionRandomBudget.binarySize (massTotal a) + (h + 3) ≤
      (measure a h)^2 + measure a h + 10 := by
    unfold measure at *
    omega
  exact hmid.trans (by nlinarith)

lemma bank_bound (a : Margins) (p h : ℕ) (hp : p ≤ dimension a) :
    CompletionRandomBudget.totalReservedBits (dimension a) p (massTotal a) h ≤
      bankCoefficient * (measure a h)^170 := by
  have hbound := CompletionRandomBudget.totalReservedBits_combined (dimension a) p (massTotal a) h
    (dimension_at_least_eleven a) hp
  have hm := Nat.pow_le_pow_left (combinedSize_le_twice_measure_square a h) 85
  calc
    _ ≤ CompletionRandomBudget.budgetCoefficient *
        (CompletionRandomBudget.combinedSize (dimension a) (massTotal a) h)^85 := hbound
    _ ≤ CompletionRandomBudget.budgetCoefficient * (2 * (measure a h)^2)^85 :=
      Nat.mul_le_mul_left _ hm
    _ = _ := by
      unfold bankCoefficient
      rw [mul_pow, ← pow_mul, show (2 : ℕ) * 85 = 170 by decide, mul_assoc]

/-- The complete deterministic input, including the bank, fits one polynomial
of margin encoding weight plus numeric target precision. -/
lemma input_weight_bound (a : Margins) (p h : ℕ) (hp : p ≤ dimension a) (bs : List Bool)
    (hlen : bs.length ≤ CompletionRandomBudget.totalReservedBits (dimension a) p (massTotal a) h) :
    weight ((a, h), bs) ≤ inputEnvelope.eval (measure a h) := by
  have hbank := bank_bound a p h hp
  have hbits := weight_bits bs
  have hh := weight_nat_numeric h
  have hlen' : bs.length ≤ bankCoefficient * (measure a h)^170 := hlen.trans hbank
  have hfour : weight a + 4 * h + 4 ≤ 4 * measure a h := by unfold measure; omega
  simp only [inputEnvelope, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow]
  rw [weight_prod, weight_prod]
  nlinarith

/-- Generic cost-and-output bound; the supplied realizer can later be the
compiled sampler. No distribution or physical-oracle premise enters here. -/
theorem reserved_program_work {B : Type} [Codec B] {f : WordInput → B} {F : Realizer f}
    (hF : PolynomialTime F) :
    ∃ P : Polynomial ℕ, ∀ (a : Margins) (p h : ℕ), p ≤ dimension a →
      ∀ bs : List Bool,
        bs.length ≤ CompletionRandomBudget.totalReservedBits (dimension a) p (massTotal a) h →
        F.cost ((a, h), bs) + weight (f ((a, h), bs)) ≤ P.eval (measure a h) := by
  obtain ⟨Q, hQ⟩ := hF
  refine ⟨Q.comp inputEnvelope, ?_⟩
  intro a p h hp bs hlen
  apply (hQ ((a, h), bs)).trans
  simpa only [Polynomial.eval_comp] using polynomial_eval_monotone Q (input_weight_bound a p h hp bs hlen)

lemma weight_nat_list_le_word_length (xs : List ℕ) :
    weight xs ≤ 4 * (xs.flatMap OAI.MatchingFPRAS.encodeNat).length + 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := weight_nat_le x
    simp only [weight_cons, List.flatMap_cons, List.length_append, Algorithms.encodeNat_length]
    omega

lemma margin_weight_le_literal_length {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    weight (List.ofFn r, List.ofFn c) ≤ 4 * (Algorithms.encodeMargins r c).length := by
  have hr := weight_nat_list_le_word_length (List.ofFn r)
  have hc := weight_nat_list_le_word_length (List.ofFn c)
  have hm : 1 ≤ (OAI.MatchingFPRAS.encodeNat m).length := by rw [Algorithms.encodeNat_length]; omega
  have hn : 1 ≤ (OAI.MatchingFPRAS.encodeNat n).length := by rw [Algorithms.encodeNat_length]; omega
  simp only [List.flatMap_def, ← List.ofFn_comp'] at hr hc
  unfold Algorithms.encodeMargins
  simp only [List.length_append, weight_prod]
  omega

lemma measure_le_literal_length_numeric {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (h : ℕ) :
    measure (List.ofFn r, List.ofFn c) h ≤ 4 * ((Algorithms.encodeMargins r c).length + h + 3) := by
  have he := margin_weight_le_literal_length r c
  unfold measure
  omega

lemma dimension_ofFn {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    dimension (List.ofFn r, List.ofFn c) = CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n) := by
  simp only [dimension, List.length_ofFn, CompletionCounts.dimensionAllowance, Fintype.card_fin]

lemma massTotal_ofFn {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) :
    massTotal (List.ofFn r, List.ofFn c) = ∑ i, r i := by simp only [massTotal, List.sum_ofFn]

end Math115.CompletionEncodingSize
