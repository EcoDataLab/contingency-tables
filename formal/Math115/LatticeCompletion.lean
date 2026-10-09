/-
SPDX-License-Identifier: Apache-2.0
Exact integer prefixSum/adjacent-cycle codec for completion dilation.
This module does not prove volume comparison, rejection acceptance,
a dense-oracle realization, or a finite-bit machine-cost theorem.
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Set
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic

namespace Math115.LatticeCompletion

open scoped BigOperators

/-- Arrays use natural coordinates; finite statements use explicit range sums.
No equality outside a finite rectangle is implicit in a finite-table claim. -/
abbrev Array := ℕ → ℕ → ℤ

def difference (u : Array) : Array := fun i j =>
  u (i + 1) (j + 1) - u i (j + 1) - u (i + 1) j + u i j

def prefixSum (X : Array) (p q : ℕ) : ℤ :=
  ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, X i j

def ZeroAxes (u : Array) : Prop := (∀ q, u 0 q = 0) ∧ (∀ p, u p 0 = 0)

def ZeroBoundary (a b : ℕ) (u : Array) : Prop :=
  ZeroAxes u ∧ (∀ q, u a q = 0) ∧ (∀ p, u p b = 0)

def BoundedDigits (k : ℤ) (u : Array) : Prop := ∀ p q, 0 ≤ u p q ∧ u p q < k

lemma difference_row_sum (u : Array) (i b : ℕ) :
    (∑ j ∈ Finset.range b, difference u i j) =
      (u (i + 1) b - u i b) - (u (i + 1) 0 - u i 0) := by
  calc
    _ = ∑ j ∈ Finset.range b,
        ((u (i + 1) (j + 1) - u i (j + 1)) - (u (i + 1) j - u i j)) := by
      apply Finset.sum_congr rfl
      intro j _
      unfold difference
      ring
    _ = _ := Finset.sum_range_sub (fun j => u (i + 1) j - u i j) b

lemma difference_column_sum (u : Array) (a j : ℕ) :
    (∑ i ∈ Finset.range a, difference u i j) =
      (u a (j + 1) - u a j) - (u 0 (j + 1) - u 0 j) := by
  calc
    _ = ∑ i ∈ Finset.range a,
        ((u (i + 1) (j + 1) - u (i + 1) j) - (u i (j + 1) - u i j)) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold difference
      ring
    _ = _ := Finset.sum_range_sub (fun i => u i (j + 1) - u i j) a

lemma difference_row_sum_zero (a b : ℕ) (u : Array) (hu : ZeroBoundary a b u) (i : ℕ) :
    (∑ j ∈ Finset.range b, difference u i j) = 0 := by
  rw [difference_row_sum, hu.2.2, hu.2.2, hu.1.2, hu.1.2]
  ring

lemma difference_column_sum_zero (a b : ℕ) (u : Array) (hu : ZeroBoundary a b u) (j : ℕ) :
    (∑ i ∈ Finset.range a, difference u i j) = 0 := by
  rw [difference_column_sum, hu.2.1, hu.2.1, hu.1.1, hu.1.1]
  ring

lemma prefix_zero_axes (X : Array) : ZeroAxes (prefixSum X) := by
  constructor <;> intro n <;> simp [prefixSum]

/-- Rectangular prefixSum sums invert adjacent-cycle differences when the
upper and left prefixSum boundaries vanish. -/
theorem prefix_difference (u : Array) (hu : ZeroAxes u) (p q : ℕ) :
    prefixSum (difference u) p q = u p q := by
  unfold prefixSum
  simp_rw [difference_row_sum, hu.2, sub_self, sub_zero]
  rw [Finset.sum_range_sub (fun i => u i q) p, hu.1, sub_zero]

/-- No boundary or sign assumption is needed in this direction. -/
theorem difference_prefix (X : Array) : difference (prefixSum X) = X := by
  funext i j
  unfold difference prefixSum
  simp only [Finset.sum_range_succ, Finset.sum_add_distrib]
  ring

lemma difference_bounds (k : ℤ) (u : Array) (hu : BoundedDigits k u) (i j : ℕ) :
    -2 * (k - 1) ≤ difference u i j ∧ difference u i j ≤ 2 * (k - 1) := by
  have h00 := hu i j
  have h01 := hu i (j + 1)
  have h10 := hu (i + 1) j
  have h11 := hu (i + 1) (j + 1)
  unfold difference
  constructor <;> omega

def encode (k : ℤ) (X u : Array) : Array :=
  fun i j => k * (X i j + 2) + difference u i j

/-- Euclidean integer division is floor division for positive k, including
negative prefixSum numerators. Truncation toward zero is not substituted. -/
def decode (k : ℤ) (Z : Array) : Array :=
  fun i j => difference (fun p q => prefixSum Z p q / k) i j - 2

def residue (k : ℤ) (Z : Array) : Array := fun p q => prefixSum Z p q % k

lemma prefix_encode (k : ℤ) (X u : Array) (hu : ZeroAxes u) (p q : ℕ) :
    prefixSum (encode k X u) p q = k * prefixSum (fun i j => X i j + 2) p q + u p q := by
  have hlin : prefixSum (encode k X u) p q =
      k * prefixSum (fun i j => X i j + 2) p q + prefixSum (difference u) p q := by
    simp only [prefixSum, encode, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hlin, prefix_difference u hu]

lemma scaled_digit_ediv (k z u : ℤ) (hk : 0 < k) (hu0 : 0 ≤ u) (hu1 : u < k) :
    (k * z + u) / k = z := by
  rw [add_comm, Int.add_mul_ediv_left u z (ne_of_gt hk), Int.ediv_eq_zero_of_lt hu0 hu1]
  simp

lemma scaled_digit_emod (k z u : ℤ) (hu0 : 0 ≤ u) (hu1 : u < k) :
    (k * z + u) % k = u := by
  rw [add_comm, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hu0 hu1]

/-- The signed integer decoder exactly recovers the original array. -/
theorem decode_encode (k : ℤ) (hk : 0 < k) (X u : Array)
    (haxes : ZeroAxes u) (hdigits : BoundedDigits k u) : decode k (encode k X u) = X := by
  have hquot : (fun p q => prefixSum (encode k X u) p q / k) =
      prefixSum (fun i j => X i j + 2) := by
    funext p q
    rw [prefix_encode k X u haxes]
    exact scaled_digit_ediv k _ _ hk (hdigits p q).1 (hdigits p q).2
  funext i j
  unfold decode
  rw [hquot, difference_prefix]
  ring

theorem residue_encode (k : ℤ) (X u : Array) (haxes : ZeroAxes u)
    (hdigits : BoundedDigits k u) : residue k (encode k X u) = u := by
  funext p q
  unfold residue
  rw [prefix_encode k X u haxes]
  exact scaled_digit_emod k _ _ (hdigits p q).1 (hdigits p q).2

lemma residue_zero_axes (k : ℤ) (Z : Array) : ZeroAxes (residue k Z) := by
  constructor <;> intro n <;> simp [residue, prefixSum]

lemma residue_bounded (k : ℤ) (hk : 0 < k) (Z : Array) : BoundedDigits k (residue k Z) := by
  intro p q
  exact ⟨Int.emod_nonneg _ (ne_of_gt hk), Int.emod_lt_of_pos _ hk⟩

/-- The inverse direction holds for every signed array, without feasibility
or positivity assumptions. -/
theorem encode_decode (k : ℤ) (Z : Array) : encode k (decode k Z) (residue k Z) = Z := by
  have h (p q : ℕ) : k * (prefixSum Z p q / k) + prefixSum Z p q % k = prefixSum Z p q :=
    Int.mul_ediv_add_emod _ _
  funext i j
  have h00 := h i j
  have h01 := h i (j + 1)
  have h10 := h (i + 1) j
  have h11 := h (i + 1) (j + 1)
  have hrec := congrFun (congrFun (difference_prefix Z) i) j
  unfold encode decode residue difference at *
  nlinarith only [h00, h01, h10, h11, hrec]

/-- Each original entry remains strictly feasible after adding two and
encoding any bounded offset digits. -/
theorem encode_entry_at_least_two (k : ℤ) (hk : 0 < k) (X u : Array)
    (hdigits : BoundedDigits k u) (i j : ℕ) (hX : 0 ≤ X i j) :
    2 ≤ encode k X u i j := by
  have hD := (difference_bounds k u hdigits i j).1
  have hmul : 0 ≤ k * X i j := mul_nonneg hk.le hX
  unfold encode
  nlinarith only [hD, hmul]

/-- Encoding preserves the row margins after exactly the stated dilation
and per-cell shift, including zero-width rectangles. -/
theorem encode_row_margin (a b : ℕ) (k : ℤ) (X u : Array)
    (hu : ZeroBoundary a b u) (i : ℕ) :
    (∑ j ∈ Finset.range b, encode k X u i j) =
      k * ((∑ j ∈ Finset.range b, X i j) + 2 * (b : ℤ)) := by
  simp only [encode, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [difference_row_sum_zero a b u hu]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

theorem encode_column_margin (a b : ℕ) (k : ℤ) (X u : Array)
    (hu : ZeroBoundary a b u) (j : ℕ) :
    (∑ i ∈ Finset.range a, encode k X u i j) =
      k * ((∑ i ∈ Finset.range a, X i j) + 2 * (a : ℤ)) := by
  simp only [encode, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [difference_column_sum_zero a b u hu]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  ring

/-- Divisibility of the full row/column sums forces the last prefixSum
boundaries to have zero residue. The array hypotheses include all rows and
columns; a finite-table adapter must supply its chosen outside extension. -/
lemma residue_zero_boundary_of_divisible_margins (a b : ℕ) (k : ℤ) (Z : Array)
    (hrow : ∀ i, k ∣ ∑ j ∈ Finset.range b, Z i j)
    (hcol : ∀ j, k ∣ ∑ i ∈ Finset.range a, Z i j) :
    ZeroBoundary a b (residue k Z) := by
  refine ⟨residue_zero_axes k Z, ?_, ?_⟩
  · intro q
    unfold residue
    apply Int.emod_eq_zero_of_dvd
    unfold prefixSum
    rw [Finset.sum_comm]
    exact Finset.dvd_sum (fun j _ => hcol j)
  · intro p
    unfold residue
    apply Int.emod_eq_zero_of_dvd
    unfold prefixSum
    exact Finset.dvd_sum (fun i _ => hrow i)

theorem decode_row_margin (a b : ℕ) (k : ℤ) (hk : k ≠ 0) (Z : Array)
    (hu : ZeroBoundary a b (residue k Z)) (i : ℕ) :
    (∑ j ∈ Finset.range b, decode k Z i j) =
      (∑ j ∈ Finset.range b, Z i j) / k - 2 * (b : ℤ) := by
  have h := encode_row_margin a b k (decode k Z) (residue k Z) hu i
  rw [encode_decode] at h
  rw [h, Int.mul_ediv_cancel_left _ hk]
  ring

theorem decode_column_margin (a b : ℕ) (k : ℤ) (hk : k ≠ 0) (Z : Array)
    (hu : ZeroBoundary a b (residue k Z)) (j : ℕ) :
    (∑ i ∈ Finset.range a, decode k Z i j) =
      (∑ i ∈ Finset.range a, Z i j) / k - 2 * (a : ℤ) := by
  have h := encode_column_margin a b k (decode k Z) (residue k Z) hu j
  rw [encode_decode] at h
  rw [h, Int.mul_ediv_cancel_left _ hk]
  ring

theorem accepted_fine_entry_at_least_two (k : ℤ) (hk : 0 < k) (Z : Array)
    (i j : ℕ) (hX : 0 ≤ decode k Z i j) : 2 ≤ Z i j := by
  have h := encode_entry_at_least_two k hk (decode k Z) (residue k Z)
    (residue_bounded k hk Z) i j hX
  simpa only [encode_decode] using h

/-- Prefix digits compatible with the universal codec; finite-grid digit
families below supply the stronger full rectangle boundary. -/
def OffsetDigits (k : ℤ) := {u : Array // ZeroAxes u ∧ BoundedDigits k u}

/-- Exact integer codec, independently of any table feasibility predicate.
The offset family here is infinite; no finite cardinality claim follows. -/
def codecEquiv (k : ℤ) (hk : 0 < k) : (Array × OffsetDigits k) ≃ Array where
  toFun x := encode k x.1 x.2.val
  invFun Z := (decode k Z, ⟨residue k Z, residue_zero_axes k Z, residue_bounded k hk Z⟩)
  left_inv x := by
    apply Prod.ext
    · exact decode_encode k hk x.1 x.2.val x.2.property.1 x.2.property.2
    · apply Subtype.ext
      exact residue_encode k x.1 x.2.val x.2.property.1 x.2.property.2
  right_inv Z := encode_decode k Z

/-- Exactly (a-1)(b-1) finite digits; offsets are zero on the whole boundary. -/
abbrev FiniteDigits (a b k : ℕ) := Fin (a - 1) → Fin (b - 1) → Fin k

def finiteOffsets (a b k : ℕ) (digits : FiniteDigits a b k) : Array := fun p q =>
  if h : 0 < p ∧ p < a ∧ 0 < q ∧ q < b then
    (digits ⟨p - 1, by omega⟩ ⟨q - 1, by omega⟩).val
  else 0

lemma finiteOffsets_zero_boundary (a b k : ℕ) (digits : FiniteDigits a b k) :
    ZeroBoundary a b (finiteOffsets a b k digits) := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro q
    simp [finiteOffsets]
  · intro p
    simp [finiteOffsets]
  · intro q
    simp [finiteOffsets]
  · intro p
    simp [finiteOffsets]

lemma finiteOffsets_bounded (a b k : ℕ) (hk : 0 < k) (digits : FiniteDigits a b k) :
    BoundedDigits (k : ℤ) (finiteOffsets a b k digits) := by
  intro p q
  unfold finiteOffsets
  split_ifs with h
  · constructor
    · exact_mod_cast Nat.zero_le _
    · exact_mod_cast (digits ⟨p - 1, by omega⟩ ⟨q - 1, by omega⟩).isLt
  · constructor
    · omega
    · exact_mod_cast hk

/-- A finite digit family gives an exact decoded original array and strictly
positive encoded entries wherever the original entries are nonnegative. -/
theorem finite_encode_decode (a b k : ℕ) (hk : 0 < k) (X : Array)
    (digits : FiniteDigits a b k) :
    decode (k : ℤ) (encode (k : ℤ) X (finiteOffsets a b k digits)) = X := by
  exact decode_encode _ (by exact_mod_cast hk) X _
    (finiteOffsets_zero_boundary a b k digits).1 (finiteOffsets_bounded a b k hk digits)

lemma finiteOffsets_apply (a b k : ℕ) (digits : FiniteDigits a b k)
    (i : Fin (a - 1)) (j : Fin (b - 1)) :
    finiteOffsets a b k digits (i.val + 1) (j.val + 1) = (digits i j).val := by
  have hi := i.isLt
  have hj := j.isLt
  have h : 0 < i.val + 1 ∧ i.val + 1 < a ∧ 0 < j.val + 1 ∧ j.val + 1 < b := by omega
  have heI : (⟨i.val + 1 - 1, by omega⟩ : Fin (a - 1)) = i := by
    apply Fin.ext
    change i.val + 1 - 1 = i.val
    omega
  have heJ : (⟨j.val + 1 - 1, by omega⟩ : Fin (b - 1)) = j := by
    apply Fin.ext
    change j.val + 1 - 1 = j.val
    omega
  simp only [finiteOffsets, dite_eq_left h, heI, heJ]

lemma finiteOffsets_injective (a b k : ℕ) : Function.Injective (finiteOffsets a b k) := by
  intro u v h
  funext i j
  apply Fin.ext
  have hcell := congrFun (congrFun h (i.val + 1)) (j.val + 1)
  rw [finiteOffsets_apply, finiteOffsets_apply] at hcell
  exact_mod_cast hcell

theorem finiteEncode_injective (a b k : ℕ) (hk : 0 < k) (X : Array) :
    Function.Injective (fun digits : FiniteDigits a b k =>
      encode (k : ℤ) X (finiteOffsets a b k digits)) := by
  intro u v h
  have hres := congrArg (residue (k : ℤ)) h
  rw [residue_encode _ X _ (finiteOffsets_zero_boundary a b k u).1
      (finiteOffsets_bounded a b k hk u),
    residue_encode _ X _ (finiteOffsets_zero_boundary a b k v).1
      (finiteOffsets_bounded a b k hk v)] at hres
  exact finiteOffsets_injective a b k hres

lemma finiteDigits_card (a b k : ℕ) :
    Fintype.card (FiniteDigits a b k) = k ^ ((a - 1) * (b - 1)) := by
  simp only [FiniteDigits, Fintype.card_fun, Fintype.card_fin]
  rw [← pow_mul, Nat.mul_comm]

/-- The image of the constructed finite offset family has exactly k^e
members. This counts that image, not the entire accepted fine-table fibre. -/
theorem encodedFamily_card (a b k : ℕ) (hk : 0 < k) (X : Array) :
    Nat.card (Set.range (fun digits : FiniteDigits a b k =>
      encode (k : ℤ) X (finiteOffsets a b k digits))) = k ^ ((a - 1) * (b - 1)) := by
  rw [← Nat.card_congr (Equiv.ofInjective _ (finiteEncode_injective a b k hk X))]
  rw [Nat.card_eq_fintype_card]
  exact finiteDigits_card a b k

end Math115.LatticeCompletion
