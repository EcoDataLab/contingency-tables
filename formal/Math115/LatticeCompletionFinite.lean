/-
SPDX-License-Identifier: Apache-2.0
Full finite accepted-fibre equivalence for the actual upstream Table model.
Original arrays extend by zero and fine arrays extend by 2k.
No geometric acceptance, oracle realization, or machine-cost claim is made.
-/
import Math115.LatticeCompletion
import OAI.Combinatorics.ContingencyTables.Model

namespace Math115.LatticeCompletionFinite
open LatticeCompletion OAI.ContingencyTables
open scoped BigOperators
noncomputable section

abbrev Grid (a b : ℕ) := Fin a → Fin b → ℤ

def extend {a b : ℕ} (c : ℤ) (X : Grid a b) : Array := fun i j =>
  if h : i < a ∧ j < b then X ⟨i, h.1⟩ ⟨j, h.2⟩ else c

def restrict {a b : ℕ} (X : Array) : Grid a b := fun i j => X i.val j.val

@[simp] lemma extend_inside {a b : ℕ} (c : ℤ) (X : Grid a b) (i : Fin a) (j : Fin b) :
    extend c X i.val j.val = X i j := by simp [extend, i.isLt, j.isLt]

lemma extend_outside {a b : ℕ} (c : ℤ) (X : Grid a b) (i j : ℕ)
    (h : a ≤ i ∨ b ≤ j) : extend c X i j = c := by
  simp [extend, show ¬(i < a ∧ j < b) by omega]

lemma extend_injective {a b : ℕ} (c : ℤ) : Function.Injective (@extend a b c) := by
  intro X Y h
  funext i j
  simpa using congrFun (congrFun h i.val) j.val

lemma range_sum_extend_row {a b : ℕ} (c : ℤ) (X : Grid a b) (i : Fin a) :
    (∑ j ∈ Finset.range b, extend c X i.val j) = ∑ j : Fin b, X i j := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp

lemma range_sum_extend_column {a b : ℕ} (c : ℤ) (X : Grid a b) (j : Fin b) :
    (∑ i ∈ Finset.range a, extend c X i j.val) = ∑ i : Fin a, X i j := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp

lemma offsets_difference_outside (a b k : ℕ) (u : FiniteDigits a b k) (i j : ℕ)
    (h : a ≤ i ∨ b ≤ j) : difference (finiteOffsets a b k u) i j = 0 := by
  have h00 : ¬(0 < i ∧ i < a ∧ 0 < j ∧ j < b) := by omega
  have h01 : ¬(0 < i ∧ i < a ∧ 0 < j + 1 ∧ j + 1 < b) := by omega
  have h10 : ¬(0 < i + 1 ∧ i + 1 < a ∧ 0 < j ∧ j < b) := by omega
  have h11 : ¬(0 < i + 1 ∧ i + 1 < a ∧ 0 < j + 1 ∧ j + 1 < b) := by omega
  simp only [difference, finiteOffsets, dite_eq_right h00, dite_eq_right h01, dite_eq_right h10, dite_eq_right h11]
  ring

def encodeGrid {a b : ℕ} (k : ℕ) (X : Grid a b) (u : FiniteDigits a b k) : Grid a b :=
  restrict (encode (k : ℤ) (extend 0 X) (finiteOffsets a b k u))

def decodeGrid {a b : ℕ} (k : ℕ) (Z : Grid a b) : Grid a b :=
  restrict (decode (k : ℤ) (extend (2 * (k : ℤ)) Z))

lemma extend_encodeGrid {a b : ℕ} (k : ℕ) (X : Grid a b) (u : FiniteDigits a b k) :
    extend (2 * (k : ℤ)) (encodeGrid k X u) =
      encode (k : ℤ) (extend 0 X) (finiteOffsets a b k u) := by
  funext i j
  by_cases h : i < a ∧ j < b
  · simp only [extend, dite_eq_left h, encodeGrid, restrict]
  · have hout : a ≤ i ∨ b ≤ j := by omega
    rw [extend_outside _ _ _ _ hout]
    simp [encode, extend_outside _ X _ _ hout, offsets_difference_outside _ _ _ _ _ _ hout]
    ring

lemma fine_row_divisible {a b : ℕ} (k : ℕ) (Z : Grid a b)
    (hrow : ∀ i : Fin a, (k : ℤ) ∣ ∑ j : Fin b, Z i j) (i : ℕ) :
    (k : ℤ) ∣ ∑ j ∈ Finset.range b, extend (2 * (k : ℤ)) Z i j := by
  by_cases hi : i < a
  · rw [range_sum_extend_row _ Z ⟨i, hi⟩]
    exact hrow ⟨i, hi⟩
  · have he : ∀ j, extend (2 * (k : ℤ)) Z i j = 2 * (k : ℤ) :=
      fun j => extend_outside _ _ _ _ (Or.inl (by omega))
    simp only [he, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

lemma fine_column_divisible {a b : ℕ} (k : ℕ) (Z : Grid a b)
    (hcol : ∀ j : Fin b, (k : ℤ) ∣ ∑ i : Fin a, Z i j) (j : ℕ) :
    (k : ℤ) ∣ ∑ i ∈ Finset.range a, extend (2 * (k : ℤ)) Z i j := by
  by_cases hj : j < b
  · rw [range_sum_extend_column _ Z ⟨j, hj⟩]
    exact hcol ⟨j, hj⟩
  · have he : ∀ i, extend (2 * (k : ℤ)) Z i j = 2 * (k : ℤ) :=
      fun i => extend_outside _ _ _ _ (Or.inr (by omega))
    simp only [he, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact dvd_mul_of_dvd_right (dvd_mul_left _ _) _

/-- Entire outside strips, not just the last grid boundary, have zero residue. -/
lemma fine_residue_zero_strips {a b : ℕ} (k : ℕ) (Z : Grid a b)
    (hrow : ∀ i : Fin a, (k : ℤ) ∣ ∑ j : Fin b, Z i j)
    (hcol : ∀ j : Fin b, (k : ℤ) ∣ ∑ i : Fin a, Z i j)
    (p q : ℕ) (hout : a ≤ p ∨ b ≤ q) :
    residue (k : ℤ) (extend (2 * (k : ℤ)) Z) p q = 0 := by
  apply Int.emod_eq_zero_of_dvd
  rcases hout with hp | hq
  · have hc : ∀ j, (k : ℤ) ∣ ∑ i ∈ Finset.range p, extend (2 * (k : ℤ)) Z i j := by
      intro j
      induction p, hp using Nat.le_induction with
      | base => exact fine_column_divisible k Z hcol j
      | succ p hp ih =>
        rw [Finset.sum_range_succ]
        apply dvd_add ih
        rw [extend_outside _ _ _ _ (Or.inl hp)]
        exact dvd_mul_left _ _
    unfold prefixSum
    rw [Finset.sum_comm]
    exact Finset.dvd_sum (fun j _ => hc j)
  · have hr : ∀ i, (k : ℤ) ∣ ∑ j ∈ Finset.range q, extend (2 * (k : ℤ)) Z i j := by
      intro i
      induction q, hq using Nat.le_induction with
      | base => exact fine_row_divisible k Z hrow i
      | succ q hq ih =>
        rw [Finset.sum_range_succ]
        apply dvd_add ih
        rw [extend_outside _ _ _ _ (Or.inr hq)]
        exact dvd_mul_left _ _
    exact Finset.dvd_sum (fun i _ => hr i)


def recoveredDigits {a b : ℕ} (k : ℕ) (hk : 0 < k) (Z : Grid a b) :
    FiniteDigits a b k := fun i j =>
  ⟨(residue (k : ℤ) (extend (2 * (k : ℤ)) Z) (i.val + 1) (j.val + 1)).toNat, by
    have h := residue_bounded (k : ℤ) (by exact_mod_cast hk)
      (extend (2 * (k : ℤ)) Z) (i.val + 1) (j.val + 1)
    omega⟩

lemma recoveredDigits_val {a b : ℕ} (k : ℕ) (hk : 0 < k) (Z : Grid a b)
    (i : Fin (a - 1)) (j : Fin (b - 1)) :
    ((recoveredDigits k hk Z i j).val : ℤ) =
      residue (k : ℤ) (extend (2 * (k : ℤ)) Z) (i.val + 1) (j.val + 1) := by
  apply Int.toNat_of_nonneg
  exact (residue_bounded _ (by exact_mod_cast hk) _ _ _).1

lemma residue_eq_finiteOffsets {a b : ℕ} (k : ℕ) (hk : 0 < k) (Z : Grid a b)
    (hrow : ∀ i : Fin a, (k : ℤ) ∣ ∑ j : Fin b, Z i j)
    (hcol : ∀ j : Fin b, (k : ℤ) ∣ ∑ i : Fin a, Z i j) :
    residue (k : ℤ) (extend (2 * (k : ℤ)) Z) =
      finiteOffsets a b k (recoveredDigits k hk Z) := by
  funext p q
  by_cases h : 0 < p ∧ p < a ∧ 0 < q ∧ q < b
  · simp only [finiteOffsets, dite_eq_left h, recoveredDigits_val]
    congr 2 <;> omega
  · rw [finiteOffsets, dite_eq_right h]
    by_cases hp : p = 0
    · subst p
      exact (residue_zero_axes _ _).1 q
    by_cases hq : q = 0
    · subst q
      exact (residue_zero_axes _ _).2 p
    exact fine_residue_zero_strips k Z hrow hcol p q (by omega)

lemma extend_decodeGrid {a b : ℕ} (k : ℕ) (hk : 0 < k) (Z : Grid a b)
    (hrow : ∀ i : Fin a, (k : ℤ) ∣ ∑ j : Fin b, Z i j)
    (hcol : ∀ j : Fin b, (k : ℤ) ∣ ∑ i : Fin a, Z i j) :
    extend 0 (decodeGrid k Z) = decode (k : ℤ) (extend (2 * (k : ℤ)) Z) := by
  funext i j
  by_cases h : i < a ∧ j < b
  · simp only [extend, dite_eq_left h, decodeGrid, restrict]
  · have hout : a ≤ i ∨ b ≤ j := by omega
    rw [extend_outside _ _ _ _ hout]
    have hrec := congrFun (congrFun (encode_decode (k : ℤ) (extend (2 * (k : ℤ)) Z)) i) j
    unfold encode at hrec
    rw [residue_eq_finiteOffsets k hk Z hrow hcol,
      offsets_difference_outside _ _ _ _ _ _ hout, extend_outside _ _ _ _ hout] at hrec
    have hk' : 0 < (k : ℤ) := by exact_mod_cast hk
    have hmul : (k : ℤ) * decode (k : ℤ) (extend (2 * (k : ℤ)) Z) i j = 0 := by
      nlinarith only [hrec]
    exact ((mul_eq_zero.mp hmul).resolve_left (ne_of_gt hk')).symm

lemma decodeGrid_encodeGrid {a b : ℕ} (k : ℕ) (hk : 0 < k)
    (X : Grid a b) (u : FiniteDigits a b k) : decodeGrid k (encodeGrid k X u) = X := by
  unfold decodeGrid
  rw [extend_encodeGrid, finite_encode_decode _ _ _ hk]
  funext i j
  exact extend_inside 0 X i j

lemma recoveredDigits_encodeGrid {a b : ℕ} (k : ℕ) (hk : 0 < k)
    (X : Grid a b) (u : FiniteDigits a b k) : recoveredDigits k hk (encodeGrid k X u) = u := by
  funext i j
  apply Fin.ext
  have hres : residue (k : ℤ) (extend (2 * (k : ℤ)) (encodeGrid k X u)) =
      finiteOffsets a b k u := by
    rw [extend_encodeGrid]
    exact residue_encode _ _ _ (finiteOffsets_zero_boundary _ _ _ u).1
      (finiteOffsets_bounded _ _ _ hk u)
  have h := congrFun (congrFun hres (i.val + 1)) (j.val + 1)
  rw [← recoveredDigits_val k hk (encodeGrid k X u), finiteOffsets_apply] at h
  exact_mod_cast h

lemma encodeGrid_decodeGrid {a b : ℕ} (k : ℕ) (hk : 0 < k) (Z : Grid a b)
    (hrow : ∀ i : Fin a, (k : ℤ) ∣ ∑ j : Fin b, Z i j)
    (hcol : ∀ j : Fin b, (k : ℤ) ∣ ∑ i : Fin a, Z i j) :
    encodeGrid k (decodeGrid k Z) (recoveredDigits k hk Z) = Z := by
  unfold encodeGrid
  rw [extend_decodeGrid k hk Z hrow hcol, ← residue_eq_finiteOffsets k hk Z hrow hcol,
    encode_decode]
  funext i j
  exact extend_inside _ Z i j

lemma encodeGrid_row {a b : ℕ} (k : ℕ) (X : Grid a b) (u : FiniteDigits a b k) (i : Fin a) :
    (∑ j : Fin b, encodeGrid k X u i j) = (k : ℤ) * ((∑ j : Fin b, X i j) + 2 * (b : ℤ)) := by
  rw [← range_sum_extend_row (2 * (k : ℤ)), extend_encodeGrid]
  rw [encode_row_margin a b (k : ℤ) (extend 0 X) _ (finiteOffsets_zero_boundary _ _ _ u)]
  rw [range_sum_extend_row]

lemma encodeGrid_column {a b : ℕ} (k : ℕ) (X : Grid a b) (u : FiniteDigits a b k) (j : Fin b) :
    (∑ i : Fin a, encodeGrid k X u i j) = (k : ℤ) * ((∑ i : Fin a, X i j) + 2 * (a : ℤ)) := by
  rw [← range_sum_extend_column (2 * (k : ℤ)), extend_encodeGrid]
  rw [encode_column_margin a b (k : ℤ) (extend 0 X) _ (finiteOffsets_zero_boundary _ _ _ u)]
  rw [range_sum_extend_column]

lemma encodeGrid_nonneg {a b : ℕ} (k : ℕ) (hk : 0 < k) (X : Grid a b)
    (hX : ∀ i j, 0 ≤ X i j) (u : FiniteDigits a b k) (i : Fin a) (j : Fin b) :
    0 ≤ encodeGrid k X u i j := by
  apply le_trans (by norm_num : (0 : ℤ) ≤ 2)
  apply encode_entry_at_least_two _ (by exact_mod_cast hk) _ _
    (finiteOffsets_bounded _ _ _ hk u)
  simpa using hX i j

lemma decodeGrid_row {a b : ℕ} (k : ℕ) (hk : 0 < k) (Z : Grid a b)
    (hrow : ∀ i : Fin a, (k : ℤ) ∣ ∑ j : Fin b, Z i j)
    (hcol : ∀ j : Fin b, (k : ℤ) ∣ ∑ i : Fin a, Z i j) (i : Fin a) :
    (∑ j : Fin b, decodeGrid k Z i j) = (∑ j : Fin b, Z i j) / (k : ℤ) - 2 * (b : ℤ) := by
  rw [← range_sum_extend_row 0, extend_decodeGrid k hk Z hrow hcol]
  rw [decode_row_margin a b _ (by exact_mod_cast (ne_of_gt hk)) _
    (residue_zero_boundary_of_divisible_margins a b _ _
      (fine_row_divisible k Z hrow) (fine_column_divisible k Z hcol))]
  rw [range_sum_extend_row]

lemma decodeGrid_column {a b : ℕ} (k : ℕ) (hk : 0 < k) (Z : Grid a b)
    (hrow : ∀ i : Fin a, (k : ℤ) ∣ ∑ j : Fin b, Z i j)
    (hcol : ∀ j : Fin b, (k : ℤ) ∣ ∑ i : Fin a, Z i j) (j : Fin b) :
    (∑ i : Fin a, decodeGrid k Z i j) = (∑ i : Fin a, Z i j) / (k : ℤ) - 2 * (a : ℤ) := by
  rw [← range_sum_extend_column 0, extend_decodeGrid k hk Z hrow hcol]
  rw [decode_column_margin a b _ (by exact_mod_cast (ne_of_gt hk)) _
    (residue_zero_boundary_of_divisible_margins a b _ _
      (fine_row_divisible k Z hrow) (fine_column_divisible k Z hcol))]
  rw [range_sum_extend_column]


def intGrid {a b : ℕ} (X : Fin a → Fin b → ℕ) : Grid a b := fun i j => X i j

def natGrid {a b : ℕ} (X : Grid a b) : Fin a → Fin b → ℕ := fun i j => (X i j).toNat

@[simp] lemma natGrid_intGrid {a b : ℕ} (X : Fin a → Fin b → ℕ) : natGrid (intGrid X) = X := by
  funext i j
  simp [natGrid, intGrid]

lemma intGrid_natGrid {a b : ℕ} (X : Grid a b) (hX : ∀ i j, 0 ≤ X i j) :
    intGrid (natGrid X) = X := by
  funext i j
  exact Int.toNat_of_nonneg (hX i j)

lemma intGrid_row {a b : ℕ} (R : Fin a → ℕ) (P : Fin b → ℕ) (X : Table R P) (i : Fin a) :
    (∑ j : Fin b, intGrid X.val i j) = (R i : ℤ) := by
  change (∑ j : Fin b, (X.val i j : ℤ)) = (R i : ℤ)
  exact_mod_cast X.property.1 i

lemma intGrid_column {a b : ℕ} (R : Fin a → ℕ) (P : Fin b → ℕ) (X : Table R P) (j : Fin b) :
    (∑ i : Fin a, intGrid X.val i j) = (P j : ℤ) := by
  change (∑ i : Fin a, (X.val i j : ℤ)) = (P j : ℤ)
  exact_mod_cast X.property.2 j

lemma natGrid_hasMargins {a b : ℕ} (R : Fin a → ℕ) (P : Fin b → ℕ) (X : Grid a b)
    (hX : ∀ i j, 0 ≤ X i j)
    (hrow : ∀ i : Fin a, (∑ j : Fin b, X i j) = (R i : ℤ))
    (hcol : ∀ j : Fin b, (∑ i : Fin a, X i j) = (P j : ℤ)) :
    HasMargins (natGrid X) R P := by
  constructor
  · intro i
    have h : (∑ j : Fin b, intGrid (natGrid X) i j) = (R i : ℤ) := by
      rw [intGrid_natGrid X hX]
      exact hrow i
    change (∑ j : Fin b, ((natGrid X i j : ℕ) : ℤ)) = (R i : ℤ) at h
    exact_mod_cast h
  · intro j
    have h : (∑ i : Fin a, intGrid (natGrid X) i j) = (P j : ℤ) := by
      rw [intGrid_natGrid X hX]
      exact hcol j
    change (∑ i : Fin a, ((natGrid X i j : ℕ) : ℤ)) = (P j : ℤ) at h
    exact_mod_cast h

/-- Exact dilation and two added units per incident cell. -/
def fineMargin {n : ℕ} (k m : ℕ) (R : Fin n → ℕ) : Fin n → ℕ := fun i => k * (R i + 2 * m)

abbrev FineTable {a b : ℕ} (k : ℕ) (R : Fin a → ℕ) (P : Fin b → ℕ) :=
  Table (fineMargin k b R) (fineMargin k a P)

lemma fineTable_row_divisible {a b : ℕ} (k : ℕ) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (Z : FineTable k R P) (i : Fin a) : (k : ℤ) ∣ ∑ j : Fin b, intGrid Z.val i j := by
  rw [intGrid_row]
  simp only [fineMargin, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  exact dvd_mul_right _ _

lemma fineTable_column_divisible {a b : ℕ} (k : ℕ) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (Z : FineTable k R P) (j : Fin b) : (k : ℤ) ∣ ∑ i : Fin a, intGrid Z.val i j := by
  rw [intGrid_column]
  simp only [fineMargin, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  exact dvd_mul_right _ _

/-- Acceptance means every actual decoded finite cell is nonnegative. -/
def Accepted {a b : ℕ} (k : ℕ) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (Z : FineTable k R P) : Prop := ∀ i j, 0 ≤ decodeGrid k (intGrid Z.val) i j

abbrev AcceptedFine {a b : ℕ} (k : ℕ) (R : Fin a → ℕ) (P : Fin b → ℕ) :=
  {Z : FineTable k R P // Accepted k R P Z}

/-- Encoding lands in the literal natural-valued upstream fine Table. -/
def encodeTable {a b : ℕ} (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (X : Table R P) (u : FiniteDigits a b k) : FineTable k R P :=
  ⟨natGrid (encodeGrid k (intGrid X.val) u),
    natGrid_hasMargins _ _ _
      (encodeGrid_nonneg k hk _ (fun i j => Int.natCast_nonneg _) u)
      (fun i => by
        rw [encodeGrid_row, intGrid_row]
        simp [fineMargin])
      (fun j => by
        rw [encodeGrid_column, intGrid_column]
        simp [fineMargin])⟩

lemma intGrid_encodeTable {a b : ℕ} (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (X : Table R P) (u : FiniteDigits a b k) :
    intGrid (encodeTable k hk R P X u).val = encodeGrid k (intGrid X.val) u := by
  apply intGrid_natGrid
  exact encodeGrid_nonneg k hk _ (fun i j => Int.natCast_nonneg _) u

lemma encodeTable_accepted {a b : ℕ} (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (X : Table R P) (u : FiniteDigits a b k) : Accepted k R P (encodeTable k hk R P X u) := by
  unfold Accepted
  rw [intGrid_encodeTable, decodeGrid_encodeGrid k hk]
  exact fun i j => Int.natCast_nonneg _

def encodeAccepted {a b : ℕ} (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (X : Table R P) (u : FiniteDigits a b k) : AcceptedFine k R P :=
  ⟨encodeTable k hk R P X u, encodeTable_accepted k hk R P X u⟩

/-- The inverse first coordinate is exactly the signed prefix decoder,
converted to Nat only after acceptance supplies nonnegativity. -/
def decodeAccepted {a b : ℕ} (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (Z : AcceptedFine k R P) : Table R P :=
  ⟨natGrid (decodeGrid k (intGrid Z.val.val)),
    natGrid_hasMargins _ _ _ Z.property
      (fun i => by
        rw [decodeGrid_row k hk _ (fineTable_row_divisible k R P Z.val)
          (fineTable_column_divisible k R P Z.val), intGrid_row]
        simp only [fineMargin, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
        rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast (ne_of_gt hk))]
        ring)
      (fun j => by
        rw [decodeGrid_column k hk _ (fineTable_row_divisible k R P Z.val)
          (fineTable_column_divisible k R P Z.val), intGrid_column]
        simp only [fineMargin, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
        rw [Int.mul_ediv_cancel_left _ (by exact_mod_cast (ne_of_gt hk))]
        ring)⟩

lemma intGrid_decodeAccepted {a b : ℕ} (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (Z : AcceptedFine k R P) :
    intGrid (decodeAccepted k hk R P Z).val = decodeGrid k (intGrid Z.val.val) := by
  exact intGrid_natGrid _ Z.property

lemma decodeAccepted_encodeAccepted {a b : ℕ} (k : ℕ) (hk : 0 < k)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (X : Table R P) (u : FiniteDigits a b k) :
    decodeAccepted k hk R P (encodeAccepted k hk R P X u) = X := by
  apply Subtype.ext
  change natGrid (decodeGrid k (intGrid (encodeTable k hk R P X u).val)) = X.val
  rw [intGrid_encodeTable, decodeGrid_encodeGrid k hk, natGrid_intGrid]

lemma encodeAccepted_decodeAccepted {a b : ℕ} (k : ℕ) (hk : 0 < k)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (Z : AcceptedFine k R P) :
    encodeAccepted k hk R P (decodeAccepted k hk R P Z)
      (recoveredDigits k hk (intGrid Z.val.val)) = Z := by
  apply Subtype.ext
  apply Subtype.ext
  change natGrid (encodeGrid k (intGrid (decodeAccepted k hk R P Z).val)
    (recoveredDigits k hk (intGrid Z.val.val))) = Z.val.val
  rw [intGrid_decodeAccepted, encodeGrid_decodeGrid k hk _
    (fineTable_row_divisible k R P Z.val) (fineTable_column_divisible k R P Z.val),
    natGrid_intGrid]

/-- Full coverage: every accepted fine table has a unique original table
and finite offset digit family. Valid for all a,b, including empty dimensions. -/
def acceptedEquiv {a b : ℕ} (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ) :
    (Table R P × FiniteDigits a b k) ≃ AcceptedFine k R P where
  toFun Xu := encodeAccepted k hk R P Xu.1 Xu.2
  invFun Z := (decodeAccepted k hk R P Z, recoveredDigits k hk (intGrid Z.val.val))
  left_inv Xu := by
    apply Prod.ext
    · exact decodeAccepted_encodeAccepted k hk R P Xu.1 Xu.2
    · change recoveredDigits k hk (intGrid (encodeTable k hk R P Xu.1 Xu.2).val) = Xu.2
      rw [intGrid_encodeTable, recoveredDigits_encodeGrid k hk]
  right_inv Z := encodeAccepted_decodeAccepted k hk R P Z

lemma accepted_card {a b : ℕ} (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ) :
    Nat.card (AcceptedFine k R P) = Nat.card (Table R P) * k ^ ((a - 1) * (b - 1)) := by
  rw [← Nat.card_congr (acceptedEquiv k hk R P), Nat.card_prod,
    Nat.card_eq_fintype_card (α := FiniteDigits a b k), finiteDigits_card]

/-- The complete accepted preimage of a fixed original table. -/
def fixedFiberEquiv {a b : ℕ} (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (X : Table R P) : FiniteDigits a b k ≃
      {Z : AcceptedFine k R P // decodeAccepted k hk R P Z = X} where
  toFun u := ⟨encodeAccepted k hk R P X u, decodeAccepted_encodeAccepted k hk R P X u⟩
  invFun Z := recoveredDigits k hk (intGrid Z.val.val.val)
  left_inv u := by
    change recoveredDigits k hk (intGrid (encodeTable k hk R P X u).val) = u
    rw [intGrid_encodeTable, recoveredDigits_encodeGrid k hk]
  right_inv Z := by
    apply Subtype.ext
    change encodeAccepted k hk R P X (recoveredDigits k hk (intGrid Z.val.val.val)) = Z.val
    exact (congrArg (fun W : Table R P => encodeAccepted k hk R P W
      (recoveredDigits k hk (intGrid Z.val.val.val))) Z.property.symm).trans
        (encodeAccepted_decodeAccepted k hk R P Z.val)

/-- Every actual original table has exactly k^((a-1)(b-1)) accepted fine
representations. This is the full preimage, not a constructed image count. -/
theorem fixedFiber_card {a b : ℕ} (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (X : Table R P) :
    Nat.card {Z : AcceptedFine k R P // decodeAccepted k hk R P Z = X} =
      k ^ ((a - 1) * (b - 1)) := by
  rw [← Nat.card_congr (fixedFiberEquiv k hk R P X), Nat.card_eq_fintype_card]
  exact finiteDigits_card a b k

end
end Math115.LatticeCompletionFinite
