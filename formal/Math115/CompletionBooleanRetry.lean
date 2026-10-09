import Math115.LatticeCompletionLaw
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordRejection

/-!
# Computable bounded retry from fresh finite Boolean words

The data-producing maps below are ordinary computable definitions. The
rational laws and their proofs are noncomputable descriptions of those
maps. A supplied fine-table draw consumes one fixed-width word; retry uses
one disjoint word per attempt and preserves the original fallback if all
attempts reject. This module supplies no machine-cost bound for the codec.
-/

namespace Math115.CompletionBooleanRetry

open OAI.ContingencyTables FirstSuccess ResidualMixture FairBits
open LatticeCompletionFinite
open scoped BigOperators

/-- Structural first-success execution; rejection alone advances the next
fresh word. An accepted fallback-valued result is still a success. -/
def retryWords {A : Type*} {q : ℕ} (f : (Fin q → Bool) → Option A) (fallback : A) :
    (J : ℕ) → (Fin J → Fin q → Bool) → A
  | 0, _ => fallback
  | J + 1, words =>
      match f (words 0) with
      | some x => x
      | none => retryWords f fallback J (Fin.tail words)

/-- A flat Boolean word is partitioned into successive width-q words. The
bijection also covers q=0 and J=0. -/
def wordBankEquiv (q J : ℕ) : (Fin (J * q) → Bool) ≃ (Fin J → Fin q → Bool) where
  toFun bits i j := bits (finProdFinEquiv (i, j))
  invFun words p := words (finProdFinEquiv.symm p).1 (finProdFinEquiv.symm p).2
  left_inv bits := by
    funext p
    change bits (finProdFinEquiv (finProdFinEquiv.symm p)) = bits p
    rw [Equiv.apply_symm_apply]
  right_inv words := by
    funext i j
    simp only [Equiv.symm_apply_apply]

def flatRetry {A : Type*} {q : ℕ} (f : (Fin q → Bool) → Option A) (fallback : A)
    (J : ℕ) (bits : Fin (J * q) → Bool) : A :=
  retryWords f fallback J (wordBankEquiv q J bits)

/-- Computational zero extension, used solely on bounded table prefixes. -/
def zeroExtend {a b : ℕ} (Z : Fin a → Fin b → ℕ) : ℕ → ℕ → ℤ := fun i j =>
  if h : i < a ∧ j < b then Z ⟨i, h.1⟩ ⟨j, h.2⟩ else 0

def prefixInt {a b : ℕ} (Z : Fin a → Fin b → ℕ) (p q : ℕ) : ℤ :=
  ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, zeroExtend Z i j

/-- The signed decoder performs integer division before mixed differences;
negative entries are tested before conversion to natural numbers. -/
def decodeCells {a b : ℕ} (k : ℕ) (Z : Fin a → Fin b → ℕ) : Grid a b := fun i j =>
  prefixInt Z (i.val + 1) (j.val + 1) / (k : ℤ) -
    prefixInt Z i.val (j.val + 1) / (k : ℤ) -
    prefixInt Z (i.val + 1) j.val / (k : ℤ) +
    prefixInt Z i.val j.val / (k : ℤ) - 2

def acceptedCells {a b : ℕ} (k : ℕ) (Z : Fin a → Fin b → ℕ) : Prop :=
  ∀ i j, 0 ≤ decodeCells k Z i j

instance acceptedCells_decidable {a b : ℕ} (k : ℕ) (Z : Fin a → Fin b → ℕ) :
    Decidable (acceptedCells k Z) := inferInstanceAs (Decidable (∀ i j, 0 ≤ decodeCells k Z i j))

/-- A raw computable decoder for matrix-valued program interfaces. -/
def rawTrial {a b : ℕ} (k : ℕ) (Z : Fin a → Fin b → ℕ) : Option (Fin a → Fin b → ℕ) :=
  if acceptedCells k Z then some (fun i j => (decodeCells k Z i j).toNat) else none

lemma prefixInt_eq_bounded_prefix {a b : ℕ} (k : ℕ) (Z : Fin a → Fin b → ℕ)
    (p q : ℕ) (hp : p ≤ a) (hq : q ≤ b) :
    prefixInt Z p q = LatticeCompletion.prefixSum (extend (2 * (k : ℤ)) (intGrid Z)) p q := by
  unfold prefixInt LatticeCompletion.prefixSum
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have h : i < a ∧ j < b :=
    ⟨lt_of_lt_of_le (Finset.mem_range.mp hi) hp, lt_of_lt_of_le (Finset.mem_range.mp hj) hq⟩
  simp [zeroExtend, extend, intGrid, h]

lemma decodeCells_eq {a b : ℕ} (k : ℕ) (Z : Fin a → Fin b → ℕ) :
    decodeCells k Z = decodeGrid k (intGrid Z) := by
  funext i j
  have hi := i.isLt
  have hj := j.isLt
  unfold decodeCells decodeGrid restrict LatticeCompletion.decode LatticeCompletion.difference
  rw [prefixInt_eq_bounded_prefix k Z _ _ (by omega) (by omega),
    prefixInt_eq_bounded_prefix k Z _ _ (by omega) (by omega),
    prefixInt_eq_bounded_prefix k Z _ _ (by omega) (by omega),
    prefixInt_eq_bounded_prefix k Z _ _ (by omega) (by omega)]

lemma acceptedCells_iff {a b : ℕ} (k : ℕ) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (Z : FineTable k R P) : acceptedCells k Z.val ↔ Accepted k R P Z := by
  simp only [acceptedCells, Accepted, decodeCells_eq]

/-- The table-valued implementation constructs its margin proof only after
the executable finite-cell nonnegativity test passes. -/
def tableTrial {a b : ℕ} (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (Z : FineTable k R P) : Option (Table R P) :=
  if h : acceptedCells k Z.val then
    some ⟨fun i j => (decodeCells k Z.val i j).toNat, by
      have ha : Accepted k R P Z := (acceptedCells_iff k R P Z).mp h
      have hp := (decodeAccepted k hk R P ⟨Z, ha⟩).property
      change HasMargins (LatticeCompletionFinite.natGrid (decodeGrid k (intGrid Z.val))) R P at hp
      change HasMargins (LatticeCompletionFinite.natGrid (decodeCells k Z.val)) R P
      rw [decodeCells_eq]
      exact hp⟩
  else none

/-- Computational interior digits, with zero errors on the complete boundary. -/
def digitOffset (a b k : ℕ) (u : LatticeCompletion.FiniteDigits a b k) : ℕ → ℕ → ℤ := fun p q =>
  if h : 0 < p ∧ p < a ∧ 0 < q ∧ q < b then
    (u ⟨p - 1, by omega⟩ ⟨q - 1, by omega⟩).val
  else 0

def signedEncodeCells {a b : ℕ} (k : ℕ) (X : Fin a → Fin b → ℕ)
    (u : LatticeCompletion.FiniteDigits a b k) : Grid a b := fun i j =>
  (k : ℤ) * ((X i j : ℤ) + 2) +
    (digitOffset a b k u (i.val + 1) (j.val + 1) -
      digitOffset a b k u i.val (j.val + 1) -
      digitOffset a b k u (i.val + 1) j.val + digitOffset a b k u i.val j.val)

def encodeCells {a b : ℕ} (k : ℕ) (X : Fin a → Fin b → ℕ)
    (u : LatticeCompletion.FiniteDigits a b k) : Fin a → Fin b → ℕ :=
  fun i j => (signedEncodeCells k X u i j).toNat

lemma digitOffset_eq (a b k : ℕ) (u : LatticeCompletion.FiniteDigits a b k) :
    digitOffset a b k u = LatticeCompletion.finiteOffsets a b k u := rfl

lemma signedEncodeCells_eq {a b : ℕ} (k : ℕ) (X : Fin a → Fin b → ℕ)
    (u : LatticeCompletion.FiniteDigits a b k) :
    signedEncodeCells k X u = encodeGrid k (intGrid X) u := by
  funext i j
  simp only [signedEncodeCells, digitOffset_eq, encodeGrid, restrict,
    LatticeCompletion.encode, LatticeCompletion.difference, extend_inside, intGrid]

lemma encodeCells_eq_encodeTable_value {a b : ℕ} (k : ℕ) (hk : 0 < k)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (X : Table R P)
    (u : LatticeCompletion.FiniteDigits a b k) :
    encodeCells k X.val u = (encodeTable k hk R P X u).val := by
  change (fun i j => (signedEncodeCells k X.val u i j).toNat) =
    natGrid (encodeGrid k (intGrid X.val) u)
  rw [signedEncodeCells_eq]
  rfl

noncomputable section
open scoped Classical

lemma tableTrial_eq {a b : ℕ} (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (Z : FineTable k R P) : tableTrial k hk R P Z = LatticeCompletionLaw.trial k hk R P Z := by
  by_cases h : Accepted k R P Z
  · have ha : acceptedCells k Z.val := (acceptedCells_iff k R P Z).mpr h
    simp only [tableTrial, LatticeCompletionLaw.trial, dite_eq_left ha, dite_eq_left h]
    congr 1
    apply Subtype.ext
    funext i j
    simp only [decodeCells_eq, decodeAccepted, natGrid]
  · have ha : ¬ acceptedCells k Z.val := fun ha => h ((acceptedCells_iff k R P Z).mp ha)
    simp only [tableTrial, LatticeCompletionLaw.trial, dite_eq_right ha, dite_eq_right h]

lemma rawTrial_eq_tableTrial_value {a b : ℕ} (k : ℕ) (hk : 0 < k)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (Z : FineTable k R P) :
    rawTrial k Z.val = (tableTrial k hk R P Z).map Subtype.val := by
  unfold rawTrial tableTrial
  split_ifs <;> rfl

lemma retryWords_eq_wordRetry {A : Type*} {q : ℕ} (f : (Fin q → Bool) → Option A)
    (fallback : A) (J : ℕ) (words : Fin J → Fin q → Bool) :
    retryWords f fallback J words = FirstSuccess.wordRetry f fallback J words := by
  induction J with
  | zero => rfl
  | succ J ih =>
    simp only [retryWords, FirstSuccess.wordRetry]
    cases f (words 0) with
    | some x => rfl
    | none => exact ih (Fin.tail words)

/-- Exact law of the executable rectangular-word retry map. Uniformity of
the whole Boolean bank supplies independent fresh words in trial order. -/
theorem retryWords_law {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    {q : ℕ} (draw : (Fin q → Bool) → S) (trial : S → Option A) (fallback : A) (J : ℕ) :
    mapLaw (uniformLaw (α := Fin J → Fin q → Bool))
      (retryWords (fun word => trial (draw word)) fallback J) =
      retryLaw (mapLaw (uniformLaw (α := Fin q → Bool)) draw) trial fallback J := by
  have heq : retryWords (fun word => trial (draw word)) fallback J =
      FirstSuccess.wordRetry (fun word => trial (draw word)) fallback J := by
    funext words
    exact retryWords_eq_wordRetry _ _ _ _
  rw [heq]
  change FirstSuccess.wordRetryLaw _ _ _ = _
  rw [FirstSuccess.wordRetryLaw_eq, FirstSuccess.retryLaw_map]

/-- The flat source consumes exactly J*q bits, partitioned bijectively into
fresh words. No rejected trial's bits are reused. -/
theorem flatRetry_law {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]
    {q : ℕ} (draw : (Fin q → Bool) → S) (trial : S → Option A) (fallback : A) (J : ℕ) :
    mapLaw (uniformLaw (α := Fin (J * q) → Bool))
      (flatRetry (fun word => trial (draw word)) fallback J) =
      retryLaw (mapLaw (uniformLaw (α := Fin q → Bool)) draw) trial fallback J := by
  change mapLaw (uniformLaw (α := Fin (J * q) → Bool))
    (fun bits => retryWords (fun word => trial (draw word)) fallback J (wordBankEquiv q J bits)) = _
  rw [← map_equiv (wordBankEquiv q J), uniform_equiv]
  exact retryWords_law draw trial fallback J

/-- A supplied fine Boolean sampler and executable integer decoder realize
exactly the completion law already used by the retry accuracy theorem. -/
theorem completion_flat_law {a b q : ℕ} (k : ℕ) (hk : 0 < k)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (draw : (Fin q → Bool) → FineTable k R P)
    (fallback : Table R P) (J : ℕ) :
    mapLaw (uniformLaw (α := Fin (J * q) → Bool))
      (flatRetry (fun word => tableTrial k hk R P (draw word)) fallback J) =
      retryLaw (mapLaw (uniformLaw (α := Fin q → Bool)) draw)
        (LatticeCompletionLaw.trial k hk R P) fallback J := by
  simp only [tableTrial_eq]
  exact flatRetry_law draw _ fallback J

end

end Math115.CompletionBooleanRetry
