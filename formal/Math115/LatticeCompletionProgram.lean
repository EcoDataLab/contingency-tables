/-
SPDX-License-Identifier: Apache-2.0
Binary list arithmetic for the prefixNat-floor completion decoder. The realizers
charge tree-machine work and encoded output size; no dense sampling or retry
runtime is asserted here. Every enumerated dimension comes from a supplied list.
-/
import Math115.CompletionBooleanRetry
import OAI.Combinatorics.ContingencyTables.Dense.DenseIntegerProgram
import OAI.Combinatorics.MatchingCount.Complexity.TreeChoiceCosts
import OAI.Combinatorics.MatchingCount.Machines.TreeSum
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostTactic

namespace Math115.LatticeCompletionProgram

open OAI OAI.ContingencyTables.DensePrograms
open OAI.MatchingFPRAS.TreeTyped
open scoped BigOperators

variable {a b : ℕ}

/-- A bounded prefixNat reads only input rows and input columns. -/
def rowPrefix (x : ℕ × List ℕ) : ℕ := (x.2.take x.1).sum

def rowPrefixRealizer : Realizer rowPrefix :=
  composition (composition (pair second first) takeFast) listSum

theorem polynomial_rowPrefix : PolynomialTime rowPrefixRealizer := by
  unfold rowPrefixRealizer rowPrefix
  have := polynomial_takeFast (A := ℕ)
  have := polynomial_listSum
  tree_cost

def prefixNat (x : MatrixCode × (ℕ × ℕ)) : ℕ :=
  ((x.1.take x.2.1).map (fun row => rowPrefix (x.2.2, row))).sum

def prefixRealizer : Realizer prefixNat :=
  composition (composition (pair second.snd
    (composition (pair first second.fst) takeFast)) (mapWith rowPrefixRealizer)) listSum

theorem polynomial_prefix : PolynomialTime prefixRealizer := by
  unfold prefixRealizer prefixNat Realizer.fst Realizer.snd
  have := polynomial_takeFast (A := List ℕ)
  have := polynomial_rowPrefix
  have := polynomial_listSum
  tree_cost

abbrev CellInput := (ℕ × MatrixCode) × (ℕ × ℕ)

def floorPrefix (x : CellInput) : ℕ := prefixNat (x.1.2, x.2) / x.1.1

def floorPrefixRealizer : Realizer floorPrefix :=
  composition (pair (composition (pair first.snd second) prefixRealizer) first.fst) quotient

theorem polynomial_floorPrefix : PolynomialTime floorPrefixRealizer := by
  unfold floorPrefixRealizer floorPrefix Realizer.fst Realizer.snd
  have := polynomial_prefix
  have := polynomial_quotient
  tree_cost

/-- The first component is the positive diagonal of the mixed difference;
the second is the negative diagonal including the padding of two. -/
def cellTotals (x : CellInput) : ℕ × ℕ :=
  (floorPrefix (x.1, (x.2.1 + 1, x.2.2 + 1)) + floorPrefix x,
   floorPrefix (x.1, (x.2.1, x.2.2 + 1)) +
     floorPrefix (x.1, (x.2.1 + 1, x.2.2)) + 2)

def cellTotalsRealizer : Realizer cellTotals :=
  (pair
    (composition (pair
      (composition (pair first (pair (composition second.fst successor)
        (composition second.snd successor))) floorPrefixRealizer)
      floorPrefixRealizer) add)
    (composition (pair
      (composition (pair
        (composition (pair first (pair second.fst (composition second.snd successor)))
          floorPrefixRealizer)
        (composition (pair first (pair (composition second.fst successor) second.snd))
          floorPrefixRealizer)) add)
      (constant 2)) add)).congr (fun _ => rfl)

theorem polynomial_cellTotals : PolynomialTime cellTotalsRealizer := by
  unfold cellTotalsRealizer cellTotals Realizer.fst Realizer.snd
  have := polynomial_floorPrefix
  have := polynomial_successor
  tree_cost

/-- Test before natural subtraction. Rejection retains its own Boolean tag,
even when its truncated numeric component happens to equal an accepted value. -/
def cell (x : CellInput) : Bool × ℕ :=
  (decide ((cellTotals x).2 ≤ (cellTotals x).1), (cellTotals x).1 - (cellTotals x).2)

def cellRealizer : Realizer cell :=
  composition cellTotalsRealizer (pair (composition (pair second first) leNat) subtract)

theorem polynomial_cell : PolynomialTime cellRealizer := by
  unfold cellRealizer cell
  have := polynomial_cellTotals
  tree_cost

/-- Enumeration is bounded by an actual encoded list, rather than a binary
natural that could request exponentially many output cells. -/
def indices {A : Type} (as : List A) : List ℕ := List.range as.length

def indicesRealizer {A : Type} [Codec A] : Realizer (indices (A := A)) :=
  composition listLength range

theorem polynomial_indices {A : Type} [Codec A] :
    PolynomialTime (indicesRealizer (A := A)) := by
  apply polynomial_boundedRange polynomial_listLength Polynomial.X
  intro as
  simpa only [Polynomial.eval_X] using list_length_le_weight as

def rowCells (x : (ℕ × MatrixCode) × ℕ) : List (Bool × ℕ) :=
  (indices (x.1.2.getD x.2 [])).map (fun j => cell (x.1, (x.2, j)))

def rowCellsRealizer : Realizer rowCells :=
  composition (pair identity
    (composition (composition (pair first.snd second) (getDFast [])) indicesRealizer))
    (mapWith (composition (pair first.fst (pair first.snd second)) cellRealizer))

theorem polynomial_rowCells : PolynomialTime rowCellsRealizer := by
  unfold rowCellsRealizer rowCells Realizer.fst Realizer.snd
  have := polynomial_getDFast ([] : List ℕ)
  have := polynomial_indices (A := ℕ)
  have := polynomial_cell
  tree_cost

def cells (x : ℕ × MatrixCode) : List (List (Bool × ℕ)) :=
  (indices x.2).map (fun i => rowCells (x, i))

def cellsRealizer : Realizer cells :=
  composition (pair identity (composition second indicesRealizer)) (mapWith rowCellsRealizer)

theorem polynomial_cells : PolynomialTime cellsRealizer := by
  unfold cellsRealizer cells
  have := polynomial_indices (A := List ℕ)
  have := polynomial_rowCells
  tree_cost

def accepted (xs : List (List (Bool × ℕ))) : Bool :=
  (xs.map (fun row => (row.map Prod.fst).all id)).all id

def acceptedRealizer : Realizer accepted := composition
  (map (composition (map first) all)) all

theorem polynomial_accepted : PolynomialTime acceptedRealizer := by
  unfold acceptedRealizer accepted
  have := polynomial_all
  tree_cost

def values (xs : List (List (Bool × ℕ))) : MatrixCode := xs.map (List.map Prod.snd)

def valuesRealizer : Realizer values := map (map second)

theorem polynomial_values : PolynomialTime valuesRealizer :=
  polynomial_map (polynomial_map polynomial_second)

def finish (xs : List (List (Bool × ℕ))) : Option MatrixCode :=
  if accepted xs then Option.some (values xs) else none

def finishRealizer : Realizer finish :=
  choose acceptedRealizer
    (composition valuesRealizer OAI.MatchingFPRAS.TreeTyped.some) (constant none)

theorem polynomial_finish : PolynomialTime finishRealizer :=
  polynomial_choose polynomial_accepted
    (polynomial_composition polynomial_values polynomial_some) (polynomial_constant none)

/-- A total, shape-preserving completion decoder for binary list matrices. -/
def decode (x : ℕ × MatrixCode) : Option MatrixCode := finish (cells x)

def decodeRealizer : Realizer decode := composition cellsRealizer finishRealizer

/-- Polynomial charged tree-machine work and output weight for the decoder.
The input weight includes the binary divisor and every supplied matrix entry. -/
theorem polynomial_decode : PolynomialTime decodeRealizer :=
  polynomial_composition polynomial_cells polynomial_finish

lemma sum_take_getD {A : Type} (xs : List A) (f : A → ℕ) (d : A)
    (hd : f d = 0) (p : ℕ) :
    ((xs.take p).map f).sum = ∑ i ∈ Finset.range p, f (xs.getD i d) := by
  induction p with
  | zero => simp
  | succ p ih =>
    rw [Finset.sum_range_succ]
    by_cases hp : p < xs.length
    · rw [List.take_succ_eq_append_getElem hp, List.map_append, List.sum_append, ih]
      simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [List.getD_eq_getElem xs d hp]
    · have hp' : xs.length ≤ p := by omega
      rw [List.take_of_length_le hp'] at ih
      rw [List.take_of_length_le (show xs.length ≤ p + 1 by omega)]
      rw [List.getD_eq_default xs d hp', hd]
      simpa using ih

lemma prefix_range (Z : MatrixCode) (p q : ℕ) :
    prefixNat (Z, (p, q)) =
      ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range q, matrixEntry (Z, (i, j)) := by
  unfold prefixNat
  rw [sum_take_getD Z (fun row => rowPrefix (q, row)) [] (by simp [rowPrefix]) p]
  apply Finset.sum_congr rfl
  intro i hi
  simpa [rowPrefix, matrixEntry] using sum_take_getD (Z.getD i []) id 0 rfl q

lemma matrixEntry_code_zero {a b : ℕ} (Z : Fin a → Fin b → ℕ) (i j : ℕ) :
    (matrixEntry (matrixCode Z, (i, j)) : ℤ) =
      CompletionBooleanRetry.zeroExtend Z i j := by
  by_cases hi : i < a
  · by_cases hj : j < b
    · simpa [CompletionBooleanRetry.zeroExtend, hi, hj] using
        congrArg (fun n : ℕ => (n : ℤ)) (matrixEntry_code Z ⟨i, hi⟩ ⟨j, hj⟩)
    · simp [matrixEntry, matrixCode, CompletionBooleanRetry.zeroExtend, hi, hj,
        List.getD_eq_getElem?_getD]
  · simp [matrixEntry, matrixCode, CompletionBooleanRetry.zeroExtend, hi,
      List.getD_eq_getElem?_getD]

lemma prefix_code (Z : Fin a → Fin b → ℕ) (p q : ℕ) :
    (prefixNat (matrixCode Z, (p, q)) : ℤ) = CompletionBooleanRetry.prefixInt Z p q := by
  rw [prefix_range]
  simp only [Nat.cast_sum]
  unfold CompletionBooleanRetry.prefixInt
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact matrixEntry_code_zero Z i j

lemma floorPrefix_code (k : ℕ) (Z : Fin a → Fin b → ℕ) (p q : ℕ) :
    (floorPrefix ((k, matrixCode Z), (p, q)) : ℤ) =
      CompletionBooleanRetry.prefixInt Z p q / (k : ℤ) := by
  unfold floorPrefix
  rw [Int.natCast_ediv, prefix_code]

lemma cellTotals_code (k : ℕ) (Z : Fin a → Fin b → ℕ) (i : Fin a) (j : Fin b) :
    ((cellTotals ((k, matrixCode Z), (i.val, j.val))).1 : ℤ) -
      ((cellTotals ((k, matrixCode Z), (i.val, j.val))).2 : ℤ) =
      CompletionBooleanRetry.decodeCells k Z i j := by
  simp only [cellTotals, Nat.cast_add, Nat.cast_ofNat, floorPrefix_code,
    CompletionBooleanRetry.decodeCells]
  ring

lemma cell_code (k : ℕ) (Z : Fin a → Fin b → ℕ) (i : Fin a) (j : Fin b) :
    cell ((k, matrixCode Z), (i.val, j.val)) =
      (decide (0 ≤ CompletionBooleanRetry.decodeCells k Z i j),
        (CompletionBooleanRetry.decodeCells k Z i j).toNat) := by
  have he := cellTotals_code k Z i j
  simp only [cell]
  apply Prod.ext
  · apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rw [← he]
    omega
  · rw [← he]
    omega

lemma map_range_ofFn {A : Type} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp

lemma rowCells_code (k : ℕ) (Z : Fin a → Fin b → ℕ) (i : Fin a) :
    rowCells ((k, matrixCode Z), i.val) =
      List.ofFn (fun j : Fin b =>
        (decide (0 ≤ CompletionBooleanRetry.decodeCells k Z i j),
          (CompletionBooleanRetry.decodeCells k Z i j).toNat)) := by
  have hrow : (matrixCode Z).getD i.val [] = List.ofFn (Z i) := by
    simp only [matrixCode, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      i.isLt, dite_true, Option.getD_some, Fin.eta]
  unfold rowCells indices
  rw [hrow, List.length_ofFn, map_range_ofFn]
  congr 1
  funext j
  exact cell_code k Z i j

lemma cells_code (k : ℕ) (Z : Fin a → Fin b → ℕ) :
    cells (k, matrixCode Z) = List.ofFn (fun i : Fin a =>
      List.ofFn (fun j : Fin b =>
        (decide (0 ≤ CompletionBooleanRetry.decodeCells k Z i j),
          (CompletionBooleanRetry.decodeCells k Z i j).toNat))) := by
  unfold cells indices
  simp only [matrixCode, List.length_ofFn]
  rw [map_range_ofFn]
  congr 1
  funext i
  exact rowCells_code k Z i

lemma all_ofFn {n : ℕ} (f : Fin n → Bool) :
    (List.ofFn f).all id = true ↔ ∀ i, f i = true := by
  simp only [List.all_eq_true, List.mem_ofFn, id_eq]
  constructor
  · intro h i
    exact h (f i) ⟨i, rfl⟩
  · intro h v hv
    obtain ⟨i, rfl⟩ := hv
    exact h i

lemma accepted_code (k : ℕ) (Z : Fin a → Fin b → ℕ) :
    accepted (cells (k, matrixCode Z)) =
      decide (CompletionBooleanRetry.acceptedCells k Z) := by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_eq]
  rw [cells_code]
  simp only [accepted, List.map_ofFn, Function.comp_apply, all_ofFn,
    CompletionBooleanRetry.acceptedCells]
  simp only [decide_eq_true_eq]

lemma values_code (k : ℕ) (Z : Fin a → Fin b → ℕ) :
    values (cells (k, matrixCode Z)) =
      matrixCode (fun i j => (CompletionBooleanRetry.decodeCells k Z i j).toNat) := by
  rw [cells_code]
  simp only [values, matrixCode, List.map_ofFn]
  congr 1
  funext i
  simp only [Function.comp_apply, List.map_ofFn]
  rfl

/-- Exact value semantics of the polynomial list decoder. It rejects the
same signed cells, including k=0 and empty/singleton dimensions, and preserves
the complete row and column order of the raw executable decoder. -/
theorem decode_code (k : ℕ) (Z : Fin a → Fin b → ℕ) :
    decode (k, matrixCode Z) = (CompletionBooleanRetry.rawTrial k Z).map matrixCode := by
  unfold decode finish CompletionBooleanRetry.rawTrial
  rw [accepted_code, values_code]
  by_cases h : CompletionBooleanRetry.acceptedCells k Z <;> simp [h]

/-- On an actual fine table, list execution has exactly the accepted/rejected
value of the geometric finite-table trial used by the accuracy theorem. -/
theorem decode_fineTable (k : ℕ) (hk : 0 < k)
    (R : Fin a → ℕ) (P : Fin b → ℕ)
    (Z : Math115.LatticeCompletionFinite.FineTable k R P) :
    decode (k, matrixCode Z.val) =
      (Math115.LatticeCompletionLaw.trial k hk R P Z).map
        (fun X => matrixCode X.val) := by
  rw [decode_code, CompletionBooleanRetry.rawTrial_eq_tableTrial_value k hk R P Z,
    CompletionBooleanRetry.tableTrial_eq k hk R P Z]
  cases h : Math115.LatticeCompletionLaw.trial k hk R P Z <;> rfl

end Math115.LatticeCompletionProgram
