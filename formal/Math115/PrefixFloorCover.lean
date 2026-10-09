/-
SPDX-License-Identifier: Apache-2.0
Coarse floor cover of actual transportation regions by integer-table cells.
All margins shifted below are signed reals; no truncated subtraction is used.
-/
import Math115.PrefixTransportation
import Math115.LatticeCompletionFinite

namespace Math115.PrefixFloorCover

open PrefixTransportation OAI.ContingencyTables
open scoped BigOperators ENNReal
noncomputable section

def floorPrefix {a b : ℕ} (X : Matrix a b) : LatticeCompletion.Array :=
  fun p q => Int.floor (prefixSum (extend X) p q)

def floorGrid {a b : ℕ} (X : Matrix a b) : LatticeCompletionFinite.Grid a b :=
  fun i j => LatticeCompletion.difference (floorPrefix X) i.val j.val

lemma floorPrefix_zero_axes {a b : ℕ} (X : Matrix a b) :
    LatticeCompletion.ZeroAxes (floorPrefix X) := by
  constructor <;> intro n <;> simp [floorPrefix, prefixSum]

lemma floorGrid_entry_error {a b : ℕ} (X : Matrix a b) (i : Fin a) (j : Fin b) :
    -2 < (floorGrid X i j : ℝ) - X i j ∧ (floorGrid X i j : ℝ) - X i j < 2 := by
  have h00 := Int.floor_le (prefixSum (extend X) i.val j.val)
  have h01 := Int.floor_le (prefixSum (extend X) i.val (j.val + 1))
  have h10 := Int.floor_le (prefixSum (extend X) (i.val + 1) j.val)
  have h11 := Int.floor_le (prefixSum (extend X) (i.val + 1) (j.val + 1))
  have g00 := Int.lt_floor_add_one (prefixSum (extend X) i.val j.val)
  have g01 := Int.lt_floor_add_one (prefixSum (extend X) i.val (j.val + 1))
  have g10 := Int.lt_floor_add_one (prefixSum (extend X) (i.val + 1) j.val)
  have g11 := Int.lt_floor_add_one (prefixSum (extend X) (i.val + 1) (j.val + 1))
  have hr := congrFun (congrFun (difference_prefix (extend X)) i.val) j.val
  rw [extend_inside] at hr
  unfold difference at hr
  simp only [floorGrid, LatticeCompletion.difference, floorPrefix, Int.cast_add, Int.cast_sub]
  constructor <;> linarith only [h00,h01,h10,h11,g00,g01,g10,g11,hr]

lemma floorGrid_nonnegative {a b : ℕ} (X : Matrix a b) (hX : ∀ i j, 2 ≤ X i j)
    (i : Fin a) (j : Fin b) : 0 ≤ floorGrid X i j := by
  have h := (floorGrid_entry_error X i j).1
  have hp : (0 : ℝ) < (floorGrid X i j : ℝ) := by linarith [hX i j]
  exact_mod_cast hp.le

def marginPrefix {n : ℕ} (R : Fin n → ℕ) (p : ℕ) : ℕ :=
  ∑ i ∈ Finset.range p, if hi : i < n then R ⟨i, hi⟩ else 0

lemma prefix_full_columns {a b : ℕ} (X : Matrix a b) (R : Fin a → ℕ)
    (hrow : ∀ i, ∑ j, X i j = (R i : ℝ)) (p : ℕ) :
    prefixSum (extend X) p b = (marginPrefix R p : ℝ) := by
  unfold prefixSum marginPrefix
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i < a
  · rw [range_sum_extend_row X ⟨i, hi⟩]
    simpa only [dite_eq_left hi] using hrow ⟨i, hi⟩
  · have hz : ∀ j, extend X i j = 0 := fun j => extend_outside X i j (Or.inl (by omega))
    simp [hz, hi]

lemma prefix_full_rows {a b : ℕ} (X : Matrix a b) (P : Fin b → ℕ)
    (hcol : ∀ j, ∑ i, X i j = (P j : ℝ)) (q : ℕ) :
    prefixSum (extend X) a q = (marginPrefix P q : ℝ) := by
  unfold prefixSum marginPrefix
  rw [Finset.sum_comm]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j < b
  · rw [range_sum_extend_column X ⟨j, hj⟩]
    simpa only [dite_eq_left hj] using hcol ⟨j, hj⟩
  · have hz : ∀ i, extend X i j = 0 := fun i => extend_outside X i j (Or.inr (by omega))
    simp [hz, hj]

lemma marginPrefix_succ {n : ℕ} (R : Fin n → ℕ) (i : Fin n) :
    marginPrefix R (i.val + 1) = marginPrefix R i.val + R i := by
  simp [marginPrefix, Finset.sum_range_succ, i.isLt]

lemma floorGrid_rows {a b : ℕ} (X : Matrix a b) (R : Fin a → ℕ)
    (hrow : ∀ i, ∑ j, X i j = (R i : ℝ)) (i : Fin a) :
    (∑ j, floorGrid X i j) = (R i : ℤ) := by
  have h := LatticeCompletion.difference_row_sum (floorPrefix X) i.val b
  rw [← Fin.sum_univ_eq_sum_range] at h
  change (∑ j, floorGrid X i j) = _ at h
  simp only [floorPrefix] at h
  rw [prefix_full_columns X R hrow, prefix_full_columns X R hrow] at h
  simpa [prefixSum, marginPrefix_succ] using h

lemma floorGrid_columns {a b : ℕ} (X : Matrix a b) (P : Fin b → ℕ)
    (hcol : ∀ j, ∑ i, X i j = (P j : ℝ)) (j : Fin b) :
    (∑ i, floorGrid X i j) = (P j : ℤ) := by
  have h := LatticeCompletion.difference_column_sum (floorPrefix X) a j.val
  rw [← Fin.sum_univ_eq_sum_range] at h
  change (∑ i, floorGrid X i j) = _ at h
  simp only [floorPrefix] at h
  rw [prefix_full_rows X P hcol, prefix_full_rows X P hcol] at h
  simpa [prefixSum, marginPrefix_succ] using h

def roundedTable {a b : ℕ} (R : Fin a → ℕ) (P : Fin b → ℕ) (X : Matrix a b)
    (hX : ∀ i j, 2 ≤ X i j)
    (hrow : ∀ i, ∑ j, X i j = (R i : ℝ))
    (hcol : ∀ j, ∑ i, X i j = (P j : ℝ)) : Table R P :=
  ⟨LatticeCompletionFinite.natGrid (floorGrid X),
    LatticeCompletionFinite.natGrid_hasMargins R P _ (floorGrid_nonnegative X hX)
      (floorGrid_rows X R hrow) (floorGrid_columns X P hcol)⟩

def tableAnchor {a b : ℕ} {R : Fin a → ℕ} {P : Fin b → ℕ}
    (X : Table R P) : Interior a b → ℤ := fun p =>
  LatticeCompletion.prefixSum
    (LatticeCompletionFinite.extend 0 (LatticeCompletionFinite.intGrid X.val))
    (p.1.val + 1) (p.2.val + 1)

def tableReal {a b : ℕ} {R : Fin a → ℕ} {P : Fin b → ℕ}
    (X : Table R P) : Matrix a b := fun i j => X.val i j

lemma tableAnchor_cast {a b : ℕ} {R : Fin a → ℕ} {P : Fin b → ℕ}
    (X : Table R P) (p : Interior a b) :
    (tableAnchor X p : ℝ) = interiorPrefix (tableReal X) p := by
  have he : (fun i j => (LatticeCompletionFinite.extend 0
      (LatticeCompletionFinite.intGrid X.val) i j : ℝ)) = extend (tableReal X) := by
    funext i j
    unfold LatticeCompletionFinite.extend extend
    split_ifs <;> simp [LatticeCompletionFinite.intGrid, tableReal]
  unfold tableAnchor interiorPrefix
  calc
    _ = prefixSum (fun i j => (LatticeCompletionFinite.extend 0
        (LatticeCompletionFinite.intGrid X.val) i j : ℝ)) (p.1.val + 1) (p.2.val + 1) := by
      simp [LatticeCompletion.prefixSum, prefixSum]
    _ = _ := by rw [he]

lemma tableReal_feasible {a b : ℕ} {R : Fin a → ℕ} {P : Fin b → ℕ}
    (X : Table R P) : Feasible (fun i => (R i : ℝ)) (fun j => (P j : ℝ)) (tableReal X) := by
  refine ⟨fun _ _ => Nat.cast_nonneg _, ?_, ?_⟩
  · intro i
    change (∑ j, (X.val i j : ℝ)) = (R i : ℝ)
    exact_mod_cast X.property.1 i
  · intro j
    change (∑ i, (X.val i j : ℝ)) = (P j : ℝ)
    exact_mod_cast X.property.2 j

lemma tableAnchor_injective {a b : ℕ} (R : Fin a → ℕ) (P : Fin b → ℕ) :
    Function.Injective (@tableAnchor a b R P) := by
  intro X Y h
  have hp : interiorPrefix (tableReal X) = interiorPrefix (tableReal Y) := by
    funext p
    rw [← tableAnchor_cast X p, ← tableAnchor_cast Y p, congrFun h p]
  have hx := tableReal_feasible X
  have hy := tableReal_feasible Y
  have hm := interiorPrefix_injective_of_margins (tableReal X) (tableReal Y)
    (fun i => (hx.2.1 i).trans (hy.2.1 i).symm)
    (fun j => (hx.2.2 j).trans (hy.2.2 j).symm) hp
  apply Subtype.ext
  funext i j
  have hv := congrFun (congrFun hm i) j
  change (X.val i j : ℝ) = (Y.val i j : ℝ) at hv
  exact_mod_cast hv

lemma floorGrid_prefix {a b : ℕ} (X : Matrix a b) (p q : ℕ) (hp : p ≤ a) (hq : q ≤ b) :
    LatticeCompletion.prefixSum (LatticeCompletionFinite.extend 0 (floorGrid X)) p q =
      floorPrefix X p q := by
  calc
    _ = LatticeCompletion.prefixSum (LatticeCompletion.difference (floorPrefix X)) p q := by
      unfold LatticeCompletion.prefixSum
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      have hab : i < a ∧ j < b := by
        have := Finset.mem_range.mp hi
        have := Finset.mem_range.mp hj
        omega
      simp only [LatticeCompletionFinite.extend, dite_eq_left hab, floorGrid]
    _ = _ := LatticeCompletion.prefix_difference _ (floorPrefix_zero_axes X) p q

lemma roundedTable_anchor {a b : ℕ} (R : Fin a → ℕ) (P : Fin b → ℕ) (X : Matrix a b)
    (hX : ∀ i j, 2 ≤ X i j)
    (hrow : ∀ i, ∑ j, X i j = (R i : ℝ))
    (hcol : ∀ j, ∑ i, X i j = (P j : ℝ)) (p : Interior a b) :
    tableAnchor (roundedTable R P X hX hrow hcol) p = Int.floor (interiorPrefix X p) := by
  unfold tableAnchor roundedTable
  rw [LatticeCompletionFinite.intGrid_natGrid _ (floorGrid_nonnegative X hX)]
  exact floorGrid_prefix X _ _ (by have := p.1.isLt; omega) (by have := p.2.isLt; omega)

lemma interiorPrefix_mem_rounded_cell {a b : ℕ} (R : Fin a → ℕ) (P : Fin b → ℕ)
    (X : Matrix a b) (hX : ∀ i j, 2 ≤ X i j)
    (hrow : ∀ i, ∑ j, X i j = (R i : ℝ))
    (hcol : ∀ j, ∑ i, X i j = (P j : ℝ)) :
    interiorPrefix X ∈ LatticeCellVolume.prefixCell 1
      (tableAnchor (roundedTable R P X hX hrow hcol)) := by
  rw [LatticeCellVolume.mem_prefixCell_iff]
  intro p
  rw [roundedTable_anchor]
  simpa using And.intro (Int.floor_le (interiorPrefix X p))
    (Int.lt_floor_add_one (interiorPrefix X p))

/-- Concrete lower containment: adding two to each entry of the reduced
real region puts every prefix vector inside a cell of an actual integer
table with the original natural margins. -/
theorem lower_floor_cover {a b : ℕ} (R : Fin a → ℕ) (P : Fin b → ℕ) :
    (fun z => interiorPrefix (fun (_ : Fin a) (_ : Fin b) => (2 : ℝ)) + z) ''
      PrefixRegion (fun i => (R i : ℝ) - 2 * b) (fun j => (P j : ℝ) - 2 * a) ⊆
      ⋃ X : Table R P, LatticeCellVolume.prefixCell 1 (tableAnchor X) := by
  rintro _ ⟨z, ⟨X, hX, rfl⟩, rfl⟩
  let B : Matrix a b := fun _ _ => 2
  let Y : Matrix a b := X + B
  have hy : ∀ i j, 2 ≤ Y i j := by intro i j; exact le_add_of_nonneg_left (hX.1 i j)
  have hr : ∀ i, ∑ j, Y i j = (R i : ℝ) := by
    intro i
    simp only [Y, B, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hX.2.1 i]
    ring
  have hc : ∀ j, ∑ i, Y i j = (P j : ℝ) := by
    intro j
    simp only [Y, B, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hX.2.2 j]
    ring
  apply Set.mem_iUnion.mpr
  refine ⟨roundedTable R P Y hy hr hc, ?_⟩
  have hm := interiorPrefix_mem_rounded_cell R P Y hy hr hc
  simpa only [Y, interiorPrefix_add, add_comm, B] using hm

/-- The volume of the reduced real transportation region is bounded by
the number of actual original integer tables, with no nonempty hypothesis. -/
theorem lower_volume_le_card {a b : ℕ} (R : Fin a → ℕ) (P : Fin b → ℕ) :
    MeasureTheory.volume
      (PrefixRegion (fun i => (R i : ℝ) - 2 * b) (fun j => (P j : ℝ) - 2 * a)) ≤
      (Fintype.card (Table R P) : ℝ≥0∞) := by
  calc
    _ ≤ MeasureTheory.volume (⋃ X : Table R P, LatticeCellVolume.prefixCell 1 (tableAnchor X)) :=
      LatticeCellVolume.volume_le_of_translated_subset _ _ _ (lower_floor_cover R P)
    _ = _ := LatticeCellVolume.prefix_unit_cells_volume tableAnchor (tableAnchor_injective R P)

end
end Math115.PrefixFloorCover
