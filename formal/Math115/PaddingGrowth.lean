/-
SPDX-License-Identifier: Apache-2.0

Sequential padding growth for the actual upstream ordinary Table model.
Every unit step uses the already proved cell-shift equivalence and strong
zero-entry count bound. The final scale is a sufficient padding threshold,
not a reparameterization of the complete sampler.
-/
import Math115.PaddedMarginBridge
import Math115.PaddingGrowthAlgebra

namespace Math115.PaddingGrowth

open OAI.ContingencyTables
open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- Increase a single margin by a nonnegative integer amount. -/
def raiseMargin {A : Type*} [DecidableEq A] (r : A → ℕ) (a : A) (k : ℕ) : A → ℕ :=
  Function.update r a (r a + k)

@[simp] theorem raiseMargin_zero {A : Type*} [DecidableEq A] (r : A → ℕ) (a : A) :
    raiseMargin r a 0 = r := by
  funext i
  by_cases hi : i = a <;> simp [raiseMargin, hi]

@[simp] theorem raiseMargin_self {A : Type*} [DecidableEq A]
    (r : A → ℕ) (a : A) (k : ℕ) : raiseMargin r a k a = r a + k := by
  simp [raiseMargin]

theorem raiseMargin_add {A : Type*} [DecidableEq A]
    (r : A → ℕ) (a : A) (k l : ℕ) :
    raiseMargin (raiseMargin r a k) a l = raiseMargin r a (k + l) := by
  funext i
  by_cases hi : i = a <;> simp [raiseMargin, hi, Nat.add_assoc]

theorem lowerMargin_raiseMargin_one {A : Type*} [DecidableEq A]
    (r : A → ℕ) (a : A) :
    SmallEntryTail.lowerMargin (raiseMargin r a 1) a 1 = r := by
  funext i
  by_cases hi : i = a <;> simp [SmallEntryTail.lowerMargin, raiseMargin, hi]

/-- Adding one in a marked cell identifies the old fiber with the positive
part of the next fiber. The strong zero-entry estimate bounds the rest. -/
theorem one_unit_count_growth (r : I → ℕ) (c : J → ℕ) (a : I) (s : J) (U : ℕ)
    (hrow : U ≤ r a) (hcol : U ≤ c s) :
    Fintype.card (Table (raiseMargin r a 1) (raiseMargin c s 1)) * (U + 1) ≤
      Fintype.card (Table r c) *
        (U + 1 + (Fintype.card I - 1) * (Fintype.card J - 1)) := by
  classical
  let R := raiseMargin r a 1
  let C := raiseMargin c s 1
  let T := Table R C
  let e := (Fintype.card I - 1) * (Fintype.card J - 1)
  have hr : U + 1 ≤ R a := by simpa [R] using Nat.add_le_add_right hrow 1
  have hc : U + 1 ≤ C s := by simpa [C] using Nat.add_le_add_right hcol 1
  have hbad := SmallEntryTail.all_donor_small_entry_count_strong a s (U + 1) 1 hr hc
    (by omega)
  have hsplit := SmallEntryTail.small_card_add_survival R C a s 1
  have hpositive : SmallEntryTail.survivalCount R C a s 1 = Fintype.card (Table r c) := by
    have hshift := SmallEntryTail.shifted_card (r := R) (c := C) a s 1 (by omega) (by omega)
    simpa only [R, C, lowerMargin_raiseMargin_one] using hshift.symm
  rw [hpositive] at hsplit
  change Fintype.card {X : T // X.val a s < 1} * (U + 1 + e) ≤
    Fintype.card T * (1 * e) at hbad
  change Fintype.card T * (U + 1) ≤ Fintype.card (Table r c) * (U + 1 + e)
  nlinarith only [hbad, hsplit]

/-- Repeat the actual one-cell shift, without a nonempty-fiber hypothesis. -/
theorem one_cell_count_growth (r : I → ℕ) (c : J → ℕ) (a : I) (s : J) (U L : ℕ)
    (hrow : U ≤ r a) (hcol : U ≤ c s) :
    Fintype.card (Table (raiseMargin r a L) (raiseMargin c s L)) * (U + 1) ^ L ≤
      Fintype.card (Table r c) *
        (U + 1 + (Fintype.card I - 1) * (Fintype.card J - 1)) ^ L := by
  induction L with
  | zero => simp
  | succ L ih =>
      let B := U + 1 + (Fintype.card I - 1) * (Fintype.card J - 1)
      have hs := one_unit_count_growth (raiseMargin r a L) (raiseMargin c s L) a s U
        (by simpa using hrow.trans (Nat.le_add_right (r a) L))
        (by simpa using hcol.trans (Nat.le_add_right (c s) L))
      rw [raiseMargin_add, raiseMargin_add] at hs
      calc
        _ = (Fintype.card (Table (raiseMargin r a (L + 1)) (raiseMargin c s (L + 1))) *
            (U + 1)) * (U + 1) ^ L := by rw [pow_succ]; ring
        _ ≤ (Fintype.card (Table (raiseMargin r a L) (raiseMargin c s L)) * B) *
            (U + 1) ^ L := Nat.mul_le_mul_right _ hs
        _ = (Fintype.card (Table (raiseMargin r a L) (raiseMargin c s L)) *
            (U + 1) ^ L) * B := by ring
        _ ≤ (Fintype.card (Table r c) * B ^ L) * B := Nat.mul_le_mul_right _ ih
        _ = _ := by rw [pow_succ]; ring

omit [Fintype I] [Fintype J] in
theorem largePadding_insert (K : Finset (I × J)) (p : I × J) (L : ℕ) (hp : p ∉ K)
    (i : I) (j : J) :
    largePadding (insert p K) L i j = largePadding K L i j +
      if i = p.1 ∧ j = p.2 then L else 0 := by
  by_cases hij : (i, j) = p
  · have hi : i = p.1 := congrArg Prod.fst hij
    have hj : j = p.2 := congrArg Prod.snd hij
    simp [largePadding, hi, hj, hp]
  · have hnot : ¬(i = p.1 ∧ j = p.2) := by
      rintro ⟨hi, hj⟩
      exact hij (Prod.ext hi hj)
    simp [largePadding, hij, hnot]

omit [Fintype I] in
theorem paddedRows_insert (r : I → ℕ) (K : Finset (I × J)) (p : I × J) (L : ℕ)
    (hp : p ∉ K) :
    paddedRows r (largePadding (insert p K) L) =
      raiseMargin (paddedRows r (largePadding K L)) p.1 L := by
  funext i
  unfold paddedRows
  simp_rw [largePadding_insert K p L hp]
  rw [Finset.sum_add_distrib]
  by_cases hi : i = p.1
  · subst i
    simp [raiseMargin, Nat.add_assoc]
  · simp [raiseMargin, hi]

omit [Fintype J] in
theorem paddedColumns_insert (c : J → ℕ) (K : Finset (I × J)) (p : I × J) (L : ℕ)
    (hp : p ∉ K) :
    paddedColumns c (largePadding (insert p K) L) =
      raiseMargin (paddedColumns c (largePadding K L)) p.2 L := by
  funext j
  unfold paddedColumns
  simp_rw [largePadding_insert K p L hp]
  rw [Finset.sum_add_distrib]
  by_cases hj : j = p.2
  · subst j
    simp [raiseMargin, Nat.add_assoc]
  · simp [raiseMargin, hj]

/-- Telescope the actual ordinary-table counts through all `|K| L` unit
additions. All earlier padding is nonnegative, so every unit uses the same
incident-margin lower bound. Empty marked sets and `L = 0` are included. -/
theorem large_padding_count_growth (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (L U : ℕ)
    (hrow : ∀ p ∈ K, U ≤ r p.1) (hcol : ∀ p ∈ K, U ≤ c p.2) :
    Fintype.card (Table (paddedRows r (largePadding K L))
      (paddedColumns c (largePadding K L))) * (U + 1) ^ (K.card * L) ≤
      Fintype.card (Table r c) *
        (U + 1 + (Fintype.card I - 1) * (Fintype.card J - 1)) ^ (K.card * L) := by
  classical
  revert hrow hcol
  induction K using Finset.induction_on with
  | empty =>
      intro _ _
      have hr : paddedRows r (largePadding (∅ : Finset (I × J)) L) = r := by
        funext i
        simp [paddedRows, largePadding]
      have hc : paddedColumns c (largePadding (∅ : Finset (I × J)) L) = c := by
        funext j
        simp [paddedColumns, largePadding]
      rw [hr, hc]
      simp
  | @insert p K hp ih =>
      intro hrow hcol
      let B := U + 1 + (Fintype.card I - 1) * (Fintype.card J - 1)
      let R := paddedRows r (largePadding K L)
      let C := paddedColumns c (largePadding K L)
      have hrowK : ∀ p ∈ K, U ≤ r p.1 := fun p hp => hrow p (Finset.mem_insert_of_mem hp)
      have hcolK : ∀ p ∈ K, U ≤ c p.2 := fun p hp => hcol p (Finset.mem_insert_of_mem hp)
      have hprior := ih hrowK hcolK
      have hr : U ≤ R p.1 := (hrow p (Finset.mem_insert_self _ _)).trans
        (Nat.le_add_right _ _)
      have hc : U ≤ C p.2 := (hcol p (Finset.mem_insert_self _ _)).trans
        (Nat.le_add_right _ _)
      have hs := one_cell_count_growth R C p.1 p.2 U L hr hc
      rw [paddedRows_insert r K p L hp, paddedColumns_insert c K p L hp]
      rw [Finset.card_insert_of_notMem hp]
      have hexp : (K.card + 1) * L = K.card * L + L := by ring
      rw [hexp, pow_add, pow_add]
      calc
        _ = (Fintype.card (Table (raiseMargin R p.1 L) (raiseMargin C p.2 L)) *
            (U + 1) ^ L) * (U + 1) ^ (K.card * L) := by ring
        _ ≤ (Fintype.card (Table R C) * B ^ L) * (U + 1) ^ (K.card * L) :=
          Nat.mul_le_mul_right _ hs
        _ = (Fintype.card (Table R C) * (U + 1) ^ (K.card * L)) * B ^ L := by ring
        _ ≤ (Fintype.card (Table r c) * B ^ (K.card * L)) * B ^ L :=
          Nat.mul_le_mul_right _ hprior
        _ = _ := by ring

/-- In a one-dimensional ordinary fiber there are no donor pairs, and
padding preserves the table count exactly, including empty fibers. -/
theorem large_padding_count_eq_of_zero_donors (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (L : ℕ)
    (he : (Fintype.card I - 1) * (Fintype.card J - 1) = 0) :
    Fintype.card (Table (paddedRows r (largePadding K L))
      (paddedColumns c (largePadding K L))) = Fintype.card (Table r c) := by
  classical
  have hupper := large_padding_count_growth r c K L 0
    (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.zero_le _)
  simp only [he, zero_add, add_zero, one_pow, mul_one] at hupper
  apply Nat.le_antisymm hupper
  rw [← successful_card r c (largePadding K L)]
  exact Fintype.card_subtype_le _

/-- The new sufficient threshold retains the fifth-power dimension scale. -/
def sequentialU (d : ℕ) : ℕ := 47 * d ^ 5

/-- The numerical budget for `q = |K| L`, at `L = 32 d³`. -/
theorem sequential_scale_budget (d g e : ℕ) (hg : g ≤ d) (he : e ≤ d) :
    47 * (g * proposedL d) * e ≤ 32 * (sequentialU d + 1) := by
  calc
    _ = (47 * proposedL d) * (g * e) := by ring
    _ ≤ (47 * proposedL d) * (d * d) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hg he)
    _ = 32 * sequentialU d := by unfold proposedL sequentialU; ring
    _ ≤ _ := Nat.mul_le_mul_left 32 (Nat.le_add_right _ _)

/-- Actual padded-table cardinalities at `U = 47 d⁵`. This theorem needs no
equal-total or nonempty-fiber premise, and remains valid at `d = 0`. -/
theorem sequential_padded_count_le_twice_original (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (d : ℕ)
    (hsize : Fintype.card I * Fintype.card J ≤ d)
    (hrow : ∀ p ∈ K, sequentialU d ≤ r p.1)
    (hcol : ∀ p ∈ K, sequentialU d ≤ c p.2) :
    Fintype.card (Table (paddedRows r (largePadding K (proposedL d)))
      (paddedColumns c (largePadding K (proposedL d)))) ≤ 2 * Fintype.card (Table r c) := by
  classical
  have hK : K.card ≤ d :=
    (show K.card ≤ Fintype.card I * Fintype.card J by
      simpa only [Fintype.card_prod] using K.card_le_univ).trans hsize
  have he : (Fintype.card I - 1) * (Fintype.card J - 1) ≤ d :=
    (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)).trans hsize
  exact PaddingGrowthAlgebra.count_le_twice_of_growth _ _ _ _ _
    (large_padding_count_growth r c K (proposedL d) (sequentialU d) hrow hcol)
    (sequential_scale_budget d K.card _ hK he)

/-- A threshold computed from the full dimensions, before choosing the
marked set. Its `2L` floor preserves the existing padding-width condition. -/
def sequentialShapeU (d cells e : ℕ) : ℕ :=
  max (2 * proposedL d) (47 * d ^ 3 * cells * e - 1)

theorem sequential_shape_scale_budget (d cells g e : ℕ) (hg : g ≤ cells) :
    47 * (g * proposedL d) * e ≤ 32 * (sequentialShapeU d cells e + 1) := by
  have hfloor : 47 * d ^ 3 * cells * e - 1 ≤ sequentialShapeU d cells e :=
    le_max_right _ _
  have hcount : 47 * d ^ 3 * cells * e ≤ sequentialShapeU d cells e + 1 := by omega
  calc
    _ = 32 * (47 * d ^ 3 * g * e) := by unfold proposedL; ring
    _ ≤ 32 * (47 * d ^ 3 * cells * e) :=
      Nat.mul_le_mul_left 32 (Nat.mul_le_mul_right e (Nat.mul_le_mul_left _ hg))
    _ ≤ _ := Nat.mul_le_mul_left 32 hcount

/-- The shape-dependent sequential threshold also bounds actual padded
counts. It depends on all cells, not on the threshold-selected marked set. -/
theorem sequential_shape_padded_count_le_twice_original (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (d : ℕ)
    (hrow : ∀ p ∈ K, sequentialShapeU d (Fintype.card I * Fintype.card J)
      ((Fintype.card I - 1) * (Fintype.card J - 1)) ≤ r p.1)
    (hcol : ∀ p ∈ K, sequentialShapeU d (Fintype.card I * Fintype.card J)
      ((Fintype.card I - 1) * (Fintype.card J - 1)) ≤ c p.2) :
    Fintype.card (Table (paddedRows r (largePadding K (proposedL d)))
      (paddedColumns c (largePadding K (proposedL d)))) ≤ 2 * Fintype.card (Table r c) := by
  classical
  have hK : K.card ≤ Fintype.card I * Fintype.card J := by
    simpa only [Fintype.card_prod] using K.card_le_univ
  exact PaddingGrowthAlgebra.count_le_twice_of_growth _ _ _ _ _
    (large_padding_count_growth r c K (proposedL d) _ hrow hcol)
    (sequential_shape_scale_budget d _ K.card _ hK)

end Math115.PaddingGrowth
