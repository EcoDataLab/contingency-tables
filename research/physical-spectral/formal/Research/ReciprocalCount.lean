import Math115.PaddingGrowth
import Research.ReciprocalZero
import Research.GrowthScalar

namespace Research.ReciprocalCount

open OAI.ContingencyTables Math115.PaddingGrowth
open Research.ReciprocalZero
open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

lemma raiseMargin_total {A : Type*} [Fintype A] [DecidableEq A]
    (r : A → ℕ) (a : A) (k : ℕ) : (∑ i, raiseMargin r a k i) = (∑ i, r i) + k := by
  unfold raiseMargin
  rw [Finset.sum_update_of_mem (Finset.mem_univ a)]
  have h := Finset.sum_erase_add (Finset.univ : Finset A) r (Finset.mem_univ a)
  simp only [Finset.sdiff_singleton_eq_erase] at *
  omega

/-- The actual reciprocal zero probability and marked-cell shift bijection
produce the product count comparison, with dimensions in their correct arms.
No probability/count-growth bound is assumed as an input. -/
theorem one_unit_count_growth_of_totals (r : I → ℕ) (c : J → ℕ) (a : I) (s : J)
    (hI : 2 ≤ Fintype.card I) (hJ : 2 ≤ Fintype.card J)
    (htotal : (∑ i, r i) = ∑ j, c j) :
    Fintype.card (Table (raiseMargin r a 1) (raiseMargin c s 1)) * (r a + 1) * (c s + 1) ≤
      Fintype.card (Table r c) * (r a + Fintype.card J) * (c s + Fintype.card I) := by
  classical
  let R := raiseMargin r a 1
  let C := raiseMargin c s 1
  have htotal' : (∑ i, R i) = ∑ j, C j := by
    simp only [R, C, raiseMargin_total, htotal]
  have hsharp := zero_entry_probability_reciprocal R C a s hI hJ htotal'
  have hcard : (0 : ℝ) < Fintype.card (Table R C) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (table_nonempty R C htotal')
  let A : ℝ := (R a : ℝ) + (Fintype.card J - 1 : ℕ)
  let B : ℝ := (C s : ℝ) + (Fintype.card I - 1 : ℕ)
  have hA : 0 < A := by dsimp [A, R]; simp only [raiseMargin_self]; positivity
  have hB : 0 < B := by dsimp [B, C]; simp only [raiseMargin_self]; positivity
  have hid : (Fintype.card J - 1 : ℕ) / A + (Fintype.card I - 1 : ℕ) / B -
      ((Fintype.card J - 1) * (Fintype.card I - 1) : ℕ) / (A * B) =
      1 - (R a : ℝ) * (C s : ℝ) / (A * B) := by
    push_cast
    field_simp [ne_of_gt hA, ne_of_gt hB]
    dsimp only [A, B]
    ring
  change (Fintype.card (Research.WeightedIncidence.Level R C a s 0) : ℝ) /
    Fintype.card (Table R C) ≤ _ at hsharp
  change (Fintype.card (Research.WeightedIncidence.Level R C a s 0) : ℝ) /
    Fintype.card (Table R C) ≤ (Fintype.card J - 1 : ℕ) / A +
      (Fintype.card I - 1 : ℕ) / B -
      ((Fintype.card J - 1) * (Fintype.card I - 1) : ℕ) / (A * B) at hsharp
  rw [hid] at hsharp
  have hbad := (div_le_iff₀ hcard).mp hsharp
  have hbadD := mul_le_mul_of_nonneg_right hbad (mul_pos hA hB).le
  have hprod : (1 - (R a : ℝ) * C s / (A * B)) *
      (Fintype.card (Table R C) : ℝ) * (A * B) =
      (Fintype.card (Table R C) : ℝ) * (A * B - (R a : ℝ) * C s) := by
    field_simp
  rw [hprod] at hbadD
  have hsplit := Math115.SmallEntryTail.small_card_add_survival R C a s 1
  have hpositive : Math115.SmallEntryTail.survivalCount R C a s 1 = Fintype.card (Table r c) := by
    have h := Math115.SmallEntryTail.shifted_card (r := R) (c := C) a s 1
      (by dsimp [R]; simp) (by dsimp [C]; simp)
    simpa only [R, C, lowerMargin_raiseMargin_one] using h.symm
  rw [hpositive] at hsplit
  simp only [Nat.lt_one_iff] at hsplit
  have hsplitR : (Fintype.card (Research.WeightedIncidence.Level R C a s 0) : ℝ) +
      Fintype.card (Table r c) = Fintype.card (Table R C) := by exact_mod_cast hsplit
  have hcount : (Fintype.card (Table R C) : ℝ) * (R a : ℝ) * C s ≤
      (Fintype.card (Table r c) : ℝ) * (A * B) := by
    calc
      _ = (Fintype.card (Table R C) : ℝ) * (A * B) -
          (Fintype.card (Table R C) : ℝ) * (A * B - (R a : ℝ) * C s) := by ring
      _ ≤ (Fintype.card (Table R C) : ℝ) * (A * B) -
          (Fintype.card (Research.WeightedIncidence.Level R C a s 0) : ℝ) * (A * B) :=
        sub_le_sub_left hbadD _
      _ = _ := by rw [← hsplitR]; ring
  have hnJ : r a + 1 + (Fintype.card J - 1) = r a + Fintype.card J := by omega
  have hnI : c s + 1 + (Fintype.card I - 1) = c s + Fintype.card I := by omega
  simp only [R, C, A, B, raiseMargin_self, ← Nat.cast_add, hnJ, hnI] at hcount
  have hNat : Fintype.card (Table (raiseMargin r a 1) (raiseMargin c s 1)) * (r a + 1) * (c s + 1) ≤
      Fintype.card (Table r c) * ((r a + Fintype.card J) * (c s + Fintype.card I)) := by
    exact_mod_cast hcount
  simpa only [Nat.mul_assoc] using hNat

/-- Unconditional ordinary count comparison. Unequal totals give an empty
fiber; singleton dimensions use the existing deterministic donor-zero count.
Original incident margins may vanish. -/
theorem one_unit_count_growth (r : I → ℕ) (c : J → ℕ) (a : I) (s : J) :
    Fintype.card (Table (raiseMargin r a 1) (raiseMargin c s 1)) * (r a + 1) * (c s + 1) ≤
      Fintype.card (Table r c) * (r a + Fintype.card J) * (c s + Fintype.card I) := by
  classical
  by_cases htotal : (∑ i, r i) = ∑ j, c j
  · by_cases hdims : 2 ≤ Fintype.card I ∧ 2 ≤ Fintype.card J
    · exact one_unit_count_growth_of_totals r c a s hdims.1 hdims.2 htotal
    · have hI : 1 ≤ Fintype.card I := Fintype.card_pos_iff.mpr ⟨a⟩
      have hJ : 1 ≤ Fintype.card J := Fintype.card_pos_iff.mpr ⟨s⟩
      have he : (Fintype.card I - 1) * (Fintype.card J - 1) = 0 := by
        rcases not_and_or.mp hdims with hi | hj
        · have h : Fintype.card I - 1 = 0 := by omega
          simp only [h, zero_mul]
        · have h : Fintype.card J - 1 = 0 := by omega
          simp only [h, mul_zero]
      have hc := Math115.PaddingGrowth.one_unit_count_growth r c a s 0 (Nat.zero_le _) (Nat.zero_le _)
      simp only [he, zero_add, add_zero, mul_one] at hc
      have hf : (r a + 1) * (c s + 1) ≤ (r a + Fintype.card J) * (c s + Fintype.card I) :=
        Nat.mul_le_mul (Nat.add_le_add_left hJ _) (Nat.add_le_add_left hI _)
      have h := (Nat.mul_le_mul_right ((r a + 1) * (c s + 1)) hc).trans
        (Nat.mul_le_mul_left (Fintype.card (Table r c)) hf)
      simpa only [Nat.mul_assoc] using h
  · have hnew : ¬ (∑ i, raiseMargin r a 1 i) = ∑ j, raiseMargin c s 1 j := by
      rw [raiseMargin_total, raiseMargin_total]
      omega
    have hempty : IsEmpty (Table (raiseMargin r a 1) (raiseMargin c s 1)) :=
      ⟨fun X => hnew (totals_equal X.property)⟩
    have hcard := Fintype.card_eq_zero_iff.mpr hempty
    rw [hcard]
    simp


/-- Move the two actual incident margins to a frozen common floor by exact
cross multiplication. The positive incident factors, not table counts, are
canceled, so zero/empty table fibers remain valid. -/
lemma frozen_floor_growth (enlarged original a b H u v : ℕ)
    (ha0 : 0 < a) (hb0 : 0 < b) (ha : H ≤ a) (hb : H ≤ b)
    (hgrowth : enlarged * a * b ≤ original * (a + u) * (b + v)) :
    enlarged * H ^ 2 ≤ original * (H + u) * (H + v) := by
  have hratioA : (a + u) * H ≤ a * (H + u) := by
    have h := Nat.mul_le_mul_right u ha
    nlinarith only [h]
  have hratioB : (b + v) * H ≤ b * (H + v) := by
    have h := Nat.mul_le_mul_right v hb
    nlinarith only [h]
  have hratio : (a + u) * (b + v) * H ^ 2 ≤ (a * b) * ((H + u) * (H + v)) := by
    convert Nat.mul_le_mul hratioA hratioB using 1 <;> ring
  apply Nat.le_of_mul_le_mul_right (c := a * b) _ (Nat.mul_pos ha0 hb0)
  calc
    _ = (enlarged * a * b) * H ^ 2 := by ring
    _ ≤ (original * (a + u) * (b + v)) * H ^ 2 := Nat.mul_le_mul_right _ hgrowth
    _ = original * ((a + u) * (b + v) * H ^ 2) := by ring
    _ ≤ original * ((a * b) * ((H + u) * (H + v))) := Nat.mul_le_mul_left _ hratio
    _ = _ := by ring

theorem one_unit_frozen_growth (r : I → ℕ) (c : J → ℕ) (a : I) (s : J) (U : ℕ)
    (hrow : U ≤ r a) (hcol : U ≤ c s) :
    Fintype.card (Table (raiseMargin r a 1) (raiseMargin c s 1)) * (U + 1) ^ 2 ≤
      Fintype.card (Table r c) * (U + 1 + (Fintype.card J - 1)) *
        (U + 1 + (Fintype.card I - 1)) := by
  have hI : 1 ≤ Fintype.card I := Fintype.card_pos_iff.mpr ⟨a⟩
  have hJ : 1 ≤ Fintype.card J := Fintype.card_pos_iff.mpr ⟨s⟩
  have hrow' : U + 1 ≤ r a + 1 := Nat.add_le_add_right hrow 1
  have hcol' : U + 1 ≤ c s + 1 := Nat.add_le_add_right hcol 1
  apply frozen_floor_growth _ _ (r a + 1) (c s + 1) (U + 1)
    (Fintype.card J - 1) (Fintype.card I - 1) (by omega) (by omega) hrow' hcol'
  have heJ : r a + 1 + (Fintype.card J - 1) = r a + Fintype.card J := by omega
  have heI : c s + 1 + (Fintype.card I - 1) = c s + Fintype.card I := by omega
  simpa only [heJ, heI] using one_unit_count_growth r c a s

/-- Actual single-increment count bound after the proved AMGM reduction.
The dimension increment is the full-table line sum m+n−2. -/
theorem one_unit_doubled_growth (r : I → ℕ) (c : J → ℕ) (a : I) (s : J) (U : ℕ)
    (hrow : U ≤ r a) (hcol : U ≤ c s) :
    Fintype.card (Table (raiseMargin r a 1) (raiseMargin c s 1)) * (2 * (U + 1)) ^ 2 ≤
      Fintype.card (Table r c) *
        (2 * (U + 1) + (Fintype.card I + Fintype.card J - 2)) ^ 2 := by
  have hI : 1 ≤ Fintype.card I := Fintype.card_pos_iff.mpr ⟨a⟩
  have hJ : 1 ≤ Fintype.card J := Fintype.card_pos_iff.mpr ⟨s⟩
  have h := Research.GrowthRefinement.doubled_one_step _ _ (U + 1)
    (Fintype.card J - 1) (Fintype.card I - 1) (one_unit_frozen_growth r c a s U hrow hcol)
  have he : 2 * (U + 1) + (Fintype.card J - 1) + (Fintype.card I - 1) =
      2 * (U + 1) + (Fintype.card I + Fintype.card J - 2) := by omega
  simpa only [he] using h

/-- Repeated actual marked-cell additions, with the frozen incident floor.
The exponent is twice the actual number of unit additions. -/
theorem one_cell_count_growth (r : I → ℕ) (c : J → ℕ) (a : I) (s : J) (U L : ℕ)
    (hrow : U ≤ r a) (hcol : U ≤ c s) :
    Fintype.card (Table (raiseMargin r a L) (raiseMargin c s L)) * (2 * (U + 1)) ^ (2 * L) ≤
      Fintype.card (Table r c) *
        (2 * (U + 1) + (Fintype.card I + Fintype.card J - 2)) ^ (2 * L) := by
  induction L with
  | zero => simp
  | succ L ih =>
    let D := 2 * (U + 1)
    let B := D + (Fintype.card I + Fintype.card J - 2)
    have hs := one_unit_doubled_growth (raiseMargin r a L) (raiseMargin c s L) a s U
      (by simpa using hrow.trans (Nat.le_add_right (r a) L))
      (by simpa using hcol.trans (Nat.le_add_right (c s) L))
    rw [raiseMargin_add, raiseMargin_add] at hs
    change Fintype.card (Table (raiseMargin r a (L + 1)) (raiseMargin c s (L + 1))) * D ^ (2 * (L + 1)) ≤
      Fintype.card (Table r c) * B ^ (2 * (L + 1))
    have he : 2 * (L + 1) = 2 * L + 2 := by ring
    rw [he, pow_add, pow_add]
    calc
      _ = (Fintype.card (Table (raiseMargin r a (L + 1)) (raiseMargin c s (L + 1))) * D ^ 2) * D ^ (2 * L) := by ring
      _ ≤ (Fintype.card (Table (raiseMargin r a L) (raiseMargin c s L)) * B ^ 2) * D ^ (2 * L) := Nat.mul_le_mul_right _ hs
      _ = (Fintype.card (Table (raiseMargin r a L) (raiseMargin c s L)) * D ^ (2 * L)) * B ^ 2 := by ring
      _ ≤ (Fintype.card (Table r c) * B ^ (2 * L)) * B ^ 2 := Nat.mul_le_mul_right _ ih
      _ = _ := by ring

/-- Telescope the new actual one-cell recurrence through every cell of an
arbitrary marked set. Earlier padding is nonnegative. Empty sets, zero
padding, zero margins, and empty or unequal-total fibers are included. -/
theorem large_padding_count_growth (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (L U : ℕ)
    (hrow : ∀ p ∈ K, U ≤ r p.1) (hcol : ∀ p ∈ K, U ≤ c p.2) :
    Fintype.card (Table (paddedRows r (largePadding K L)) (paddedColumns c (largePadding K L))) *
        (2 * (U + 1)) ^ (2 * (K.card * L)) ≤
      Fintype.card (Table r c) *
        (2 * (U + 1) + (Fintype.card I + Fintype.card J - 2)) ^ (2 * (K.card * L)) := by
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
    let D := 2 * (U + 1)
    let B := D + (Fintype.card I + Fintype.card J - 2)
    let R := paddedRows r (largePadding K L)
    let C := paddedColumns c (largePadding K L)
    have hprior := ih (fun p hp => hrow p (Finset.mem_insert_of_mem hp))
      (fun p hp => hcol p (Finset.mem_insert_of_mem hp))
    have hr : U ≤ R p.1 := (hrow p (Finset.mem_insert_self _ _)).trans (Nat.le_add_right _ _)
    have hc : U ≤ C p.2 := (hcol p (Finset.mem_insert_self _ _)).trans (Nat.le_add_right _ _)
    have hs := one_cell_count_growth R C p.1 p.2 U L hr hc
    rw [paddedRows_insert r K p L hp, paddedColumns_insert c K p L hp, Finset.card_insert_of_notMem hp]
    have he : 2 * ((K.card + 1) * L) = 2 * (K.card * L) + 2 * L := by ring
    rw [he, pow_add, pow_add]
    calc
      _ = (Fintype.card (Table (raiseMargin R p.1 L) (raiseMargin C p.2 L)) * D ^ (2 * L)) * D ^ (2 * (K.card * L)) := by ring
      _ ≤ (Fintype.card (Table R C) * B ^ (2 * L)) * D ^ (2 * (K.card * L)) := Nat.mul_le_mul_right _ hs
      _ = (Fintype.card (Table R C) * D ^ (2 * (K.card * L))) * B ^ (2 * L) := by ring
      _ ≤ (Fintype.card (Table r c) * B ^ (2 * (K.card * L))) * B ^ (2 * L) := Nat.mul_le_mul_right _ hprior
      _ = _ := by ring

/-- The smaller m+n−2 scale now controls actual ordinary padded counts,
not merely a scalar recurrence supplied by a caller. -/
theorem large_padding_count_le_twice (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (L U : ℕ)
    (hrow : ∀ p ∈ K, U ≤ r p.1) (hcol : ∀ p ∈ K, U ≤ c p.2)
    (hbudget : 47 * (K.card * L) * (Fintype.card I + Fintype.card J - 2) ≤ 32 * (U + 1)) :
    Fintype.card (Table (paddedRows r (largePadding K L)) (paddedColumns c (largePadding K L))) ≤
      2 * Fintype.card (Table r c) := by
  exact Research.GrowthRefinement.doubled_growth_twice _ _ (K.card * L) (U + 1)
    (Fintype.card I + Fintype.card J - 2) (by omega)
    (large_padding_count_growth r c K L U hrow hcol) hbudget


/-- The old donor-pair and new reciprocal growth certificates are independent
valid bounds. Selecting their smaller numerical scale does not reinterpret
the old switching donor count. -/
theorem large_padding_count_le_twice_min (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (L U : ℕ)
    (hrow : ∀ p ∈ K, U ≤ r p.1) (hcol : ∀ p ∈ K, U ≤ c p.2)
    (hbudget : 47 * (K.card * L) *
      min ((Fintype.card I - 1) * (Fintype.card J - 1))
        (Fintype.card I + Fintype.card J - 2) ≤ 32 * (U + 1)) :
    Fintype.card (Table (paddedRows r (largePadding K L)) (paddedColumns c (largePadding K L))) ≤
      2 * Fintype.card (Table r c) := by
  by_cases he : (Fintype.card I - 1) * (Fintype.card J - 1) ≤
      Fintype.card I + Fintype.card J - 2
  · rw [min_eq_left he] at hbudget
    exact Math115.PaddingGrowthAlgebra.count_le_twice_of_growth _ _ (K.card * L) U _
      (Math115.PaddingGrowth.large_padding_count_growth r c K L U hrow hcol) hbudget
  · rw [min_eq_right (le_of_not_ge he)] at hbudget
    exact large_padding_count_le_twice r c K L U hrow hcol hbudget

/-- The preselected outer-shape cutoff now has an actual ordinary padded
count certificate. This theorem does not classify a physical mask, change
capacities, or supply a spectral/sampler conclusion. -/
theorem shape_padding_count_le_twice (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (d : ℕ)
    (hsize : Fintype.card I * Fintype.card J ≤ d)
    (hrow : ∀ p ∈ K, 11 * d * (Fintype.card I + Fintype.card J - 2) ≤ r p.1)
    (hcol : ∀ p ∈ K, 11 * d * (Fintype.card I + Fintype.card J - 2) ≤ c p.2) :
    Fintype.card (Table (paddedRows r (largePadding K 7)) (paddedColumns c (largePadding K 7))) ≤
      2 * Fintype.card (Table r c) := by
  classical
  have hK : K.card ≤ d :=
    (show K.card ≤ Fintype.card I * Fintype.card J by
      simpa only [Fintype.card_prod] using K.card_le_univ).trans hsize
  apply large_padding_count_le_twice r c K 7
    (11 * d * (Fintype.card I + Fintype.card J - 2)) hrow hcol
  have h := Research.GrowthRefinement.shape_cutoff_budget K.card d
    (Fintype.card I + Fintype.card J - 2) hK
  simpa only [Nat.mul_comm] using h

end Research.ReciprocalCount
