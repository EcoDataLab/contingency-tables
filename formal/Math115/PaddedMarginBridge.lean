/-
SPDX-License-Identifier: Apache-2.0

Connect the new all-donor count and scale interfaces to the actual upstream
paddedRows, paddedColumns, largePadding, and ordinary Table definitions.
The good-cardinality equivalence follows the private proof in OpenAI's
Sampling/Padding.lean at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
-/
import Math115.ScaleCertificate
import Math115.SmallEntrySwitching
import Math115.SmallEntryTail
import OAI.Combinatorics.ContingencyTables.Sampling.Padding

namespace Math115.PaddedMarginBridge

set_option maxHeartbeats 800000

open OAI.ContingencyTables
open scoped BigOperators Classical

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [Fintype I] in
/-- A marked padded cell contributes its own padding to its row margin. -/
theorem marked_row_margin (r : I → ℕ) (K : Finset (I × J)) (L : ℕ)
    {i : I} {j : J} (hij : (i, j) ∈ K) :
    r i + L ≤ paddedRows r (largePadding K L) i := by
  have hterm : L ≤ ∑ j', largePadding K L i j' := by
    calc
      L = largePadding K L i j := by simp [largePadding, hij]
      _ ≤ _ := Finset.single_le_sum (f := fun j' => largePadding K L i j')
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  unfold paddedRows
  omega

omit [Fintype J] in
/-- A marked padded cell contributes its own padding to its column margin. -/
theorem marked_column_margin (c : J → ℕ) (K : Finset (I × J)) (L : ℕ)
    {i : I} {j : J} (hij : (i, j) ∈ K) :
    c j + L ≤ paddedColumns c (largePadding K L) j := by
  have hterm : L ≤ ∑ i', largePadding K L i' j := by
    calc
      L = largePadding K L i j := by simp [largePadding, hij]
      _ ≤ _ := Finset.single_le_sum (f := fun i' => largePadding K L i' j)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  unfold paddedColumns
  omega

theorem marked_incident_margins (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (L U : ℕ) {p : I × J} (hp : p ∈ K)
    (hr : U ≤ r p.1) (hc : U ≤ c p.2) :
    U + L ≤ paddedRows r (largePadding K L) p.1 ∧
      U + L ≤ paddedColumns c (largePadding K L) p.2 := by
  constructor
  · exact (Nat.add_le_add_right hr L).trans (marked_row_margin r K L hp)
  · exact (Nat.add_le_add_right hc L).trans (marked_column_margin c K L hp)

/-- Export the successful-cell-test cardinality in terms of the source's
existing padding bijection. Empty marked sets and empty dimensions are allowed. -/
theorem large_padding_good_card (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (L : ℕ) :
    Fintype.card {Y : Table (paddedRows r (largePadding K L))
        (paddedColumns c (largePadding K L)) //
      ¬∃ p : K, Y.val p.val.1 p.val.2 < L} = Fintype.card (Table r c) := by
  let P := largePadding K L
  let T := Table (paddedRows r P) (paddedColumns c P)
  have heq (Y : T) : (¬∃ p : K, Y.val p.val.1 p.val.2 < L) ↔
      ∀ i j, P i j ≤ Y.val i j := by
    constructor
    · intro hb i j
      by_cases hij : (i, j) ∈ K
      · have hn : ¬Y.val i j < L := fun h => hb ⟨⟨(i, j), hij⟩, h⟩
        simpa [P, largePadding, hij] using (show L ≤ Y.val i j by omega)
      · simp [P, largePadding, hij]
    · intro hg
      rintro ⟨p, hp⟩
      have h := hg p.val.1 p.val.2
      have hm : (p.val.1, p.val.2) ∈ K := p.property
      simp only [P, largePadding, hm, ite_true] at h
      omega
  let he : {Y : T // ¬∃ p : K, Y.val p.val.1 p.val.2 < L} ≃
      {Y : T // ∀ i j, P i j ≤ Y.val i j} := Equiv.subtypeEquivRight heq
  rw [Fintype.card_congr he]
  exact successful_card r c P

omit [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] in
theorem union_count_mul_bound {α K : Type*} [Fintype α] [Fintype K]
    (event : K → α → Prop) (D C : ℕ)
    (hlocal : ∀ k, Fintype.card {x : α // event k x} * D ≤ Fintype.card α * C) :
    Fintype.card {x : α // ∃ k, event k x} * D ≤
      Fintype.card α * (Fintype.card K * C) := by
  classical
  calc
    _ ≤ (∑ k, Fintype.card {x : α // event k x}) * D :=
      Nat.mul_le_mul_right D (card_exists_le_sum event)
    _ = ∑ k, Fintype.card {x : α // event k x} * D := Finset.sum_mul _ _ _
    _ ≤ ∑ _k : K, Fintype.card α * C := Finset.sum_le_sum (fun k _ => hlocal k)
    _ = _ := by simp; ring

/-- Apply all-donor counting to each actual marked cell at the stronger
incident-margin lower bound `U+L`, then union-bound the bad enlarged tables.
The output denominator is `U+1`, rather than the coarser `U-L+1`. -/
theorem enlarged_bad_count (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (L U : ℕ)
    (hrow : ∀ p ∈ K, U ≤ r p.1) (hcol : ∀ p ∈ K, U ≤ c p.2) :
    Fintype.card {Y : Table (paddedRows r (largePadding K L))
        (paddedColumns c (largePadding K L)) //
      ∃ p : K, Y.val p.val.1 p.val.2 < L} * (U + 1) ≤
      Fintype.card (Table (paddedRows r (largePadding K L))
        (paddedColumns c (largePadding K L))) *
      (K.card * L * ((Fintype.card I - 1) * (Fintype.card J - 1))) := by
  classical
  let T := Table (paddedRows r (largePadding K L)) (paddedColumns c (largePadding K L))
  let e := (Fintype.card I - 1) * (Fintype.card J - 1)
  let event := fun (p : K) (Y : T) => Y.val p.val.1 p.val.2 < L
  have hlocal (p : K) : Fintype.card {Y : T // event p Y} * (U + 1) ≤
      Fintype.card T * (L * e) := by
    have hm := marked_incident_margins r c K L U p.property
      (hrow p.val p.property) (hcol p.val p.property)
    have hc := SmallEntrySwitching.all_donor_small_entry_count p.val.1 p.val.2
      (U + L) L hm.1 hm.2 (by omega)
    simpa only [T, e, event, Nat.add_sub_cancel, Fintype.card_eq_nat_card] using hc
  have h := union_count_mul_bound event (U + 1) (L * e) (fun p => by
    simpa only [Fintype.card_eq_nat_card] using hlocal p)
  simpa only [T, e, event, Fintype.card_eq_nat_card, Nat.card_eq_finsetCard, Nat.mul_assoc] using h

/-- The source's padded-count comparison, with the new count theorem and
generic enlarged-margin scale certificate discharged at their actual interfaces. -/
theorem padded_count_le_twice_original (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (d L U : ℕ)
    (hscale : EnlargedMarginPaddingConditions d L U)
    (hsize : Fintype.card I * Fintype.card J ≤ d)
    (hrow : ∀ p ∈ K, U ≤ r p.1) (hcol : ∀ p ∈ K, U ≤ c p.2) :
    Fintype.card (Table (paddedRows r (largePadding K L))
      (paddedColumns c (largePadding K L))) ≤ 2 * Fintype.card (Table r c) := by
  classical
  let T := Table (paddedRows r (largePadding K L)) (paddedColumns c (largePadding K L))
  let bad := fun Y : T => ∃ p : K, Y.val p.val.1 p.val.2 < L
  have hK : K.card ≤ d :=
    (show K.card ≤ Fintype.card I * Fintype.card J by
      simpa only [Fintype.card_prod] using K.card_le_univ).trans hsize
  have he : (Fintype.card I - 1) * (Fintype.card J - 1) ≤ d :=
    (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)).trans hsize
  have hpartition : Fintype.card {Y : T // bad Y} +
      Fintype.card {Y : T // ¬bad Y} = Fintype.card T := by
    rw [Fintype.card_subtype_compl]
    exact Nat.add_sub_of_le (Fintype.card_subtype_le _)
  have h := hscale.total_le_twice_good hK he hpartition
    (enlarged_bad_count r c K L U hrow hcol)
  rw [large_padding_good_card r c K L] at h
  exact h

theorem sharper_padded_count_le_twice_original (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (d : ℕ) (hd : 14 ≤ d)
    (hsize : Fintype.card I * Fintype.card J ≤ d)
    (hrow : ∀ p ∈ K, sharperU d ≤ r p.1) (hcol : ∀ p ∈ K, sharperU d ≤ c p.2) :
    Fintype.card (Table (paddedRows r (largePadding K (proposedL d)))
      (paddedColumns c (largePadding K (proposedL d)))) ≤ 2 * Fintype.card (Table r c) :=
  padded_count_le_twice_original r c K d (proposedL d) (sharperU d)
    (sharper_enlarged_margin_padding_scales d hd) hsize hrow hcol

/-- The stronger conditional-shift tail theorem improves the actual enlarged
fiber's denominator to `U+L+e`. No additional table-model premise is introduced. -/
theorem enlarged_bad_count_strong (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (L U : ℕ)
    (hrow : ∀ p ∈ K, U ≤ r p.1) (hcol : ∀ p ∈ K, U ≤ c p.2) :
    Fintype.card {Y : Table (paddedRows r (largePadding K L))
        (paddedColumns c (largePadding K L)) //
      ∃ p : K, Y.val p.val.1 p.val.2 < L} *
      (U + L + (Fintype.card I - 1) * (Fintype.card J - 1)) ≤
      Fintype.card (Table (paddedRows r (largePadding K L))
        (paddedColumns c (largePadding K L))) *
      (K.card * L * ((Fintype.card I - 1) * (Fintype.card J - 1))) := by
  classical
  let T := Table (paddedRows r (largePadding K L)) (paddedColumns c (largePadding K L))
  let e := (Fintype.card I - 1) * (Fintype.card J - 1)
  let event := fun (p : K) (Y : T) => Y.val p.val.1 p.val.2 < L
  have hlocal (p : K) : Fintype.card {Y : T // event p Y} * (U + L + e) ≤
      Fintype.card T * (L * e) := by
    have hm := marked_incident_margins r c K L U p.property
      (hrow p.val p.property) (hcol p.val p.property)
    have hc := SmallEntryTail.all_donor_small_entry_count_strong p.val.1 p.val.2
      (U + L) L hm.1 hm.2 (by omega)
    simpa only [T, e, event, Fintype.card_eq_nat_card] using hc
  have h := union_count_mul_bound event (U + L + e) (L * e) (fun p => by
    simpa only [Fintype.card_eq_nat_card] using hlocal p)
  simpa only [T, e, event, Fintype.card_eq_nat_card, Nat.card_eq_finsetCard, Nat.mul_assoc] using h

/-- A fully connected ordinary-table padding count at the explicit shape-aware
threshold. The threshold uses all possible cells, not the threshold-selected
marked set, so its definition has no circular dependence on that set.
No equal-total or nonempty-fiber assumption is required for this natural count. -/
theorem shape_aware_padded_count_le_twice_original (r : I → ℕ) (c : J → ℕ)
    (K : Finset (I × J)) (d : ℕ) (hd : 14 ≤ d)
    (hrow : ∀ p ∈ K,
      shapeAwareU d (Fintype.card I * Fintype.card J)
        ((Fintype.card I - 1) * (Fintype.card J - 1)) ≤ r p.1)
    (hcol : ∀ p ∈ K,
      shapeAwareU d (Fintype.card I * Fintype.card J)
        ((Fintype.card I - 1) * (Fintype.card J - 1)) ≤ c p.2) :
    Fintype.card (Table (paddedRows r (largePadding K (proposedL d)))
      (paddedColumns c (largePadding K (proposedL d)))) ≤ 2 * Fintype.card (Table r c) := by
  classical
  let e := (Fintype.card I - 1) * (Fintype.card J - 1)
  let cells := Fintype.card I * Fintype.card J
  let U := shapeAwareU d cells e
  let T := Table (paddedRows r (largePadding K (proposedL d)))
    (paddedColumns c (largePadding K (proposedL d)))
  let bad := fun Y : T => ∃ p : K, Y.val p.val.1 p.val.2 < proposedL d
  have hK : K.card ≤ cells := by
    simpa only [Fintype.card_prod] using K.card_le_univ
  have hpartition : Fintype.card {Y : T // bad Y} +
      Fintype.card {Y : T // ¬bad Y} = Fintype.card T := by
    rw [Fintype.card_subtype_compl]
    exact Nat.add_sub_of_le (Fintype.card_subtype_le _)
  have hcount := enlarged_bad_count_strong r c K (proposedL d) U hrow hcol
  have h := shape_aware_total_le_twice_good d cells e K.card
    (Fintype.card {Y : T // bad Y}) (Fintype.card {Y : T // ¬bad Y}) (Fintype.card T)
    hd hK hpartition hcount
  rw [large_padding_good_card r c K (proposedL d)] at h
  exact h

end Math115.PaddedMarginBridge
