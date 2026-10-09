/-
SPDX-License-Identifier: Apache-2.0
Concrete transportation-region sandwich for the actual fine Table count.
The comparison uses the full finite cell family and signed real reduced margins.
It makes no finite-bit realization or machine-cost claim.
-/
import Math115.PrefixFloorCover

namespace Math115.CompletionCountBound
open PrefixTransportation PrefixFloorCover OAI.ContingencyTables
open scoped BigOperators ENNReal
noncomputable section

/-- Prefix cells of every actual fine table, at spacing 1/k. -/
def fineCells {a b : ℕ} (k : ℕ) (R : Fin a → ℕ) (P : Fin b → ℕ) :
    Set (Interior a b → ℝ) :=
  ⋃ Z : LatticeCompletionFinite.FineTable k R P,
    LatticeCellVolume.prefixCell (k : ℤ) (tableAnchor Z)

/-- The fine-table margins divided by k are R+2b and P+2a. -/
lemma normalized_fine_feasible {a b : ℕ} (k : ℕ) (hk : 0 < k)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (Z : LatticeCompletionFinite.FineTable k R P) :
    Feasible (fun i => (R i : ℝ) + 2 * b) (fun j => (P j : ℝ) + 2 * a)
      ((1 / (k : ℝ)) • tableReal Z) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hZ := tableReal_feasible Z
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact mul_nonneg (by positivity) (hZ.1 i j)
  · intro i
    change (∑ j, (1 / (k : ℝ)) * tableReal Z i j) = _
    rw [← Finset.mul_sum, hZ.2.1 i]
    simp only [LatticeCompletionFinite.fineMargin, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    field_simp [ne_of_gt hkR]
  · intro j
    change (∑ i, (1 / (k : ℝ)) * tableReal Z i j) = _
    rw [← Finset.mul_sum, hZ.2.2 j]
    simp only [LatticeCompletionFinite.fineMargin, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
    field_simp [ne_of_gt hkR]

/-- Translating each fine cell by the prefix of the constant table 2/k
puts the entire cell union in the upper transportation region. -/
theorem upper_cell_cover {a b : ℕ} (k : ℕ) (hk : 0 < k)
    (R : Fin a → ℕ) (P : Fin b → ℕ) :
    (fun z => interiorPrefix (fun (_ : Fin a) (_ : Fin b) => 2 / (k : ℝ)) + z) ''
      fineCells k R P ⊆
      PrefixRegion (fun i => (R i : ℝ) + (b : ℝ) * (2 + 2 / (k : ℝ)))
        (fun j => (P j : ℝ) + (a : ℝ) * (2 + 2 / (k : ℝ))) := by
  rintro _ ⟨z, hz, rfl⟩
  obtain ⟨Z, hz⟩ := Set.mem_iUnion.mp hz
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have herror : ∀ p, 0 ≤ z p - interiorPrefix ((1 / (k : ℝ)) • tableReal Z) p ∧
      z p - interiorPrefix ((1 / (k : ℝ)) • tableReal Z) p < 1 / (k : ℝ) := by
    intro p
    rw [interiorPrefix_smul]
    have hp := LatticeCellVolume.prefixCell_error (k : ℤ) (tableAnchor Z) z hz p
    rw [tableAnchor_cast] at hp
    simpa only [Int.cast_natCast, Pi.smul_apply, smul_eq_mul, one_div_mul_eq_div] using hp
  have h := prefix_error_upper_containment _ _ _ (normalized_fine_feasible k hk R P Z)
    (1 / (k : ℝ)) (by positivity) z herror
  have hrowEq : (fun i => (R i : ℝ) + 2 * b + (b : ℝ) * (2 * (1 / (k : ℝ)))) =
      (fun i => (R i : ℝ) + (b : ℝ) * (2 + 2 / (k : ℝ))) := by
    funext i
    ring
  have hcolEq : (fun j => (P j : ℝ) + 2 * a + (a : ℝ) * (2 * (1 / (k : ℝ)))) =
      (fun j => (P j : ℝ) + (a : ℝ) * (2 + 2 / (k : ℝ))) := by
    funext j
    ring
  have hbuffer : (fun (_ : Fin a) (_ : Fin b) => 2 * (1 / (k : ℝ))) =
      (fun (_ : Fin a) (_ : Fin b) => 2 / (k : ℝ)) := by
    funext i j
    ring
  rw [hrowEq, hcolEq, hbuffer, add_comm z] at h
  exact h

theorem fine_cells_volume {a b : ℕ} (k : ℕ) (hk : 0 < k)
    (R : Fin a → ℕ) (P : Fin b → ℕ) :
    MeasureTheory.volume (fineCells k R P) =
      (Fintype.card (LatticeCompletionFinite.FineTable k R P) : ℝ≥0∞) *
        ENNReal.ofReal ((1 / (k : ℝ)) ^ ((a - 1) * (b - 1))) := by
  have h := LatticeCellVolume.prefix_lattice_cells_volume (k : ℤ) (by exact_mod_cast hk)
    (@tableAnchor a b (LatticeCompletionFinite.fineMargin k b R)
      (LatticeCompletionFinite.fineMargin k a P))
    (tableAnchor_injective _ _)
  simpa only [fineCells, Interior, Fintype.card_prod, Fintype.card_fin, Int.cast_natCast] using h

theorem fine_cells_volume_toReal {a b : ℕ} (k : ℕ) (hk : 0 < k)
    (R : Fin a → ℕ) (P : Fin b → ℕ) :
    (MeasureTheory.volume (fineCells k R P)).toReal =
      (Fintype.card (LatticeCompletionFinite.FineTable k R P) : ℝ) *
        (1 / (k : ℝ)) ^ ((a - 1) * (b - 1)) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  rw [fine_cells_volume k hk R P, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_ofReal (by positivity)]

theorem fine_cells_volume_le_upper {a b : ℕ} (k : ℕ) (hk : 0 < k)
    (R : Fin a → ℕ) (P : Fin b → ℕ) :
    MeasureTheory.volume (fineCells k R P) ≤ MeasureTheory.volume
      (PrefixRegion (fun i => (R i : ℝ) + (b : ℝ) * (2 + 2 / (k : ℝ)))
        (fun j => (P j : ℝ) + (a : ℝ) * (2 + 2 / (k : ℝ)))) := by
  exact LatticeCellVolume.volume_le_of_translated_subset _ _ _ (upper_cell_cover k hk R P)

/-- Geometric inflation from reduced original margins to upper fine-cell
margins under the actual stronger residual lower bounds. -/
def inflation (k L : ℕ) : ℝ := ((L : ℝ) + 2 + 2 / (k : ℝ)) / ((L : ℝ) - 2)

lemma inflation_pos (k L : ℕ) (hk : 0 < k) (hL : 2 < L) : 0 < inflation k L := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hLR : 2 < (L : ℝ) := by exact_mod_cast hL
  unfold inflation
  positivity

lemma inflation_ge_one (k L : ℕ) (hk : 0 < k) (hL : 2 < L) : 1 ≤ inflation k L := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hLR : 2 < (L : ℝ) := by exact_mod_cast hL
  unfold inflation
  apply (le_div_iff₀ (by linarith : 0 < (L : ℝ) - 2)).mpr
  have hdiv : 0 ≤ 2 / (k : ℝ) := by positivity
  linarith

lemma inflated_margin_ge_upper (k L m r : ℕ) (hk : 0 < k) (hL : 2 < L)
    (hr : m * L ≤ r) :
    (r : ℝ) + (m : ℝ) * (2 + 2 / (k : ℝ)) ≤
      inflation k L * ((r : ℝ) - 2 * (m : ℝ)) := by
  have hLR : 2 < (L : ℝ) := by exact_mod_cast hL
  have hmul : inflation k L * ((L : ℝ) - 2) = (L : ℝ) + 2 + 2 / (k : ℝ) := by
    unfold inflation
    exact div_mul_cancel₀ _ (by linarith)
  have hrR : (m : ℝ) * (L : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hnonneg : 0 ≤ (inflation k L - 1) * ((r : ℝ) - (m : ℝ) * (L : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr (inflation_ge_one k L hk hL)) (sub_nonneg.mpr hrR)
  have hmulm := congrArg (fun x : ℝ => (m : ℝ) * x) hmul
  nlinarith only [hmulm, hnonneg]

lemma shifted_totals_equal {a b : ℕ} (R : Fin a → ℕ) (P : Fin b → ℕ)
    (htotal : (∑ i, R i) = ∑ j, P j) (s : ℝ) :
    (∑ i, ((R i : ℝ) + (b : ℝ) * s)) = ∑ j, ((P j : ℝ) + (a : ℝ) * s) := by
  have ht : (∑ i, (R i : ℝ)) = ∑ j, (P j : ℝ) := by exact_mod_cast htotal
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ht]
  ring

lemma reduced_totals_equal {a b : ℕ} (R : Fin a → ℕ) (P : Fin b → ℕ)
    (htotal : (∑ i, R i) = ∑ j, P j) :
    (∑ i, ((R i : ℝ) - 2 * b)) = ∑ j, ((P j : ℝ) - 2 * a) := by
  have ht : (∑ i, (R i : ℝ)) = ∑ j, (P j : ℝ) := by exact_mod_cast htotal
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, ht]
  ring

/-- No division by a region's volume: the ENNReal sandwich remains valid
when the reduced region has volume zero. -/
theorem upper_volume_le_inflated_lower {a b : ℕ} (k L : ℕ) (hk : 0 < k) (hL : 2 < L)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (htotal : (∑ i, R i) = ∑ j, P j)
    (hR : ∀ i, b * L ≤ R i) (hP : ∀ j, a * L ≤ P j) :
    MeasureTheory.volume
      (PrefixRegion (fun i => (R i : ℝ) + (b : ℝ) * (2 + 2 / (k : ℝ)))
        (fun j => (P j : ℝ) + (a : ℝ) * (2 + 2 / (k : ℝ)))) ≤
      ENNReal.ofReal (inflation k L ^ ((a - 1) * (b - 1))) * MeasureTheory.volume
        (PrefixRegion (fun i => (R i : ℝ) - 2 * b) (fun j => (P j : ℝ) - 2 * a)) := by
  have htlow := reduced_totals_equal R P htotal
  have htscale : (∑ i, (inflation k L • (fun i => (R i : ℝ) - 2 * b)) i) =
      ∑ j, (inflation k L • (fun j => (P j : ℝ) - 2 * a)) j := by
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, htlow]
  have hmono := prefixRegion_volume_mono
    (fun i => (R i : ℝ) + (b : ℝ) * (2 + 2 / (k : ℝ)))
    (inflation k L • (fun i => (R i : ℝ) - 2 * b))
    (fun j => (P j : ℝ) + (a : ℝ) * (2 + 2 / (k : ℝ)))
    (inflation k L • (fun j => (P j : ℝ) - 2 * a))
    (fun i => inflated_margin_ge_upper k L b (R i) hk hL (hR i))
    (fun j => inflated_margin_ge_upper k L a (P j) hk hL (hP j))
    (shifted_totals_equal R P htotal _) htscale
  rw [prefixRegion_volume_scale _ _ (inflation k L) (inflation_pos k L hk hL)] at hmono
  exact hmono

/-- Full concrete ENNReal sandwich, using the upper fine-cell cover and
coarse floor cover of the lower region by actual original Table cells. -/
theorem fine_cells_volume_le_count {a b : ℕ} (k L : ℕ) (hk : 0 < k) (hL : 2 < L)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (htotal : (∑ i, R i) = ∑ j, P j)
    (hR : ∀ i, b * L ≤ R i) (hP : ∀ j, a * L ≤ P j) :
    MeasureTheory.volume (fineCells k R P) ≤
      ENNReal.ofReal (inflation k L ^ ((a - 1) * (b - 1))) *
        (Fintype.card (Table R P) : ℝ≥0∞) := by
  calc
    _ ≤ _ := fine_cells_volume_le_upper k hk R P
    _ ≤ _ := upper_volume_le_inflated_lower k L hk hL R P htotal hR hP
    _ ≤ _ := by
      gcongr
      exact lower_volume_le_card R P

/-- Actual fine-table count bound. Equal total margins and strong residual
lower bounds suffice; no positive-region-volume assumption is introduced. -/
theorem fine_card_le {a b : ℕ} (k L : ℕ) (hk : 0 < k) (hL : 2 < L)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (htotal : (∑ i, R i) = ∑ j, P j)
    (hR : ∀ i, b * L ≤ R i) (hP : ∀ j, a * L ≤ P j) :
    (Fintype.card (LatticeCompletionFinite.FineTable k R P) : ℝ) ≤
      inflation k L ^ ((a - 1) * (b - 1)) * (k : ℝ) ^ ((a - 1) * (b - 1)) *
        (Fintype.card (Table R P) : ℝ) := by
  have hkR : 0 < (k : ℝ) := by exact_mod_cast hk
  have hlambda : 0 < inflation k L := inflation_pos k L hk hL
  have h := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _))
    (fine_cells_volume_le_count k L hk hL R P htotal hR hP)
  rw [fine_cells_volume_toReal k hk R P, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal (by positivity)] at h
  have hm := mul_le_mul_of_nonneg_right h (show 0 ≤ (k : ℝ) ^ ((a - 1) * (b - 1)) by positivity)
  have hinv : (1 / (k : ℝ)) ^ ((a - 1) * (b - 1)) * (k : ℝ) ^ ((a - 1) * (b - 1)) = 1 := by
    rw [← mul_pow, one_div_mul_cancel (ne_of_gt hkR), one_pow]
  calc
    _ = ((Fintype.card (LatticeCompletionFinite.FineTable k R P) : ℝ) *
      (1 / (k : ℝ)) ^ ((a - 1) * (b - 1))) * (k : ℝ) ^ ((a - 1) * (b - 1)) := by
        rw [mul_assoc, hinv, mul_one]
    _ ≤ _ := hm
    _ = _ := by ring


/-- The same full fine-table count inequality using Nat.card. -/
theorem fine_nat_card_le {a b : ℕ} (k L : ℕ) (hk : 0 < k) (hL : 2 < L)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (htotal : (∑ i, R i) = ∑ j, P j)
    (hR : ∀ i, b * L ≤ R i) (hP : ∀ j, a * L ≤ P j) :
    (Nat.card (LatticeCompletionFinite.FineTable k R P) : ℝ) ≤
      inflation k L ^ ((a - 1) * (b - 1)) * (k : ℝ) ^ ((a - 1) * (b - 1)) *
        (Nat.card (Table R P) : ℝ) := by
  simpa only [Nat.card_eq_fintype_card] using fine_card_le k L hk hL R P htotal hR hP

end
end Math115.CompletionCountBound
