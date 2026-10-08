/-
SPDX-License-Identifier: Apache-2.0

Generic dense-width and padding interfaces, and a certificate for the reduced
scales in docs/scale-audit.md. The integer-width proof follows OpenAI's
DenseScales.integer_width_bounds at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
No claim about the complete sampler follows from the numerical certificate alone.
-/
import Mathlib.Tactic
import Mathlib.Data.Nat.Cast.Order.Field

namespace Math115

/-- Sufficient numerical hypotheses for the existing dense-bin geometry.
The normalizer budget is expressed without division, so it is usable by
integer parameter constructors as well as the real-volume proof. -/
structure DenseScaleConditions (d A B L : ℕ) : Prop where
  dimension_pos : 0 < d
  penalty_pos : 0 < A
  bin_pos : 0 < B
  padding_width : 2 * B ≤ L
  inner_volume : 8 * d ^ 3 ≤ B
  density_change : A * d ≤ B
  normalizer_budget : 8 * d ^ 2 * B + 8 * d ^ 3 * A ≤ A * B

/-- Sufficient numerical hypotheses for completion acceptance and unpadding
after the all-donor small-entry count is available. These do not assert that
the count theorem holds for bounded or weighted table models. -/
structure PaddingScaleConditions (d L U : ℕ) : Prop where
  dimension_pos : 0 < d
  padding_pos : 0 < L
  threshold_le : L ≤ U
  directional_acceptance : 4 * d ≤ L
  unpadding_budget : 2 * L * d ^ 2 ≤ U - L + 1

namespace DenseScaleConditions

theorem width_positive {d A B L : ℕ} (h : DenseScaleConditions d A B L)
    {s : ℕ} (hs : L ≤ s) : 0 < s / B :=
  Nat.div_pos (by have := h.padding_width; omega) h.bin_pos

/-- The actual floor-width comparison needed by DenseAffine, for any cell
scale `s` whose margin lower bound is `L`. -/
theorem width_bounds {d A B L : ℕ} (h : DenseScaleConditions d A B L)
    {s : ℕ} (hs : L ≤ s) :
    (s : ℝ) / (2 * B) ≤ (s / B : ℕ) ∧
      (s / B : ℕ) ≤ (s : ℝ) / B := by
  have hq := h.width_positive hs
  have hmod := Nat.mod_lt s h.bin_pos
  have hid := Nat.mod_add_div s B
  have hscale : s ≤ 2 * B * (s / B) := by nlinarith
  constructor
  · apply (div_le_iff₀ (show (0 : ℝ) < 2 * B by exact_mod_cast (by omega : 0 < 2 * B))).mpr
    have hscale' : (s : ℝ) ≤ 2 * (B : ℝ) * (s / B : ℕ) := by exact_mod_cast hscale
    nlinarith
  · exact Nat.cast_div_le

theorem density_change_le_one {d A B L : ℕ}
    (h : DenseScaleConditions d A B L) : (A : ℝ) * d / B ≤ 1 := by
  apply (div_le_one (by exact_mod_cast h.bin_pos : (0 : ℝ) < B)).mpr
  exact_mod_cast h.density_change

theorem inner_volume_loss_le_half {d A B L : ℕ}
    (h : DenseScaleConditions d A B L) : 4 * (d : ℝ) ^ 3 / B ≤ 1 / 2 := by
  apply (div_le_iff₀ (by exact_mod_cast h.bin_pos : (0 : ℝ) < B)).mpr
  have hscale : 8 * (d : ℝ) ^ 3 ≤ B := by exact_mod_cast h.inner_volume
  linarith

/-- This is the real-valued layer-sum premise used by the normalizer proof. -/
theorem layer_exponent_sum_le_quarter {d A B L : ℕ}
    (h : DenseScaleConditions d A B L) :
    2 * (d : ℝ) ^ 2 / A + 2 * (d : ℝ) ^ 3 / B ≤ 1 / 4 := by
  have hA : (0 : ℝ) < A := by exact_mod_cast h.penalty_pos
  have hB : (0 : ℝ) < B := by exact_mod_cast h.bin_pos
  have hbudget : 8 * (d : ℝ) ^ 2 * B + 8 * (d : ℝ) ^ 3 * A ≤ (A : ℝ) * B := by
    exact_mod_cast h.normalizer_budget
  have heq : 2 * (d : ℝ) ^ 2 / A + 2 * (d : ℝ) ^ 3 / B =
      (2 * (d : ℝ) ^ 2 * B + 2 * (d : ℝ) ^ 3 * A) / ((A : ℝ) * B) := by
    field_simp
  rw [heq]
  apply (div_le_iff₀ (mul_pos hA hB)).mpr
  linarith

end DenseScaleConditions

namespace PaddingScaleConditions

theorem denominator_pos {d L U : ℕ} (_h : PaddingScaleConditions d L U) :
    0 < U - L + 1 := by omega

theorem directional_rejection_le_half {d L U : ℕ}
    (h : PaddingScaleConditions d L U) : 2 * (d : ℝ) / L ≤ 1 / 2 := by
  apply (div_le_iff₀ (by exact_mod_cast h.padding_pos : (0 : ℝ) < L)).mpr
  have hscale : 4 * (d : ℝ) ≤ L := by exact_mod_cast h.directional_acceptance
  linarith

theorem union_numerator_budget {d L U : ℕ} (h : PaddingScaleConditions d L U)
    {g e : ℕ} (hg : g ≤ d) (he : e ≤ d) :
    2 * (g * L * e) ≤ U - L + 1 := by
  calc
    _ ≤ 2 * (d * L * d) := by gcongr
    _ = 2 * L * d ^ 2 := by ring
    _ ≤ _ := h.unpadding_budget

/-- Generic union-bound consequence: `g` is the number of marked large cells,
and `e` bounds the donor-label count per marked cell. -/
theorem unpadding_error_le_half {d L U : ℕ} (h : PaddingScaleConditions d L U)
    {g e : ℕ} (hg : g ≤ d) (he : e ≤ d) :
    (g : ℝ) * L * e / (U - L + 1 : ℕ) ≤ 1 / 2 := by
  apply (div_le_iff₀ (by exact_mod_cast h.denominator_pos :
    (0 : ℝ) < (U - L + 1 : ℕ))).mpr
  have hbudget : 2 * ((g : ℝ) * L * e) ≤ (U - L + 1 : ℕ) := by
    exact_mod_cast h.union_numerator_budget hg he
  linarith

/-- A counting interface for the all-donor theorem and the finite union bound.
No division or nonempty-fiber assumption is needed in this form. -/
theorem bad_count_le_half {d L U : ℕ} (h : PaddingScaleConditions d L U)
    {g e bad total : ℕ} (hg : g ≤ d) (he : e ≤ d)
    (hcount : bad * (U - L + 1) ≤ total * (g * L * e)) : 2 * bad ≤ total := by
  have hbudget := h.union_numerator_budget hg he
  have hden := h.denominator_pos
  have htwice : (2 * bad) * (U - L + 1) ≤ total * (U - L + 1) := by
    calc
      _ = 2 * (bad * (U - L + 1)) := by ring
      _ ≤ 2 * (total * (g * L * e)) := Nat.mul_le_mul_left 2 hcount
      _ = total * (2 * (g * L * e)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left total hbudget
  nlinarith

/-- If good and bad objects partition the fiber, at least half are good. -/
theorem total_le_twice_good {d L U : ℕ} (h : PaddingScaleConditions d L U)
    {g e bad good total : ℕ} (hg : g ≤ d) (he : e ≤ d)
    (hpartition : bad + good = total)
    (hcount : bad * (U - L + 1) ≤ total * (g * L * e)) : total ≤ 2 * good := by
  have := h.bad_count_le_half hg he hcount
  omega

end PaddingScaleConditions

def proposedA (d : ℕ) : ℕ := 16 * d ^ 2
def proposedB (d : ℕ) : ℕ := 16 * d ^ 3
def proposedL (d : ℕ) : ℕ := 32 * d ^ 3
def proposedU (d : ℕ) : ℕ := 128 * d ^ 5

theorem proposed_dense_scales (d : ℕ) (hd : 14 ≤ d) :
    DenseScaleConditions d (proposedA d) (proposedB d) (proposedL d) := by
  have hd0 : 0 < d := by omega
  refine ⟨hd0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold proposedA
    positivity
  · unfold proposedB
    positivity
  · unfold proposedL proposedB
    omega
  · unfold proposedB
    omega
  · apply le_of_eq
    unfold proposedA proposedB
    ring
  · apply le_of_eq
    unfold proposedA proposedB
    ring

theorem proposed_padding_scales (d : ℕ) (hd : 14 ≤ d) :
    PaddingScaleConditions d (proposedL d) (proposedU d) := by
  have hd0 : 0 < d := by omega
  have hd1 : 1 ≤ d := by omega
  have hp : d ^ 3 ≤ d ^ 5 := Nat.pow_le_pow_right hd1 (by decide)
  have hL : proposedL d ≤ proposedU d := by
    unfold proposedL proposedU
    omega
  have hsum : proposedL d + 2 * proposedL d * d ^ 2 ≤ proposedU d + 1 := by
    unfold proposedL proposedU
    calc
      32 * d ^ 3 + 2 * (32 * d ^ 3) * d ^ 2 = 32 * d ^ 3 + 64 * d ^ 5 := by ring
      _ ≤ 128 * d ^ 5 + 1 := by omega
  refine ⟨hd0, ?_, hL, ?_, ?_⟩
  · unfold proposedL
    positivity
  · have hself : d ≤ d ^ 3 := Nat.le_self_pow (by decide) d
    unfold proposedL
    omega
  · have hcancel := Nat.sub_add_cancel hL
    omega

theorem proposed_threshold_at_least_twice_padding (d : ℕ) (hd : 14 ≤ d) :
    2 * proposedL d ≤ proposedU d := by
  have hp : d ^ 3 ≤ d ^ 5 := Nat.pow_le_pow_right (by omega : 1 ≤ d) (by decide)
  unfold proposedL proposedU
  omega

/-- A ready-to-use real error bound for the reduced-parameter padding proof. -/
theorem proposed_unpadding_error_le_half (d g e : ℕ) (hd : 14 ≤ d)
    (hg : g ≤ d) (he : e ≤ d) :
    (g : ℝ) * proposedL d * e / (proposedU d - proposedL d + 1 : ℕ) ≤ 1 / 2 :=
  (proposed_padding_scales d hd).unpadding_error_le_half hg he

/-- A ready-to-use integer successful-cardinality bound, avoiding probabilities. -/
theorem proposed_total_le_twice_good (d g e bad good total : ℕ) (hd : 14 ≤ d)
    (hg : g ≤ d) (he : e ≤ d) (hpartition : bad + good = total)
    (hcount : bad * (proposedU d - proposedL d + 1) ≤ total * (g * proposedL d * e)) :
    total ≤ 2 * good :=
  (proposed_padding_scales d hd).total_le_twice_good hg he hpartition hcount

/-- A stronger padding interface uses the marked cell's own padding: its two
enlarged incident margins are at least `U+L`, giving denominator `U+1`.
The physical margin premise is proved separately in PaddedMarginBridge. -/
structure EnlargedMarginPaddingConditions (d L U : ℕ) : Prop where
  dimension_pos : 0 < d
  padding_pos : 0 < L
  threshold_pos : 0 < U
  directional_acceptance : 4 * d ≤ L
  unpadding_budget : 2 * L * d ^ 2 ≤ U + 1

namespace EnlargedMarginPaddingConditions

theorem union_numerator_budget {d L U : ℕ}
    (h : EnlargedMarginPaddingConditions d L U)
    {g e : ℕ} (hg : g ≤ d) (he : e ≤ d) : 2 * (g * L * e) ≤ U + 1 := by
  calc
    _ ≤ 2 * (d * L * d) := by gcongr
    _ = 2 * L * d ^ 2 := by ring
    _ ≤ _ := h.unpadding_budget

theorem unpadding_error_le_half {d L U : ℕ}
    (h : EnlargedMarginPaddingConditions d L U)
    {g e : ℕ} (hg : g ≤ d) (he : e ≤ d) :
    (g : ℝ) * L * e / (U + 1 : ℕ) ≤ 1 / 2 := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (U + 1 : ℕ))).mpr
  have hbudget : 2 * ((g : ℝ) * L * e) ≤ (U + 1 : ℕ) := by
    exact_mod_cast h.union_numerator_budget hg he
  linarith

theorem total_le_twice_good {d L U : ℕ}
    (h : EnlargedMarginPaddingConditions d L U)
    {g e bad good total : ℕ} (hg : g ≤ d) (he : e ≤ d)
    (hpartition : bad + good = total)
    (hcount : bad * (U + 1) ≤ total * (g * L * e)) : total ≤ 2 * good := by
  have hbudget := h.union_numerator_budget hg he
  have htwice : (2 * bad) * (U + 1) ≤ total * (U + 1) := by
    calc
      _ = 2 * (bad * (U + 1)) := by ring
      _ ≤ 2 * (total * (g * L * e)) := Nat.mul_le_mul_left 2 hcount
      _ = total * (2 * (g * L * e)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left total hbudget
  have hbad : 2 * bad ≤ total := by nlinarith
  omega

end EnlargedMarginPaddingConditions

/-- The optional stronger threshold keeps A, B, and L unchanged. -/
def sharperU (d : ℕ) : ℕ := 64 * d ^ 5

theorem sharper_enlarged_margin_padding_scales (d : ℕ) (hd : 14 ≤ d) :
    EnlargedMarginPaddingConditions d (proposedL d) (sharperU d) := by
  have h := proposed_padding_scales d hd
  refine ⟨h.dimension_pos, h.padding_pos, ?_, h.directional_acceptance, ?_⟩
  · have hd0 := h.dimension_pos
    unfold sharperU
    positivity
  · calc
      2 * proposedL d * d ^ 2 = sharperU d := by unfold proposedL sharperU; ring
      _ ≤ sharperU d + 1 := by omega

theorem sharper_unpadding_error_le_half (d g e : ℕ) (hd : 14 ≤ d)
    (hg : g ≤ d) (he : e ≤ d) :
    (g : ℝ) * proposedL d * e / (sharperU d + 1 : ℕ) ≤ 1 / 2 :=
  (sharper_enlarged_margin_padding_scales d hd).unpadding_error_le_half hg he

theorem sharper_total_le_twice_good (d g e bad good total : ℕ) (hd : 14 ≤ d)
    (hg : g ≤ d) (he : e ≤ d) (hpartition : bad + good = total)
    (hcount : bad * (sharperU d + 1) ≤ total * (g * proposedL d * e)) :
    total ≤ 2 * good :=
  (sharper_enlarged_margin_padding_scales d hd).total_le_twice_good hg he hpartition hcount

/-- Shape-aware threshold for a separately supplied linear-tail count. The
cell-count allowance is explicit, avoiding circular dependence on the large
rectangle selected by the threshold. Natural subtraction is harmless because
the maximum also enforces `U >= 2L`. -/
def shapeAwareU (d cells donors : ℕ) : ℕ :=
  max (2 * proposedL d) (2 * proposedL d * cells * donors - proposedL d - donors)

theorem shape_aware_threshold_at_least_twice_padding (d cells donors : ℕ) :
    2 * proposedL d ≤ shapeAwareU d cells donors := le_max_left _ _

/-- Numerical interface for the stronger linear-tail denominator `U+L+e`.
This theorem does not supply the linear-tail counting premise itself. -/
theorem shape_aware_linear_tail_budget (d cells donors marked : ℕ) (hm : marked ≤ cells) :
    2 * (marked * proposedL d * donors) ≤
      shapeAwareU d cells donors + proposedL d + donors := by
  have hmax := le_max_right (2 * proposedL d)
    (2 * proposedL d * cells * donors - proposedL d - donors)
  have hsub : 2 * proposedL d * cells * donors ≤
      (2 * proposedL d * cells * donors - proposedL d - donors) + proposedL d + donors := by omega
  calc
    _ ≤ 2 * (cells * proposedL d * donors) := by gcongr
    _ = 2 * proposedL d * cells * donors := by ring
    _ ≤ _ := by unfold shapeAwareU; omega

theorem shape_aware_linear_unpadding_error_le_half
    (d cells donors marked : ℕ) (hd : 14 ≤ d) (hm : marked ≤ cells) :
    (marked : ℝ) * proposedL d * donors /
      (shapeAwareU d cells donors + proposedL d + donors : ℕ) ≤ 1 / 2 := by
  have hL := (proposed_padding_scales d hd).padding_pos
  have hden : (0 : ℝ) < (shapeAwareU d cells donors + proposedL d + donors : ℕ) := by
    exact_mod_cast (by omega : 0 < shapeAwareU d cells donors + proposedL d + donors)
  apply (div_le_iff₀ hden).mpr
  have hbudget : 2 * ((marked : ℝ) * proposedL d * donors) ≤
      (shapeAwareU d cells donors + proposedL d + donors : ℕ) := by
    exact_mod_cast shape_aware_linear_tail_budget d cells donors marked hm
  linarith

theorem shape_aware_total_le_twice_good
    (d cells donors marked bad good total : ℕ) (hd : 14 ≤ d) (hm : marked ≤ cells)
    (hpartition : bad + good = total)
    (hcount : bad * (shapeAwareU d cells donors + proposedL d + donors) ≤
      total * (marked * proposedL d * donors)) : total ≤ 2 * good := by
  let D := shapeAwareU d cells donors + proposedL d + donors
  have hL := (proposed_padding_scales d hd).padding_pos
  have hD : 0 < D := by dsimp [D]; omega
  have hbudget := shape_aware_linear_tail_budget d cells donors marked hm
  have htwice : (2 * bad) * D ≤ total * D := by
    calc
      _ = 2 * (bad * D) := by ring
      _ ≤ 2 * (total * (marked * proposedL d * donors)) := Nat.mul_le_mul_left 2 hcount
      _ = total * (2 * (marked * proposedL d * donors)) := by ring
      _ ≤ _ := Nat.mul_le_mul_left total hbudget
  have hbad : 2 * bad ≤ total := by nlinarith
  omega

end Math115
