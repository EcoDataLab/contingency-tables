import Math115.ReferenceEdgeAcceptance
import Math115.DilatedCompletionMargins

namespace Research.AcceptancePadding

open OAI.ContingencyTables
open OAI.ContingencyTables.CompletionTranslation
open OAI.ContingencyTables.SmallGraphProfiles
open OAI.ContingencyTables.PhysicalCompletionFibres
open OAI.ContingencyTables.FirstPaperProfiles
open OAI.ContingencyTables.FirstPaperPhysicalMarginal
open OAI.ContingencyTables.CompletionCounts
open OAI.ContingencyTables.PaddedCompletions
open Math115.ReferenceEdgeAcceptance Math115.DilatedCompletionMargins
open scoped BigOperators Classical

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- A large residual row receives padding in every large column. This holds
for every physical state and any capacities B, including truncated slacks. -/
theorem residual_row_floor (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (B : I → J → ℕ) (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (i : LargeRows r U) :
    Fintype.card (LargeColumns c U) * L ≤
      residualRows (firstPaperSmall r c U) B r c L z i.val := by
  unfold residualRows
  rw [rowLargeCount_rectangle, ite_eq_left i.property]
  omega

theorem residual_column_floor (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (B : I → J → ℕ) (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (j : LargeColumns c U) :
    Fintype.card (LargeRows r U) * L ≤
      residualColumns (firstPaperSmall r c U) B r c L z j.val := by
  unfold residualColumns
  rw [columnLargeCount_rectangle, ite_eq_left j.property]
  omega

/-- Exact physical graph half-acceptance, including exchange, designated
repair, and reverse repair across small/large boundaries. Only the acceptance
scale changes; literal source translation and cap identification are retained. -/
theorem reference_edge_acceptance_block_floor (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (B : I → J → ℕ) (hB : ∀ i j, firstPaperSmall r c U i j = true → B i j = U)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (hscale : 3 * (Fintype.card {i : LargeRows r U // i ≠ i₀} *
      Fintype.card {j : LargeColumns c U // j ≠ j₀}) ≤
      min (Fintype.card (LargeRows r U)) (Fintype.card (LargeColumns c U)) * L)
    (hcap : ∀ z : PhysicalStates (firstPaperSmall r c U) B r c L, ∀ i j,
      firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hxy : physicalAdjacent r c U L B hB x y) :
    (blockCount (referenceRows r c U L B i₀) (referenceColumns r c U L B j₀) x : ℝ) / 2 ≤
      acceptedCount (referenceRows r c U L B i₀) (referenceColumns r c U L B j₀) x y := by
  have hD := physical_reference_adjustment_bounds r c U L B hB i₀ j₀ hcap x y hxy
  have h := between_accepted_half_count
    (referenceRows r c U L B i₀ x) (referenceRows r c U L B i₀ y)
    (referenceColumns r c U L B j₀ x) (referenceColumns r c U L B j₀ y)
    (reference_totals r c U L B i₀ j₀ y (hcap y)) hD
    (min (Fintype.card (LargeRows r U)) (Fintype.card (LargeColumns c U)) * L) hscale
    (fun p _ => (Nat.mul_le_mul_right L (min_le_right _ _)).trans
      (residual_row_floor r c U L B x ((Equiv.optionSubtypeNe i₀) p.1)))
    (fun p _ => (Nat.mul_le_mul_right L (min_le_left _ _)).trans
      (residual_column_floor r c U L B x ((Equiv.optionSubtypeNe j₀) p.2)))
  have hR : (blockCount (referenceRows r c U L B i₀) (referenceColumns r c U L B j₀) x : ℝ) ≤
      2 * acceptedCount (referenceRows r c U L B i₀) (referenceColumns r c U L B j₀) x y := by
    exact_mod_cast h
  linarith

/-- A positive integer scale with no unsafe division, including zero donors.
The nonempty-block class gives s≥1. -/
def floorPadding (R C : ℕ) : ℕ :=
  max 1 ((3 * ((R - 1) * (C - 1)) + min R C - 1) / min R C)


/-- Ceiling with natural subtraction; all scale uses have a positive divisor. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

theorem ceilDiv_mul_lower (a b : ℕ) (hb : 0 < b) : a ≤ b * ceilDiv a b := by
  have hm := Nat.mod_lt (a + b - 1) hb
  have h := Nat.div_add_mod (a + b - 1) b
  unfold ceilDiv
  omega

theorem ceilDiv_le (a b k : ℕ) (hb : 0 < b) (h : a ≤ b * k) :
    ceilDiv a b ≤ k := by
  apply (Nat.div_le_iff_le_mul hb).mpr
  have h' : a ≤ k * b := by simpa only [Nat.mul_comm] using h
  exact Nat.sub_le_sub_right (Nat.add_le_add_right h' b) 1

theorem floorPadding_budget (R C : ℕ) (hR : 0 < R) (hC : 0 < C) :
    3 * ((R - 1) * (C - 1)) ≤ min R C * floorPadding R C := by
  have hs : 0 < min R C := lt_min hR hC
  have h := ceilDiv_mul_lower (3 * ((R - 1) * (C - 1))) (min R C) hs
  exact h.trans (Nat.mul_le_mul_left _ (le_max_right _ _))

theorem floorPadding_le_three_max (R C : ℕ) (hR : 0 < R) (hC : 0 < C) :
    floorPadding R C ≤ 3 * max R C := by
  have hs : 0 < min R C := lt_min hR hC
  have ht : 1 ≤ max R C := hR.trans_le (le_max_left _ _)
  have he : (R - 1) * (C - 1) ≤ min R C * max R C := by
    rw [min_mul_max]
    exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have hceil := ceilDiv_le (3 * ((R - 1) * (C - 1))) (min R C) (3 * max R C) hs
    (by nlinarith)
  exact max_le (by omega) hceil

/-- The conservative width guard is retained, and the count-growth budget is
exactly the free-padding sufficient condition with full-table donor count. -/
def cutoff (m n R C : ℕ) : ℕ :=
  max 2 (max (2 * floorPadding R C)
    (ceilDiv (47 * (R * C) * floorPadding R C * ((m - 1) * (n - 1))) 32 - 1))

theorem cutoff_budget (m n R C : ℕ) :
    47 * (R * C) * floorPadding R C * ((m - 1) * (n - 1)) ≤
      32 * (cutoff m n R C + 1) := by
  have h := ceilDiv_mul_lower
    (47 * (R * C) * floorPadding R C * ((m - 1) * (n - 1))) 32 (by decide)
  have hc : ceilDiv
      (47 * (R * C) * floorPadding R C * ((m - 1) * (n - 1))) 32 - 1 ≤
      cutoff m n R C := (le_max_right _ _).trans (le_max_right _ _)
  omega

/-- A dimension-only envelope for the checked cutoff. This does not assume
that classification at another U survives: R and C must be the actual counts. -/
theorem cutoff_le (m n R C d : ℕ) (hd : 2 ≤ d)
    (hR : 0 < R) (hC : 0 < C) (hRm : R ≤ m) (hCn : C ≤ n)
    (hmn : m * n ≤ d) : cutoff m n R C ≤ 5 * d ^ 2 * max R C := by
  let t := max R C
  have ht : 1 ≤ t := hR.trans_le (le_max_left _ _)
  have hL : floorPadding R C ≤ 3 * t := floorPadding_le_three_max R C hR hC
  have hg : R * C ≤ d := (Nat.mul_le_mul hRm hCn).trans hmn
  have he : (m - 1) * (n - 1) ≤ d :=
    (Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)).trans hmn
  have hprod := Nat.mul_le_mul (Nat.mul_le_mul hg hL) he
  have hnum : 47 * (R * C) * floorPadding R C * ((m - 1) * (n - 1)) ≤
      141 * d ^ 2 * t := by nlinarith only [hprod]
  have hceil := ceilDiv_le
    (47 * (R * C) * floorPadding R C * ((m - 1) * (n - 1))) 32
    (5 * d ^ 2 * t) (by decide) (by nlinarith only [hnum])
  have htwo : 2 ≤ 5 * d ^ 2 * t := by nlinarith [sq_nonneg (d : ℤ)]
  have hsq : 2 ≤ d ^ 2 := by nlinarith
  have hmul := Nat.mul_le_mul_right (5 * t) hsq
  have hwidth : 2 * floorPadding R C ≤ 5 * d ^ 2 * t := by nlinarith only [hL, hmul]
  exact max_le htwo (max_le hwidth ((Nat.sub_le _ _).trans hceil))

/-- Exact scalar inverse-gap envelope from the shape degree, effective width,
and strengthened acceptance scales. A is an integer aspect allowance. -/
theorem bounded_aspect_gap (d t A p V U K : ℕ) (hp : p ≤ d) (hV : V ≤ U)
    (hU : U ≤ 5 * d ^ 2 * t) (haspect : t ^ 2 ≤ A * d)
    (hK : K ≤ 16 * p ^ 4 * V ^ 4) : K ≤ 10000 * A ^ 2 * d ^ 14 := by
  have hp4 := Nat.pow_le_pow_left hp 4
  have hV4 := Nat.pow_le_pow_left hV 4
  have hU4 := Nat.pow_le_pow_left hU 4
  have ht4 := Nat.pow_le_pow_left haspect 2
  calc
    K ≤ 16 * p ^ 4 * V ^ 4 := hK
    _ ≤ 16 * d ^ 4 * U ^ 4 := Nat.mul_le_mul (Nat.mul_le_mul_left 16 hp4) hV4
    _ ≤ 16 * d ^ 4 * (5 * d ^ 2 * t) ^ 4 := Nat.mul_le_mul_left _ hU4
    _ = 10000 * d ^ 12 * (t ^ 2) ^ 2 := by ring
    _ ≤ 10000 * d ^ 12 * (A * d) ^ 2 := Nat.mul_le_mul_left _ ht4
    _ = 10000 * A ^ 2 * d ^ 14 := by ring


/-- Preselect before classifying margins; therefore this is an unconditional
outer-shape cutoff, without a fixed-point or persistence assumption. -/
def outerCutoff (m n d : ℕ) : ℕ := 5 * d ^ 2 * max m n

theorem cutoff_le_outerCutoff (m n R C d : ℕ) (hd : 2 ≤ d)
    (hR : 0 < R) (hC : 0 < C) (hRm : R ≤ m) (hCn : C ≤ n)
    (hmn : m * n ≤ d) : cutoff m n R C ≤ outerCutoff m n d := by
  have ht : max R C ≤ max m n := max_le_max hRm hCn
  exact (cutoff_le m n R C d hd hR hC hRm hCn hmn).trans
    (Nat.mul_le_mul_left _ ht)

theorem outerCutoff_budget (m n R C d : ℕ) (hd : 2 ≤ d)
    (hR : 0 < R) (hC : 0 < C) (hRm : R ≤ m) (hCn : C ≤ n)
    (hmn : m * n ≤ d) :
    47 * (R * C) * floorPadding R C * ((m - 1) * (n - 1)) ≤
      32 * (outerCutoff m n d + 1) := by
  exact (cutoff_budget m n R C).trans (Nat.mul_le_mul_left 32
    (Nat.add_le_add_right (cutoff_le_outerCutoff m n R C d hd hR hC hRm hCn hmn) 1))

/-- Classifying at the preselected outer cutoff permits floorPadding directly,
with no scalar hscale supplied by the caller. The actual graph predicates,
reference choice, and capacity conditions are all present. -/
theorem reference_edge_acceptance_floorPadding (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (B : I → J → ℕ)
    (hB : ∀ i j, firstPaperSmall r c U i j = true → B i j = U)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (hcap : ∀ z : PhysicalStates (firstPaperSmall r c U) B r c
        (floorPadding (Fintype.card (LargeRows r U)) (Fintype.card (LargeColumns c U))), ∀ i j,
      firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c
        (floorPadding (Fintype.card (LargeRows r U)) (Fintype.card (LargeColumns c U))) z k) ≤ B i j)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c
      (floorPadding (Fintype.card (LargeRows r U)) (Fintype.card (LargeColumns c U))))
    (hxy : physicalAdjacent r c U
      (floorPadding (Fintype.card (LargeRows r U)) (Fintype.card (LargeColumns c U))) B hB x y) :
    (blockCount (referenceRows r c U
      (floorPadding (Fintype.card (LargeRows r U)) (Fintype.card (LargeColumns c U))) B i₀)
      (referenceColumns r c U
      (floorPadding (Fintype.card (LargeRows r U)) (Fintype.card (LargeColumns c U))) B j₀) x : ℝ) / 2 ≤
      acceptedCount (referenceRows r c U
      (floorPadding (Fintype.card (LargeRows r U)) (Fintype.card (LargeColumns c U))) B i₀)
      (referenceColumns r c U
      (floorPadding (Fintype.card (LargeRows r U)) (Fintype.card (LargeColumns c U))) B j₀) x y := by
  apply reference_edge_acceptance_block_floor r c U _ B hB i₀ j₀ _ hcap x y hxy
  have hr := Fintype.card_congr (Equiv.optionSubtypeNe i₀)
  have hc := Fintype.card_congr (Equiv.optionSubtypeNe j₀)
  simp only [Fintype.card_option] at hr hc
  have hr' : Fintype.card {i : LargeRows r U // i ≠ i₀} = Fintype.card (LargeRows r U) - 1 := by omega
  have hc' : Fintype.card {j : LargeColumns c U // j ≠ j₀} = Fintype.card (LargeColumns c U) - 1 := by omega
  rw [hr', hc']
  exact floorPadding_budget _ _ (by omega) (by omega)

end Research.AcceptancePadding
