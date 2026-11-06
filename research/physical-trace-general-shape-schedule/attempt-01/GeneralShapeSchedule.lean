/-
SPDX-License-Identifier: Apache-2.0
Exact-numerator outer retry scheduling. The existing correction, numerator,
kernels and inner schedule are unchanged. Integer ceiling retains the full
shape-specific c0 instead of replacing it by a universal lower bound.
-/
import ResearchPhysicalTraceJoin.GeneralLinearSchedule
import ResearchPhysicalTraceJoin.GeneralCorrectionCode

set_option maxHeartbeats 1200000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open FirstSuccess ResidualMixture
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.CompletionRetryBudget
open scoped BigOperators

/-- Exact ceiling D/c for c>0. The zero-denominator convention is total,
but only positive reference numerators are used by the proved schedule. -/
def shapeCeiling (D c : ℕ) : ℕ := (D + c - 1) / c

def reciprocalRetryAttempts (K t : ℕ) : ℕ := K * (t + 1)

def reciprocalRetryPrecision (K t : ℕ) : ℕ :=
  t + 2 + Nat.clog 2 (reciprocalRetryAttempts K t)

/-- Literal catalog/count version of the shape-aware retry block. -/
def shapeRetryBlockCode (rs cs : List ℕ) (U : ℕ) : ℕ :=
  let p := (smallCellCatalog ((rs,cs),U)).length
  let D := 2 * (p * (p - 1))
  min (min D (4 * p)) (shapeCeiling D (correctionAllowanceCode rs cs U))

/-- Exact inspectable fixture data: p,c0,D,A,K,Rold,Rnew,hold,hnew. -/
def shapeScheduleCodeData (rs cs : List ℕ) (U t : ℕ) :
    ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let p := (smallCellCatalog ((rs,cs),U)).length
  let c0 := correctionAllowanceCode rs cs U
  let D := 2 * (p * (p - 1))
  let A := min D (4 * p)
  let K := shapeRetryBlockCode rs cs U
  (p,c0,D,A,K,reciprocalRetryAttempts A t,reciprocalRetryAttempts K t,
    reciprocalRetryPrecision A t,reciprocalRetryPrecision K t)

/-- The ceiling is the least integer whose product with c covers D. -/
theorem shapeCeiling_le_iff (D c k : ℕ) (hc : 0 < c) :
    shapeCeiling D c ≤ k ↔ D ≤ k * c := by
  unfold shapeCeiling
  constructor
  · intro h
    have ht : (D + c - 1) / c < k + 1 := by omega
    have hm := (Nat.div_lt_iff_lt_mul hc).mp ht
    rw [Nat.add_mul, Nat.one_mul] at hm
    omega
  · intro h
    have hm : D + c - 1 < (k + 1) * c := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have ht := (Nat.div_lt_iff_lt_mul hc).mpr hm
    omega

theorem shapeCeiling_product (D c : ℕ) (hc : 0 < c) :
    D ≤ shapeCeiling D c * c :=
  (shapeCeiling_le_iff D c _ hc).mp le_rfl

theorem shapeCeiling_positive (D c : ℕ) (hD : 0 < D) (hc : 0 < c) :
    0 < shapeCeiling D c := by
  have h := shapeCeiling_product D c hc
  by_contra hz
  have he : shapeCeiling D c = 0 := by omega
  rw [he, Nat.zero_mul] at h
  omega

private theorem linearBlock_product (p c0 : ℕ) (hc0 : 0 < c0) (htwo : p - 1 ≤ 2 * c0) :
    2 * (p * (p - 1)) ≤ min (2 * (p * (p - 1))) (4 * p) * c0 := by
  rw [Nat.min_def]
  split_ifs
  · have h := Nat.mul_le_mul_left (2 * (p * (p - 1))) (show 1 ≤ c0 by omega)
    simpa only [Nat.mul_one] using h
  · calc
      2 * (p * (p - 1)) = (2 * p) * (p - 1) := by ring
      _ ≤ (2 * p) * (2 * c0) := Nat.mul_le_mul_left _ htwo
      _ = (4 * p) * c0 := by ring

noncomputable section
open scoped Classical
variable (xs ys : List ℕ)

/-- Retain the universal block as a total fallback; on valid reference
inputs the minimum is proved equal to the exact ceiling. -/
def positiveTraceShapeBlock : ℕ :=
  min (positiveTraceLinearBlock xs ys)
    (shapeCeiling (positiveTraceOuterBlock xs ys)
      (inverseSupportAllowance (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys)))

def positiveTraceShapeAttempts (t : ℕ) : ℕ := reciprocalRetryAttempts (positiveTraceShapeBlock xs ys) t

def positiveTraceShapePrecision (t : ℕ) : ℕ := reciprocalRetryPrecision (positiveTraceShapeBlock xs ys) t

private theorem shapeNumerator_positive (hb : positiveTraceBranch xs ys = .reference) :
    0 < inverseSupportAllowance (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) := by
  have hg := positiveTraceReference_conditions xs ys hb
  exact inverseSupportAllowance_positive _ _ _ hg.1 hg.2.1 (by omega)

/-- Exact equality, rather than a heuristic clipping claim. -/
theorem positiveTraceShapeBlock_eq_ceiling (hb : positiveTraceBranch xs ys = .reference) :
    positiveTraceShapeBlock xs ys =
      shapeCeiling (positiveTraceOuterBlock xs ys)
        (inverseSupportAllowance (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys)) := by
  unfold positiveTraceShapeBlock
  apply min_eq_right
  apply (shapeCeiling_le_iff _ _ _ (shapeNumerator_positive xs ys hb)).mpr
  exact linearBlock_product _ _ (shapeNumerator_positive xs ys hb)
    (inverseSupportAllowance_twice _ _ _)

theorem positiveTraceShapeBlock_le_iff (hb : positiveTraceBranch xs ys = .reference) (k : ℕ) :
    positiveTraceShapeBlock xs ys ≤ k ↔
      positiveTraceOuterBlock xs ys ≤ k *
        inverseSupportAllowance (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) := by
  rw [positiveTraceShapeBlock_eq_ceiling xs ys hb]
  exact shapeCeiling_le_iff _ _ _ (shapeNumerator_positive xs ys hb)

theorem positiveTraceShapeBlock_positive (hb : positiveTraceBranch xs ys = .reference) :
    0 < positiveTraceShapeBlock xs ys := by
  rw [positiveTraceShapeBlock_eq_ceiling xs ys hb]
  exact shapeCeiling_positive _ _ (positiveTraceOuterBlock_positive xs ys hb)
    (shapeNumerator_positive xs ys hb)

/-- No larger retry count than the current linear schedule, for every t. -/
theorem positiveTraceShapeAttempts_le_linear (t : ℕ) :
    positiveTraceShapeAttempts xs ys t ≤ positiveTraceLinearAttempts xs ys t := by
  exact Nat.mul_le_mul (Nat.min_le_left _ _) le_rfl

theorem positiveTraceShapePrecision_eq (t : ℕ) :
    positiveTraceShapePrecision xs ys t =
      t + 2 + Nat.clog 2 (positiveTraceShapeAttempts xs ys t) := rfl

theorem positiveTraceShapePrecision_le_linear (t : ℕ) :
    positiveTraceShapePrecision xs ys t ≤ positiveTraceLinearPrecision xs ys t := by
  have hc := Nat.clog_mono_right 2 (positiveTraceShapeAttempts_le_linear xs ys t)
  change t + 2 + Nat.clog 2 (positiveTraceShapeAttempts xs ys t) ≤
    t + 2 + Nat.clog 2 (positiveTraceLinearAttempts xs ys t)
  omega

/-- The chosen block times the unchanged exact success allowance is at least one. -/
theorem positiveTraceShapeBlock_success (hb : positiveTraceBranch xs ys = .reference) :
    1 ≤ (positiveTraceShapeBlock xs ys : ℚ) * positiveTraceCorrectionSuccess xs ys := by
  have hD : (0 : ℚ) < positiveTraceOuterBlock xs ys :=
    Nat.cast_pos.mpr (positiveTraceOuterBlock_positive xs ys hb)
  have hp := shapeCeiling_product (positiveTraceOuterBlock xs ys)
    (inverseSupportAllowance (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys))
    (shapeNumerator_positive xs ys hb)
  rw [← positiveTraceShapeBlock_eq_ceiling xs ys hb] at hp
  have hpQ := (Nat.cast_le (α := ℚ)).mpr hp
  push_cast at hpQ
  change 1 ≤ (positiveTraceShapeBlock xs ys : ℚ) *
    ((inverseSupportAllowance (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) : ℚ) /
      (positiveTraceOuterBlock xs ys : ℚ))
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hD).mpr (by simpa only [one_mul] using hpQ)

theorem positiveTraceShapeBlock_reciprocal (hb : positiveTraceBranch xs ys = .reference) :
    1 / (positiveTraceShapeBlock xs ys : ℚ) ≤ positiveTraceCorrectionSuccess xs ys := by
  apply (div_le_iff₀ (Nat.cast_pos.mpr (positiveTraceShapeBlock_positive xs ys hb))).mpr
  simpa only [mul_comm] using positiveTraceShapeBlock_success xs ys hb

/-- Shared finite geometric arithmetic, independent of shape/state encodings. -/
theorem reciprocalRetry_failure_budget (s : ℚ) (K t : ℕ) (hK : 0 < K)
    (hrecip : 1 / (K : ℚ) ≤ s) (hs : s ≤ 1) :
    (1 - s)^(reciprocalRetryAttempts K t) ≤ dyadic (t + 1) := by
  have hq : 0 ≤ 1 - s := sub_nonneg.mpr hs
  have he : 1 - s ≤ 1 - 1 / (K : ℚ) := by linarith
  unfold reciprocalRetryAttempts
  rw [pow_mul]
  calc
    _ ≤ (1 / 2 : ℚ)^(t + 1) := by
      apply pow_le_pow_left₀ (pow_nonneg hq _)
      exact (pow_le_pow_left₀ hq he _).trans
        (Math115.PhysicalStarBudget.reciprocal_block K hK)
    _ = dyadic (t + 1) := by simp [dyadic]

theorem reciprocalRetry_draw_budget (K t : ℕ) :
    (reciprocalRetryAttempts K t : ℚ) * dyadic (reciprocalRetryPrecision K t) ≤ dyadic (t + 2) := by
  have hclog : (reciprocalRetryAttempts K t : ℚ) ≤ (2 : ℚ)^Nat.clog 2 (reciprocalRetryAttempts K t) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (reciprocalRetryAttempts K t)
  calc
    _ ≤ (2 : ℚ)^Nat.clog 2 (reciprocalRetryAttempts K t) * dyadic (reciprocalRetryPrecision K t) :=
      mul_le_mul_of_nonneg_right hclog (dyadic_positive _).le
    _ = dyadic (t + 2) := by
      unfold dyadic reciprocalRetryPrecision
      rw [pow_add]
      field_simp

theorem reciprocalRetry_budget (s : ℚ) (K t : ℕ) (hK : 0 < K)
    (hrecip : 1 / (K : ℚ) ≤ s) (hs : s ≤ 1) :
    (1 - s)^(reciprocalRetryAttempts K t) +
      (reciprocalRetryAttempts K t : ℚ) *
        (dyadic (reciprocalRetryPrecision K t) + dyadic (reciprocalRetryPrecision K t)) ≤ dyadic t := by
  have hf := reciprocalRetry_failure_budget s K t hK hrecip hs
  have hd := reciprocalRetry_draw_budget K t
  have hh := dyadic_succ t
  have hq := dyadic_succ (t + 1)
  nlinarith

theorem positiveTraceShape_budget (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) 7) (t : ℕ) :
    (1 - positiveTraceCorrectionSuccess xs ys)^(positiveTraceShapeAttempts xs ys t) +
      (positiveTraceShapeAttempts xs ys t : ℚ) *
        (dyadic (positiveTraceShapePrecision xs ys t) + dyadic (positiveTraceShapePrecision xs ys t)) ≤ dyadic t :=
  reciprocalRetry_budget _ _ t (positiveTraceShapeBlock_positive xs ys hb)
    (positiveTraceShapeBlock_reciprocal xs ys hb)
    (positiveTraceCorrectionSuccess_bounds xs ys hb start).2

def positiveTraceShapeScheduledLaw (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) 7)
    (fallback : Table (filteredMargin xs) (filteredMargin ys)) (t : ℕ) :
    RationalLaw (Table (listMargin xs) (listMargin ys)) :=
  positiveTraceCorrectedRetryLaw xs ys hb start (positiveTraceShapePrecision xs ys t)
    (positiveTraceShapePrecision xs ys t) fallback (positiveTraceShapeAttempts xs ys t)

/-- Reuse the old corrected-retry accuracy theorem; only its arithmetic
parameters change. No correction/kernel or runtime-exponent change is asserted. -/
theorem positiveTraceShapeScheduled_accuracy
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference)
    (start : DefectVertices (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys) 7)
    (fallback : Table (filteredMargin xs) (filteredMargin ys)) (t : ℕ) :
    letI := table_nonempty (listMargin xs) (listMargin ys) htotal
    variation (positiveTraceShapeScheduledLaw xs ys hb start fallback t)
      (uniformLaw (α := Table (listMargin xs) (listMargin ys))) ≤ dyadic t :=
  (positiveTraceCorrectedRetry_accuracy xs ys htotal hb start
    (positiveTraceShapePrecision xs ys t) (positiveTraceShapePrecision xs ys t)
    fallback (positiveTraceShapeAttempts xs ys t)).trans (positiveTraceShape_budget xs ys hb start t)

lemma shapeCatalog_length_card {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U : ℕ) :
    (smallCellCatalog ((List.ofFn r,List.ofFn c),U)).length =
      Fintype.card (Cells (firstPaperSmall r c U)) :=
  (Fintype.card_fin _).symm.trans
    (Fintype.card_congr (Math115.PhysicalComputedProposal.computedCellEquiv r c U))

/-- Literal list arithmetic computes exactly the typed block. -/
theorem positiveTraceShapeBlock_code :
    shapeRetryBlockCode (positiveMargins xs) (positiveMargins ys) (positiveTraceCutoff xs ys) =
      positiveTraceShapeBlock xs ys := by
  rw [← ofFn_filteredMargin xs, ← ofFn_filteredMargin ys]
  unfold shapeRetryBlockCode
  rw [shapeCatalog_length_card, correctionAllowanceCode_eq]
  rfl

/-- Exact typed meaning of every reported fixture number, including both
retry counts and both precisions. -/
theorem positiveTraceShapeScheduleData_code (t : ℕ) :
    shapeScheduleCodeData (positiveMargins xs) (positiveMargins ys) (positiveTraceCutoff xs ys) t =
      (Fintype.card (Cells (firstPaperSmall (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys))),
        inverseSupportAllowance (filteredMargin xs) (filteredMargin ys) (positiveTraceCutoff xs ys),
        positiveTraceOuterBlock xs ys,positiveTraceLinearBlock xs ys,positiveTraceShapeBlock xs ys,
        positiveTraceLinearAttempts xs ys t,positiveTraceShapeAttempts xs ys t,
        positiveTraceLinearPrecision xs ys t,positiveTraceShapePrecision xs ys t) := by
  rw [← ofFn_filteredMargin xs, ← ofFn_filteredMargin ys]
  unfold shapeScheduleCodeData shapeRetryBlockCode
  rw [shapeCatalog_length_card, correctionAllowanceCode_eq]
  rfl

/-- Two actual equal-total reference fixtures, with exact code-level data.
The code/type bridge above certifies the computed block; no timing claim follows. -/
theorem shapeSchedule_fixture10 :
    let xs := List.replicate 9 1 ++ [30000]
    positiveTraceBranch xs xs = .reference ∧ positiveTraceCutoff xs xs = 25938 ∧
      shapeScheduleCodeData (positiveMargins xs) (positiveMargins xs) (positiveTraceCutoff xs xs) 10 =
        (99,801,19404,396,25,4356,275,25,21) := by decide

theorem shapeSchedule_fixture20 :
    let xs := List.replicate 19 1 ++ [200000]
    positiveTraceBranch xs xs = .reference ∧ positiveTraceCutoff xs xs = 188518 ∧
      shapeScheduleCodeData (positiveMargins xs) (positiveMargins xs) (positiveTraceCutoff xs xs) 10 =
        (399,7201,317604,1596,45,17556,495,27,21) := by decide

end
end Math115.PhysicalTraceJoin
