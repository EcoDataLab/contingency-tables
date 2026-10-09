/-
SPDX-License-Identifier: Apache-2.0
Finite repair refinements. Only the defect-side lifted deviations
participate in the cross term; the base variance is retained separately.
-/
import OAI.Combinatorics.ContingencyTables.Transport.FiniteRepairVariance
import Mathlib.Analysis.Real.Sqrt

namespace Math115.RepairVarianceRefinement

open OAI.ContingencyTables.FiniteExposureVariance
open scoped BigOperators Classical

/-- Young's inequality with a freely chosen positive repair parameter. -/
lemma square_repair_young (x y a η : ℝ) (hη : 0 < η) :
    (x - a)^2 ≤ (1 + 1 / η) * (x - y)^2 + (1 + η) * (y - a)^2 := by
  have hη0 : η ≠ 0 := ne_of_gt hη
  have hid : η * ((1 + 1 / η) * (x - y)^2 + (1 + η) * (y - a)^2 -
      (x - a)^2) = ((x - y) - η * (y - a))^2 := by
    field_simp [hη0]
    <;> ring
  have hnon : 0 ≤ η * ((1 + 1 / η) * (x - y)^2 + (1 + η) * (y - a)^2 -
      (x - a)^2) := by rw [hid]; exact sq_nonneg _
  have h := (mul_nonneg_iff_of_pos_left hη).mp hnon
  linarith

/-- The square-root coefficient is nonnegative under the natural
transversal-variance hypothesis. -/
lemma repair_sqrt_coefficient_nonnegative (D C : ℝ) (hC : 0 ≤ C) :
    0 ≤ C + (Real.sqrt (D * C) + 1)^2 := by positivity

/-- The refinement never exceeds the source factor-two coefficient.
The difference is precisely `(sqrt(D*C) - 1)^2`. -/
lemma repair_sqrt_coefficient_le_source (D C : ℝ) (hD : 0 ≤ D) (hC : 0 ≤ C) :
    C + (Real.sqrt (D * C) + 1)^2 ≤ (1 + 2 * D) * C + 2 := by
  have hs := Real.sq_sqrt (mul_nonneg hD hC)
  nlinarith only [hs, sq_nonneg (Real.sqrt (D * C) - 1)]

/-- Keeping base variance outside the defect cross term also improves
the earlier coefficient obtained by one Hilbert-space triangle inequality. -/
lemma repair_sqrt_coefficient_le_triangle (D C : ℝ) (hD : 0 ≤ D) (hC : 0 ≤ C) :
    C + (Real.sqrt (D * C) + 1)^2 ≤ (Real.sqrt ((1 + D) * C) + 1)^2 := by
  have hs := Real.sq_sqrt (mul_nonneg hD hC)
  have ht := Real.sq_sqrt (mul_nonneg (show 0 ≤ 1 + D by linarith) hC)
  have hroot : Real.sqrt (D * C) ≤ Real.sqrt ((1 + D) * C) :=
    Real.sqrt_le_sqrt (by nlinarith only [hC])
  nlinarith only [hs, ht, hroot]

/-- A one-parameter refinement of the source's finite repair bound.
Taking `η = 1` recovers its original factor-two estimate. -/
theorem variance_sum_repair_young {B D T : Type*} [Fintype B] [Fintype D] [Fintype T]
    (w : B → ℝ) (v : D → ℝ) (H : B → ℝ) (K : D → ℝ)
    (R : D → B) (label : D → T) (hw : ∀ b, 0 ≤ w b) (hv : ∀ d, 0 ≤ v d)
    (hdom : ∀ d, v d ≤ w (R d)) (hinj : Function.Injective (fun d => (label d, R d)))
    (η : ℝ) (hη : 0 < η) :
    variance (Sum.elim w v) (Sum.elim H K) ≤
      (1 + (1 + η) * (Fintype.card T : ℝ)) * variance w H +
        (1 + 1 / η) * ∑ d, v d * (K d - H (R d))^2 := by
  have hcenter := variance_le_center (Sum.elim w v) (Sum.elim H K)
    (fun x => Sum.rec hw hv x) (mean w H)
  have hdefect : (∑ d, v d * (K d - mean w H)^2) ≤
      (1 + 1 / η) * (∑ d, v d * (K d - H (R d))^2) +
        (1 + η) * (∑ d, v d * (H (R d) - mean w H)^2) := by
    calc
      _ ≤ ∑ d, v d * ((1 + 1 / η) * (K d - H (R d))^2 +
          (1 + η) * (H (R d) - mean w H)^2) :=
        Finset.sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left
          (square_repair_young (K d) (H (R d)) (mean w H) η hη) (hv d))
      _ = _ := by
        have he (d : D) : v d * ((1 + 1 / η) * (K d - H (R d))^2 +
            (1 + η) * (H (R d) - mean w H)^2) =
            (1 + 1 / η) * (v d * (K d - H (R d))^2) +
              (1 + η) * (v d * (H (R d) - mean w H)^2) := by ring
        simp_rw [he]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hmass := repair_center_mass w v H R label hw hdom hinj (mean w H)
  change (∑ d, v d * (H (R d) - mean w H)^2) ≤
    (Fintype.card T : ℝ) * variance w H at hmass
  have hmass' := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 1 + η by linarith)
  rw [Fintype.sum_sum_type] at hcenter
  change variance (Sum.elim w v) (Sum.elim H K) ≤
    variance w H + (∑ d, v d * (K d - mean w H)^2) at hcenter
  nlinarith only [hcenter, hdefect, hmass']

/-- The Cauchy--Schwarz form of the same refinement includes every zero
case without dividing by a mass or by a variance. -/
theorem variance_sum_repair_sqrt {B D T : Type*} [Fintype B] [Fintype D] [Fintype T]
    (w : B → ℝ) (v : D → ℝ) (H : B → ℝ) (K : D → ℝ)
    (R : D → B) (label : D → T) (hw : ∀ b, 0 ≤ w b) (hv : ∀ d, 0 ≤ v d)
    (hdom : ∀ d, v d ≤ w (R d)) (hinj : Function.Injective (fun d => (label d, R d))) :
    variance (Sum.elim w v) (Sum.elim H K) ≤
      (1 + (Fintype.card T : ℝ)) * variance w H +
        (∑ d, v d * (K d - H (R d))^2) +
        2 * Real.sqrt ((Fintype.card T : ℝ) * variance w H *
          (∑ d, v d * (K d - H (R d))^2)) := by
  let V := variance w H
  let A := ∑ d, v d * (H (R d) - mean w H)^2
  let E := ∑ d, v d * (K d - H (R d))^2
  let Q := ∑ d, v d * (K d - H (R d)) * (H (R d) - mean w H)
  have hV : 0 ≤ V := Finset.sum_nonneg (fun b _ => mul_nonneg (hw b) (sq_nonneg _))
  have hA : 0 ≤ A := Finset.sum_nonneg (fun d _ => mul_nonneg (hv d) (sq_nonneg _))
  have hE : 0 ≤ E := Finset.sum_nonneg (fun d _ => mul_nonneg (hv d) (sq_nonneg _))
  have hmass : A ≤ (Fintype.card T : ℝ) * V :=
    repair_center_mass w v H R label hw hdom hinj (mean w H)
  have hsq (d : D) (x : ℝ) : (Real.sqrt (v d) * x)^2 = v d * x^2 := by
    rw [mul_pow, Real.sq_sqrt (hv d)]
  have hprod (d : D) (x y : ℝ) :
      (Real.sqrt (v d) * x) * (Real.sqrt (v d) * y) = v d * x * y := by
    calc
      _ = (Real.sqrt (v d))^2 * x * y := by ring
      _ = _ := by rw [Real.sq_sqrt (hv d)]
  have hcs : Q ≤ Real.sqrt E * Real.sqrt A := by
    simpa only [hprod, hsq] using
      Real.sum_mul_le_sqrt_mul_sqrt Finset.univ
        (fun d => Real.sqrt (v d) * (K d - H (R d)))
        (fun d => Real.sqrt (v d) * (H (R d) - mean w H))
  have hcross : Q ≤ Real.sqrt ((Fintype.card T : ℝ) * V * E) := by
    calc
      Q ≤ Real.sqrt E * Real.sqrt A := hcs
      _ ≤ Real.sqrt E * Real.sqrt ((Fintype.card T : ℝ) * V) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hmass) (Real.sqrt_nonneg _)
      _ = Real.sqrt ((Fintype.card T : ℝ) * V * E) := by
        rw [← Real.sqrt_mul hE]
        congr 1
        ring
  have hcenter := variance_le_center (Sum.elim w v) (Sum.elim H K)
    (fun x => Sum.rec hw hv x) (mean w H)
  rw [Fintype.sum_sum_type] at hcenter
  have he : (∑ d, v d * (K d - mean w H)^2) = E + A + 2 * Q := by
    have h (d : D) : v d * (K d - mean w H)^2 =
        v d * (K d - H (R d))^2 + v d * (H (R d) - mean w H)^2 +
          2 * (v d * (K d - H (R d)) * (H (R d) - mean w H)) := by ring
    simp_rw [h]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  change variance (Sum.elim w v) (Sum.elim H K) ≤
    V + (∑ d, v d * (K d - mean w H)^2) at hcenter
  rw [he] at hcenter
  change variance (Sum.elim w v) (Sum.elim H K) ≤
    (1 + (Fintype.card T : ℝ)) * V + E +
      2 * Real.sqrt ((Fintype.card T : ℝ) * V * E)
  nlinarith only [hcenter, hmass, hcross]

/-- A common graph-energy budget gives the sharper coefficient
`C + (sqrt(D*C) + 1)^2`, including `D*C = 0`. -/
theorem variance_repaired_energy_sqrt {B D T : Type*} [Fintype B] [Fintype D] [Fintype T]
    (w : B → ℝ) (v : D → ℝ) (H : B → ℝ) (K : D → ℝ)
    (R : D → B) (label : D → T) (hw : ∀ b, 0 ≤ w b) (hv : ∀ d, 0 ≤ v d)
    (hdom : ∀ d, v d ≤ w (R d)) (hinj : Function.Injective (fun d => (label d, R d)))
    (C E : ℝ) (hC : 0 ≤ C) (hE : 0 ≤ E)
    (hvar : variance w H ≤ C * E)
    (hrepair : (∑ d, v d * (K d - H (R d))^2) ≤ E) :
    variance (Sum.elim w v) (Sum.elim H K) ≤
      (C + (Real.sqrt ((Fintype.card T : ℝ) * C) + 1)^2) * E := by
  let A := ∑ d, v d * (K d - H (R d))^2
  have hA : 0 ≤ A := Finset.sum_nonneg (fun d _ => mul_nonneg (hv d) (sq_nonneg _))
  have hV : 0 ≤ variance w H :=
    Finset.sum_nonneg (fun b _ => mul_nonneg (hw b) (sq_nonneg _))
  have hTC : 0 ≤ (Fintype.card T : ℝ) * C := mul_nonneg (Nat.cast_nonneg _) hC
  have hproduct : (Fintype.card T : ℝ) * variance w H * A ≤
      ((Fintype.card T : ℝ) * C) * E^2 := by
    calc
      _ ≤ (Fintype.card T : ℝ) * (C * E) * E :=
        mul_le_mul (mul_le_mul_of_nonneg_left hvar (Nat.cast_nonneg _)) hrepair hA
          (by positivity)
      _ = _ := by ring
  have hroot : Real.sqrt ((Fintype.card T : ℝ) * variance w H * A) ≤
      Real.sqrt ((Fintype.card T : ℝ) * C) * E := by
    calc
      _ ≤ Real.sqrt (((Fintype.card T : ℝ) * C) * E^2) := Real.sqrt_le_sqrt hproduct
      _ = _ := by rw [Real.sqrt_mul hTC, Real.sqrt_sq hE]
  have hlin := mul_le_mul_of_nonneg_left hvar
    (show 0 ≤ 1 + (Fintype.card T : ℝ) by positivity)
  have hsqrt := Real.sq_sqrt hTC
  have hcoefficient : C + (Real.sqrt ((Fintype.card T : ℝ) * C) + 1)^2 =
      (1 + (Fintype.card T : ℝ)) * C + 1 +
        2 * Real.sqrt ((Fintype.card T : ℝ) * C) := by nlinarith only [hsqrt]
  have h := variance_sum_repair_sqrt w v H K R label hw hv hdom hinj
  change variance (Sum.elim w v) (Sum.elim H K) ≤
    (1 + (Fintype.card T : ℝ)) * variance w H + A +
      2 * Real.sqrt ((Fintype.card T : ℝ) * variance w H * A) at h
  calc
    _ ≤ (1 + (Fintype.card T : ℝ)) * (C * E) + E +
        2 * (Real.sqrt ((Fintype.card T : ℝ) * C) * E) := by linarith
    _ = _ := by rw [hcoefficient]; ring

end Math115.RepairVarianceRefinement
