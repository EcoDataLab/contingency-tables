/-
SPDX-License-Identifier: Apache-2.0
Uses the original weighted variance and child-profile definitions from the
pinned OpenAI #115 source. Endpoint-minimum is the global no-valley property,
which in particular excludes gaps inside positive support.
-/
import OAI.Combinatorics.ContingencyTables.Transport.FiniteRepairVariance
import Mathlib.Tactic
import Mathlib.Data.Nat.Dist
import Math115.PathDistanceSum

namespace Math115.PathVariance

open OAI.ContingencyTables
open IntegerWeightedTransport FiniteExposureVariance BalancedBox Finset Filter
open scoped BigOperators Topology

/-- The actual adjacent-child path energy, with each path edge counted once. -/
noncomputable def pathEnergy (z H : ℕ → ℝ) (U : ℕ) : ℝ :=
  ∑ j ∈ Finset.range U, min (z j) (z (j + 1)) * (H j - H (j + 1)) ^ 2

lemma pathEnergy_nonneg (z H : ℕ → ℝ) (U : ℕ)
    (hz : ∀ j ≤ U, 0 ≤ z j) : 0 ≤ pathEnergy z H U := by
  apply Finset.sum_nonneg
  intro j hj
  have hjU := Finset.mem_range.mp hj
  exact mul_nonneg (le_min (hz j (by omega)) (hz (j + 1) (by omega))) (sq_nonneg _)

/-- Retain the whole path-energy sum when telescoping between two children. -/
theorem weighted_pair_path_bound (z H : ℕ → ℝ) (U a b : ℕ)
    (hz : ∀ j ≤ U, 0 ≤ z j)
    (hminimum : ∀ r j s, r ≤ j → j ≤ s → s ≤ U → min (z r) (z s) ≤ z j)
    (hab : a ≤ b) (hb : b ≤ U) :
    min (z a) (z b) * (H a - H b) ^ 2 ≤
      (b - a : ℕ) * pathEnergy z H U := by
  have hmin : 0 ≤ min (z a) (z b) := le_min (hz a (by omega)) (hz b hb)
  have hpath := path_square H a (b - a)
  rw [Nat.add_sub_of_le hab] at hpath
  have hsteps : (∑ j ∈ Finset.range (b - a),
      min (z a) (z b) * (H (a + j) - H (a + j + 1)) ^ 2) ≤ pathEnergy z H U := by
    calc
      _ ≤ ∑ j ∈ Finset.range (b - a),
          min (z (a + j)) (z (a + j + 1)) * (H (a + j) - H (a + j + 1)) ^ 2 := by
        apply Finset.sum_le_sum
        intro j hj
        have hjn := Finset.mem_range.mp hj
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        exact le_min
          (hminimum a (a + j) b (by omega) (by omega) hb)
          (hminimum a (a + j + 1) b (by omega) (by omega) hb)
      _ ≤ pathEnergy z H U := by
        let q := fun j => min (z j) (z (j + 1)) * (H j - H (j + 1)) ^ 2
        change (∑ j ∈ Finset.range (b - a), q (a + j)) ≤ ∑ j ∈ Finset.range U, q j
        rw [← Finset.sum_image (fun r _ s _ hrs => Nat.add_left_cancel hrs)]
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro j hj
          obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hj
          have hrn := Finset.mem_range.mp hr
          exact Finset.mem_range.mpr (by omega)
        · intro j hj _
          have hjU := Finset.mem_range.mp hj
          exact mul_nonneg (le_min (hz j (by omega)) (hz (j + 1) (by omega))) (sq_nonneg _)
  calc
    _ ≤ min (z a) (z b) * ((b - a : ℕ) *
        ∑ j ∈ Finset.range (b - a), (H (a + j) - H (a + j + 1)) ^ 2) :=
      mul_le_mul_of_nonneg_left hpath hmin
    _ = (b - a : ℕ) * (∑ j ∈ Finset.range (b - a),
        min (z a) (z b) * (H (a + j) - H (a + j + 1)) ^ 2) := by
      rw [← Finset.mul_sum]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsteps (Nat.cast_nonneg _)

/-- Choosing a maximum-weight child removes the minimum from the pair bound. -/
theorem centered_at_mode_term (z H : ℕ → ℝ) (U m r : ℕ)
    (hz : ∀ j ≤ U, 0 ≤ z j)
    (hminimum : ∀ a j b, a ≤ j → j ≤ b → b ≤ U → min (z a) (z b) ≤ z j)
    (hm : m ≤ U) (hr : r ≤ U) (hmode : ∀ j ≤ U, z j ≤ z m) :
    z r * (H r - H m) ^ 2 ≤ (Nat.dist r m : ℝ) * pathEnergy z H U := by
  by_cases hrm : r ≤ m
  · have h := weighted_pair_path_bound z H U r m hz hminimum hrm hm
    simpa only [min_eq_left (hmode r hr), Nat.dist_eq_sub_of_le hrm] using h
  · have hmr : m ≤ r := by omega
    have h := weighted_pair_path_bound z H U m r hz hminimum hmr hr
    have hs : (H m - H r) ^ 2 = (H r - H m) ^ 2 := by ring
    simpa only [min_eq_right (hmode r hr), Nat.dist_eq_sub_of_le_right hmr, hs] using h

/-- A mode-dependent bound for the source's exact unnormalized variance.
Nonnegative weights and the global no-valley property suffice. -/
theorem weighted_path_variance_mode (z H : ℕ → ℝ) (U m : ℕ)
    (hz : ∀ j ≤ U, 0 ≤ z j)
    (hminimum : ∀ a j b, a ≤ j → j ≤ b → b ≤ U → min (z a) (z b) ≤ z j)
    (hm : m ≤ U) (hmode : ∀ j ≤ U, z j ≤ z m) :
    variance (fun j : Fin (U + 1) => z j.val) (fun j => H j.val) ≤
      (∑ j : Fin (U + 1), (Nat.dist j.val m : ℝ)) * pathEnergy z H U := by
  calc
    _ ≤ ∑ j : Fin (U + 1), z j.val * (H j.val - H m) ^ 2 :=
      variance_le_center (fun j : Fin (U + 1) => z j.val) (fun j => H j.val)
        (fun j => hz j.val (by omega)) (H m)
    _ ≤ ∑ j : Fin (U + 1), (Nat.dist j.val m : ℝ) * pathEnergy z H U := by
      exact Finset.sum_le_sum (fun j _ =>
        centered_at_mode_term z H U m j.val hz hminimum hm (by omega) hmode)
    _ = _ := by rw [Finset.sum_mul]

/-- The mode location gives the exact distance coefficient, improving the
universal triangular coefficient by `m*(U-m)`. -/
theorem weighted_path_variance_mode_sharp (z H : ℕ → ℝ) (U m : ℕ)
    (hz : ∀ j ≤ U, 0 ≤ z j)
    (hminimum : ∀ a j b, a ≤ j → j ≤ b → b ≤ U → min (z a) (z b) ≤ z j)
    (hm : m ≤ U) (hmode : ∀ j ≤ U, z j ≤ z m) :
    variance (fun j : Fin (U + 1) => z j.val) (fun j => H j.val) ≤
      ((U : ℝ) * ((U : ℝ) + 1) / 2 - (m : ℝ) * ((U : ℝ) - m)) *
        pathEnergy z H U := by
  simpa only [PathDistanceSum.sum_dist_eq_triangle_sub U m hm] using
    weighted_path_variance_mode z H U m hz hminimum hm hmode

/-- A global no-valley sequence has weighted path variance at most
`U*(U+1)/2` times its adjacent path energy. This covers all-zero mass,
singleton support, and zero weights outside the positive interval. -/
theorem weighted_path_variance_bound (z H : ℕ → ℝ) (U : ℕ)
    (hz : ∀ j ≤ U, 0 ≤ z j)
    (hminimum : ∀ a j b, a ≤ j → j ≤ b → b ≤ U → min (z a) (z b) ≤ z j) :
    variance (fun j : Fin (U + 1) => z j.val) (fun j => H j.val) ≤
      ((U : ℝ) * ((U : ℝ) + 1) / 2) * pathEnergy z H U := by
  classical
  obtain ⟨m, _, hmode⟩ := (Finset.univ : Finset (Fin (U + 1))).exists_max_image
    (fun j => z j.val) (by simp)
  have hm : m.val ≤ U := by omega
  have hmax : ∀ j ≤ U, z j ≤ z m.val := by
    intro j hj
    exact hmode ⟨j, by omega⟩ (Finset.mem_univ _)
  exact (weighted_path_variance_mode z H U m.val hz hminimum hm hmax).trans
    (mul_le_mul_of_nonneg_right (PathDistanceSum.sum_dist_le_triangle U m.val hm)
      (pathEnergy_nonneg z H U hz))

/-- Adjacent estimates may carry distinct localized energies. Their sum is
retained by the path inequality instead of bounding each by a common energy. -/
theorem weighted_path_variance_of_adjacent (z H E : ℕ → ℝ) (U : ℕ) (C : ℝ)
    (hz : ∀ j ≤ U, 0 ≤ z j)
    (hminimum : ∀ a j b, a ≤ j → j ≤ b → b ≤ U → min (z a) (z b) ≤ z j)
    (hadj : ∀ j < U, min (z j) (z (j + 1)) * (H j - H (j + 1)) ^ 2 ≤ C * E j) :
    variance (fun j : Fin (U + 1) => z j.val) (fun j => H j.val) ≤
      ((U : ℝ) * ((U : ℝ) + 1) / 2) * C * ∑ j ∈ Finset.range U, E j := by
  have henergy : pathEnergy z H U ≤ C * ∑ j ∈ Finset.range U, E j := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun j hj => hadj j (Finset.mem_range.mp hj))
  have hT : 0 ≤ (U : ℝ) * ((U : ℝ) + 1) / 2 := by positivity
  exact (weighted_path_variance_bound z H U hz hminimum).trans
    (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left henergy hT)

/-- Direct application to upstream's genuine positive child-profile sequence. -/
theorem child_variance_path_bound (f : (Bool → ℕ) → ℝ) (U : ℕ) (H : ℕ → ℝ)
    (hp : PositiveSlice f (fun _ => U) U) (hs : RemovalSlice f (fun _ => U) U) :
    variance (fun j : Fin (U + 1) => f (childProfile U j.val)) (fun j => H j.val) ≤
      ((U : ℝ) * ((U : ℝ) + 1) / 2) *
        pathEnergy (fun j => f (childProfile U j)) H U := by
  apply weighted_path_variance_bound (fun j => f (childProfile U j)) H U
  · intro j hj
    exact (hp _ (childProfile_inBox U j hj) (childProfile_total U j hj)).le
  · exact child_minimum f U hp hs

/-- The same estimate for upstream's hard-zero child masses, using its
actual soft-slice limit theorem for the global endpoint-minimum property. -/
theorem child_variance_limit_path_bound {K : Type*} {l : Filter K} [l.NeBot]
    (F : K → (Bool → ℕ) → ℝ) (f : (Bool → ℕ) → ℝ) (U : ℕ) (H : ℕ → ℝ)
    (hlim : ∀ z, Tendsto (fun t => F t z) l (nhds (f z)))
    (hsoft : ∀ᶠ t in l, PositiveSlice (F t) (fun _ => U) U ∧
      RemovalSlice (F t) (fun _ => U) U) :
    variance (fun j : Fin (U + 1) => f (childProfile U j.val)) (fun j => H j.val) ≤
      ((U : ℝ) * ((U : ℝ) + 1) / 2) *
        pathEnergy (fun j => f (childProfile U j)) H U := by
  apply weighted_path_variance_bound (fun j => f (childProfile U j)) H U
  · intro j hj
    apply ge_of_tendsto (hlim (childProfile U j))
    filter_upwards [hsoft] with t ht
    exact (ht.1 _ (childProfile_inBox U j hj) (childProfile_total U j hj)).le
  · exact child_minimum_limit F f U hlim hsoft

end Math115.PathVariance
