/- Generic finite star elimination, with OAI's unnormalized variance.
No physical graph instantiation is asserted here. -/
import OAI.Combinatorics.ContingencyTables.Transport.FiniteRepairVariance
import Mathlib.Tactic

namespace Math115.FiniteStarTrace

open OAI.ContingencyTables.FiniteExposureVariance
open scoped BigOperators Classical

variable {X B D : Type*} [Fintype X] [Fintype B] [Fintype D]

/-- Pairwise energy identity, valid also for zero total mass. The double
sum counts both orientations, so the denominator has the factor two. -/
theorem variance_eq_pairwise (w g : X → ℝ) (hw : ∀ x, 0 ≤ w x) :
    variance w g = (∑ x, ∑ y, w x * w y * (g x - g y)^2) /
      (2 * ∑ x, w x) := by
  have halg (x y : X) : w x * w y * (g x - g y)^2 =
      (w x * (g x)^2) * w y + w x * (w y * (g y)^2) -
        (w x * g x) * (2 * (w y * g y)) := by ring
  have hpair : (∑ x, ∑ y, w x * w y * (g x - g y)^2) =
      2 * (∑ x, w x) * (∑ x, w x * (g x)^2) -
        2 * (∑ x, w x * g x)^2 := by
    simp_rw [halg, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    ring
  by_cases hz : (∑ x, w x) = 0
  · have hzero := zero_mass_weights w hw hz
    simp [variance, hzero]
  · rw [variance_formula w g hw, hpair]
    field_simp

noncomputable def fiberWeight (R : D → B) (b : B) (d : D) : ℝ :=
  if R d = b then 1 else 0

noncomputable def fiberMean (R : D → B) (g : D → ℝ) (b : B) : ℝ :=
  mean (fiberWeight R b) g

omit [Fintype B] in
theorem fiber_mass_eq_card (R : D → B) (b : B) :
    (∑ d, fiberWeight R b d) =
      ((Finset.univ.filter (fun d => R d = b)).card : ℝ) := by
  unfold fiberWeight
  rw [← Finset.sum_filter]
  simp

omit [Fintype B] in
theorem fiber_mean_eq_average (R : D → B) (g : D → ℝ) (b : B) :
    fiberMean R g b = (∑ d ∈ Finset.univ.filter (fun d => R d = b), g d) /
      ((Finset.univ.filter (fun d => R d = b)).card : ℝ) := by
  unfold fiberMean mean
  rw [fiber_mass_eq_card]
  congr 1
  simp only [fiberWeight, ite_mul, one_mul, zero_mul, Finset.sum_filter]

noncomputable def harmonicExtension (R : D → B) (g : D → ℝ) : B ⊕ D → ℝ :=
  Sum.elim (fiberMean R g) g

/-- Half the ordered DD energy; for unit undirected adjacency this counts
each edge once. Symmetry is not needed for the elimination identity. -/
noncomputable def defectEnergy (W : D → D → ℝ) (g : D → ℝ) : ℝ :=
  (∑ x, ∑ y, W x y * (g x - g y)^2) / 2

/-- This decomposition states that there are no B-B edges and every defect
has exactly its R-neighbor among B, with unit star-edge conductance. -/
noncomputable def decomposedEnergy (R : D → B) (W : D → D → ℝ)
    (F : B ⊕ D → ℝ) : ℝ :=
  defectEnergy W (fun d => F (Sum.inr d)) +
    ∑ b, ∑ d, fiberWeight R b d * (F (Sum.inr d) - F (Sum.inl b))^2

/-- Pairwise refresh energy on each repair fiber. The denominator is twice
the fiber cardinality because the numerator counts ordered pairs. Empty
fibers contribute zero under Lean's real division convention. -/
noncomputable def traceEnergy (R : D → B) (W : D → D → ℝ) (g : D → ℝ) : ℝ :=
  defectEnergy W g + ∑ b,
    (∑ x, ∑ y, fiberWeight R b x * fiberWeight R b y * (g x - g y)^2) /
      (2 * ∑ d, fiberWeight R b d)

omit [Fintype B] in
theorem star_energy_eq_pairwise (R : D → B) (g : D → ℝ) (b : B) :
    (∑ d, fiberWeight R b d * (g d - fiberMean R g b)^2) =
      (∑ x, ∑ y, fiberWeight R b x * fiberWeight R b y * (g x - g y)^2) /
        (2 * ∑ d, fiberWeight R b d) := by
  exact variance_eq_pairwise (fiberWeight R b) g (fun d => by
    unfold fiberWeight
    split <;> norm_num)

omit [Fintype B] in
/-- Choosing a linear order counts each unordered pair exactly once.
This is the precise `1 / fiber_card` star-elimination formula. -/
theorem star_energy_eq_unordered [LinearOrder D]
    (R : D → B) (g : D → ℝ) (b : B) :
    (∑ d, fiberWeight R b d * (g d - fiberMean R g b)^2) =
      (∑ x, ∑ y, if x < y then
        fiberWeight R b x * fiberWeight R b y * (g x - g y)^2 else 0) /
          (∑ d, fiberWeight R b d) := by
  let A := fun x y => fiberWeight R b x * fiberWeight R b y * (g x - g y)^2
  have hs (x y : D) : A x y = A y x := by dsimp [A]; ring
  have hd (x : D) : A x x = 0 := by simp [A]
  have hp (x y : D) : A x y =
      (if x < y then A x y else 0) + (if y < x then A y x else 0) := by
    rcases lt_trichotomy x y with h | h | h
    · simp [h, not_lt_of_ge (le_of_lt h)]
    · subst y; simp [hd]
    · simp [h, not_lt_of_ge (le_of_lt h), hs]
  have hpair : (∑ x, ∑ y, A x y) =
      2 * (∑ x, ∑ y, if x < y then A x y else 0) := by
    have hswap : (∑ x, ∑ y, if y < x then A y x else 0) =
        ∑ x, ∑ y, if x < y then A x y else 0 := Finset.sum_comm
    calc
      _ = ∑ x, ∑ y,
          ((if x < y then A x y else 0) + (if y < x then A y x else 0)) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        exact hp x y
      _ = _ := by simp_rw [Finset.sum_add_distrib]; rw [hswap]; ring
  rw [star_energy_eq_pairwise]
  change (∑ x, ∑ y, A x y) / (2 * ∑ d, fiberWeight R b d) =
    (∑ x, ∑ y, if x < y then A x y else 0) / (∑ d, fiberWeight R b d)
  rw [hpair]
  simp only [mul_div_mul_left _ _ (show (2 : ℝ) ≠ 0 by norm_num)]

theorem harmonic_energy_eq_trace (R : D → B) (W : D → D → ℝ) (g : D → ℝ) :
    decomposedEnergy R W (harmonicExtension R g) = traceEnergy R W g := by
  unfold decomposedEnergy harmonicExtension traceEnergy
  simp only [Sum.elim_inr, Sum.elim_inl]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  exact star_energy_eq_pairwise R g b

/-- Fiber averaging minimizes the energy among all balanced-vertex values
with the defect observable fixed. No sign assumption on DD energy is used. -/
theorem harmonic_energy_min (R : D → B) (W : D → D → ℝ)
    (g : D → ℝ) (h : B → ℝ) :
    decomposedEnergy R W (harmonicExtension R g) ≤
      decomposedEnergy R W (Sum.elim h g) := by
  unfold decomposedEnergy harmonicExtension
  simp only [Sum.elim_inl, Sum.elim_inr]
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro b _
  exact variance_le_center (fiberWeight R b) g (fun d => by
    unfold fiberWeight
    split <;> norm_num) (h b)

/-- Restricting the vertex set can only decrease unnormalized variance.
The extension's values on B can be arbitrary. -/
theorem variance_restrict_le (h : B → ℝ) (g : D → ℝ) :
    variance (fun _ : D => 1) g ≤
      variance (fun _ : B ⊕ D => 1) (Sum.elim h g) := by
  let a := mean (fun _ : B ⊕ D => 1) (Sum.elim h g)
  have hc := variance_le_center (fun _ : D => (1 : ℝ)) g (fun _ => by norm_num) a
  have hb : 0 ≤ ∑ b : B, (h b - a)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  simp only [one_mul] at hc
  calc
    _ ≤ ∑ d, (g d - a)^2 := hc
    _ ≤ (∑ b, (h b - a)^2) + ∑ d, (g d - a)^2 := le_add_of_nonneg_left hb
    _ = _ := by
      unfold variance
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, one_mul, a]

/-- Generic bridge. A physical application must supply both the full
Poincare inequality and the actual graph decomposition. Neither is hidden
in a new axiom or claimed by this theorem. -/
theorem poincare_transfer (R : D → B) (W : D → D → ℝ)
    (Efull : (B ⊕ D → ℝ) → ℝ) (C : ℝ)
    (hdecomp : ∀ F, Efull F = decomposedEnergy R W F)
    (hfull : ∀ F, variance (fun _ : B ⊕ D => 1) F ≤ C * Efull F)
    (g : D → ℝ) :
    variance (fun _ : D => 1) g ≤ C * traceEnergy R W g := by
  have hv := variance_restrict_le (fiberMean R g) g
  have hp := hfull (harmonicExtension R g)
  rw [hdecomp, harmonic_energy_eq_trace] at hp
  exact hv.trans hp


end Math115.FiniteStarTrace
