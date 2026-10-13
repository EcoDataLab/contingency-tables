import Research.WeightedHarmonicTrace
import Mathlib.Tactic

/-! Generic finite junction/star bridge. The repair map and accepted incidence
matrix are literal data. No contingency-table label or count lemma, global
variance inequality, or numerical Poincare conclusion is an input. -/
namespace Research.JunctionStarBridge

open OAI.ContingencyTables.FiniteExposureVariance
open scoped BigOperators Classical

variable {B D J : Type*} [Fintype B] [Fintype D] [Fintype J]

noncomputable def repairWeight (rho : D → B) (w : D → ℝ) (b : B) (d : D) : ℝ :=
  if rho d = b then w d else 0

noncomputable def repairMass (rho : D → B) (w : D → ℝ) (b : B) : ℝ :=
  WeightedHarmonicTrace.starMass (repairWeight rho w) b

noncomputable def repairMean (rho : D → B) (w g : D → ℝ) (b : B) : ℝ :=
  mean (repairWeight rho w b) g

noncomputable def harmonicMean (S : B → D → ℝ) (g : D → ℝ) (b : B) : ℝ :=
  mean (S b) g

noncomputable def starEnergy (S : B → D → ℝ) (g : D → ℝ) : ℝ :=
  ∑ b, variance (S b) g

noncomputable def repairNoise (rho : D → B) (w g : D → ℝ) : ℝ :=
  ∑ b, variance (repairWeight rho w b) g

noncomputable def centerError (rho : D → B) (w g : D → ℝ)
    (S : B → D → ℝ) : ℝ :=
  ∑ b, repairMass rho w b * (repairMean rho w g b - harmonicMean S g b)^2

noncomputable def junctionEnergy (src dst : J → B) (mu : J → ℝ) (F : B → ℝ) : ℝ :=
  ∑ j, mu j * (F (src j) - F (dst j))^2

/-- The energy used here is literally the existing weighted Schur-star
energy, including its ordered-energy factor one half and zero stars. -/
theorem starEnergy_eq_trace (S : B → D → ℝ) (hS : ∀ b d, 0 ≤ S b d)
    (g : D → ℝ) :
    starEnergy S g = WeightedHarmonicTrace.graphEnergy
      (WeightedHarmonicTrace.traceConductance (fun _ _ => 0) S) g := by
  rw [WeightedHarmonicTrace.trace_energy_eq_stars _ S hS g]
  simp [starEnergy, WeightedHarmonicTrace.graphEnergy]

lemma repairWeight_nonnegative (rho : D → B) (w : D → ℝ)
    (hw : ∀ d, 0 ≤ w d) (b : B) (d : D) : 0 ≤ repairWeight rho w b d := by
  unfold repairWeight
  split_ifs
  · exact hw d
  · exact le_refl _

lemma center_square_identity (w g : D → ℝ) (hw : ∀ d, 0 ≤ w d) (a : ℝ) :
    (∑ d, w d * (g d - a)^2) =
      variance w g + (∑ d, w d) * (mean w g - a)^2 := by
  have hmoment := mean_moment w g hw
  have hp (d : D) : w d * (g d - a)^2 =
      w d * (g d - mean w g)^2 +
      2 * (mean w g - a) * (w d * g d - w d * mean w g) +
      w d * (mean w g - a)^2 := by ring
  simp_rw [hp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp_rw [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul]
  unfold variance
  rw [hmoment]
  ring

lemma repairNoise_eq_sum (rho : D → B) (w g : D → ℝ) :
    repairNoise rho w g = ∑ d, w d * (g d - repairMean rho w g (rho d))^2 := by
  unfold repairNoise variance
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  simp [repairWeight, repairMean]

/-- Joint bound, derived by centering every repair fiber at its actual
accepted-star mean. Zero-mass fibers and empty finite sets are included. -/
theorem joint_noise_center_error (rho : D → B) (w g : D → ℝ)
    (S : B → D → ℝ) (hw : ∀ d, 0 ≤ w d) (hS : ∀ b d, 0 ≤ S b d)
    (hhalf : ∀ d, w d / 2 ≤ S (rho d) d) :
    repairNoise rho w g + centerError rho w g S ≤ 2 * starEnergy S g := by
  have hf (b : B) :
      variance (repairWeight rho w b) g +
        repairMass rho w b * (repairMean rho w g b - harmonicMean S g b)^2 =
      ∑ d, repairWeight rho w b d * (g d - harmonicMean S g b)^2 := by
    exact (center_square_identity (repairWeight rho w b) g
      (repairWeight_nonnegative rho w hw b) (harmonicMean S g b)).symm
  have hpoint (b : B) (d : D) : repairWeight rho w b d ≤ 2 * S b d := by
    unfold repairWeight
    split_ifs with he
    · have hh := hhalf d
      rw [he] at hh
      linarith
    · exact mul_nonneg (by norm_num) (hS b d)
  calc
    _ = ∑ b, ∑ d, repairWeight rho w b d * (g d - harmonicMean S g b)^2 := by
      unfold repairNoise centerError
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun b _ => hf b)
    _ ≤ ∑ b, ∑ d, 2 * (S b d * (g d - harmonicMean S g b)^2) := by
      apply Finset.sum_le_sum
      intro b _
      apply Finset.sum_le_sum
      intro d _
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hpoint b d) (sq_nonneg _)
    _ = _ := by
      unfold starEnergy variance harmonicMean
      simp_rw [← Finset.mul_sum]

lemma three_square (x y z : ℝ) : (x+y+z)^2 ≤ 3*x^2+3*y^2+3*z^2 := by
  nlinarith [sq_nonneg (x-y), sq_nonneg (x-z), sq_nonneg (y-z)]

/-- Actual shared-junction data give the finite energy bridge. The incoming
load condition is structural and contains no observable/energy inequality.
Table-specific construction of these data is a separate obligation. -/
theorem junction_energy_le_twelve_star
    (rho : D → B) (w : D → ℝ) (S : B → D → ℝ)
    (src dst : J → B) (shared : J → D) (mu : J → ℝ)
    (hw : ∀ d, 0 ≤ w d) (hS : ∀ b d, 0 ≤ S b d)
    (hhalf : ∀ d, w d / 2 ≤ S (rho d) d)
    (hmu : ∀ j, 0 ≤ mu j)
    (hinj : Function.Injective shared)
    (hrepair : ∀ j, rho (shared j) = src j)
    (hweight : ∀ j, mu j ≤ w (shared j))
    (hdest : ∀ j, mu j / 2 ≤ S (dst j) (shared j))
    (hincoming : ∀ b, (∑ j, if dst j = b then mu j else 0) ≤ repairMass rho w b)
    (g : D → ℝ) :
    junctionEnergy src dst mu (repairMean rho w g) ≤ 12 * starEnergy S g := by
  let F := repairMean rho w g
  let H := harmonicMean S g
  have hnoise : (∑ j, mu j * (F (src j) - g (shared j))^2) ≤ repairNoise rho w g := by
    calc
      _ ≤ ∑ j, w (shared j) * (g (shared j) - F (rho (shared j)))^2 := by
        apply Finset.sum_le_sum
        intro j _
        rw [hrepair j]
        have h := mul_le_mul_of_nonneg_right (hweight j) (sq_nonneg (F (src j) - g (shared j)))
        nlinarith only [h]
      _ ≤ ∑ d, w d * (g d - F (rho d))^2 :=
        OAI.ContingencyTables.ExcessContextProfiles.finite_injective_sum_le shared hinj
          (fun d => w d * (g d - F (rho d))^2) (fun d => mul_nonneg (hw d) (sq_nonneg _))
      _ = _ := (repairNoise_eq_sum rho w g).symm
  have hpair : Function.Injective (fun j => (dst j, shared j)) := by
    intro j k he
    exact hinj (congrArg Prod.snd he)
  have hstar : (∑ j, mu j * (g (shared j) - H (dst j))^2) ≤ 2 * starEnergy S g := by
    calc
      _ ≤ ∑ j, 2 * S (dst j) (shared j) * (g (shared j) - H (dst j))^2 := by
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
        linarith only [hdest j]
      _ ≤ ∑ p : B × D, 2 * S p.1 p.2 * (g p.2 - H p.1)^2 :=
        OAI.ContingencyTables.ExcessContextProfiles.finite_injective_sum_le _ hpair
          (fun p : B × D => 2 * S p.1 p.2 * (g p.2 - H p.1)^2)
          (fun p => mul_nonneg (mul_nonneg (by norm_num) (hS _ _)) (sq_nonneg _))
      _ = _ := by
        rw [Fintype.sum_prod_type]
        unfold starEnergy variance
        simp_rw [mul_assoc, ← Finset.mul_sum]
        rfl
  have herr : (∑ j, mu j * (H (dst j) - F (dst j))^2) ≤ centerError rho w g S := by
    have hs : (∑ j, mu j * (H (dst j) - F (dst j))^2) =
        ∑ b, (∑ j, if dst j = b then mu j else 0) * (H b - F b)^2 := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      simp
    rw [hs]
    unfold centerError
    apply Finset.sum_le_sum
    intro b _
    have h := mul_le_mul_of_nonneg_right (hincoming b) (sq_nonneg (H b - F b))
    dsimp [F, H] at h
    nlinarith only [h]
  have hsum : junctionEnergy src dst mu F ≤
      3 * (∑ j, mu j * (F (src j) - g (shared j))^2) +
      3 * (∑ j, mu j * (g (shared j) - H (dst j))^2) +
      3 * (∑ j, mu j * (H (dst j) - F (dst j))^2) := by
    unfold junctionEnergy
    simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    have h := three_square (F (src j) - g (shared j))
      (g (shared j) - H (dst j)) (H (dst j) - F (dst j))
    have hm := mul_le_mul_of_nonneg_left h (hmu j)
    nlinarith only [hm]
  have hjoint := joint_noise_center_error rho w g S hw hS hhalf
  change junctionEnergy src dst mu F ≤ _
  linarith

end Research.JunctionStarBridge
