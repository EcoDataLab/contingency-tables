import Marked.Survivor
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-! Centered L2 contraction implies the dominated-survivor TV allowance.
The contraction is an explicit hypothesis; deriving it from a gap, laziness,
or an iterated kernel is outside this module. -/
namespace Marked.Survivor
open scoped BigOperators Classical
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]

def mean (π g : X → ℝ) : ℝ := ∑ x, π x * g x
def energy (π g : X → ℝ) : ℝ := ∑ x, π x * (g x) ^ 2
def act (K : X → X → ℝ) (g : X → ℝ) : X → ℝ :=
  fun x => ∑ z, K x z * g z
def IsReversible (π : X → ℝ) (K : X → X → ℝ) : Prop :=
  ∀ x z, π x * K x z = π z * K z x

/-- A squared centered L2 operator bound, valid for every real centered
function, rather than just endpoint distributions. -/
def CenteredL2Contraction (π : X → ℝ) (K : X → X → ℝ) (ρ : ℝ) : Prop :=
  ∀ g : X → ℝ, mean π g = 0 → energy π (act K g) ≤ ρ ^ 2 * energy π g

lemma reversible_stationary (π : X → ℝ) (K : X → X → ℝ)
    (hK : IsMarkov K) (hrev : IsReversible π K) : bind π K = π := by
  funext z
  change (∑ x, π x * K x z) = π z
  calc
    (∑ x, π x * K x z) = ∑ x, π z * K z x :=
      Finset.sum_congr rfl (fun x _ => hrev x z)
    _ = π z := by rw [← Finset.mul_sum, hK.total, mul_one]

lemma energy_centered (π g : X → ℝ) (hπ : IsProbability π) :
    energy π (fun x => g x - mean π g) = energy π g - (mean π g) ^ 2 := by
  let m := mean π g
  calc
    energy π (fun x => g x - mean π g) =
        ∑ x, (π x * (g x)^2 - 2*m*(π x*g x) + m^2*π x) := by
      apply Finset.sum_congr rfl
      intro x _
      dsimp [m]
      ring
    _ = energy π g - 2*m*m + m^2*1 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [show (∑ x, π x * g x) = m from rfl,
        show (∑ x, π x) = 1 from hπ.total]
      rfl
    _ = energy π g - (mean π g)^2 := by dsimp [m]; ring

/-- The `1/4` variance bound uses `0≤g≤1` and normalized positive weights.
It does not condition on survival or divide by survivor mass. -/
theorem dominated_centered_energy (π g : X → ℝ) (hπ : IsProbability π)
    (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1) :
    energy π (fun x => g x - mean π g) ≤ 1/4 := by
  have he : energy π g ≤ mean π g := by
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_left _ (hπ.nonneg x)
    nlinarith [(hg x).1, (hg x).2]
  rw [energy_centered π g hπ]
  nlinarith [sq_nonneg (mean π g - 1/2)]

lemma centered_mean_zero (π g : X → ℝ) (hπ : IsProbability π) :
    mean π (fun x => g x - mean π g) = 0 := by
  simp only [mean, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [show (∑ x, π x) = 1 from hπ.total]
  ring

lemma weighted_cauchy_schwarz (π g : X → ℝ) (hπ : IsProbability π) :
    (∑ x, π x * |g x|)^2 ≤ energy π g := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (Finset.univ : Finset X))
    (r := fun x => π x * |g x|) (f := π) (g := fun x => π x * (g x)^2)
    (fun x _ => hπ.nonneg x)
    (fun x _ => mul_nonneg (hπ.nonneg x) (sq_nonneg (g x)))
    (fun x _ => by rw [mul_pow, sq_abs]; ring_nf; exact le_rfl)
  rw [show (∑ x, π x) = 1 from hπ.total, one_mul] at h
  exact h

lemma act_centered (K : X → X → ℝ) (g : X → ℝ) (m : ℝ)
    (hK : IsMarkov K) :
    act K (fun x => g x - m) = fun x => act K g x - m := by
  funext x
  simp only [act, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hK.total, one_mul]

omit [Fintype X] in
lemma survivor_density (π μ : X → ℝ) (hπpos : ∀ x, 0 < π x)
    (hμ : ∀ x, 0 ≤ μ x ∧ μ x ≤ π x) :
    ∀ x, 0 ≤ μ x / π x ∧ μ x / π x ≤ 1 := by
  intro x
  exact ⟨div_nonneg (hμ x).1 (hπpos x).le,
    (div_le_one (hπpos x)).mpr (hμ x).2⟩

lemma density_mean (π μ : X → ℝ) (hπpos : ∀ x, 0 < π x) :
    mean π (fun x => μ x / π x) = mass μ := by
  apply Finset.sum_congr rfl
  intro x _
  field_simp [(hπpos x).ne']

lemma reversible_density_action (π μ : X → ℝ) (K : X → X → ℝ)
    (hπpos : ∀ x, 0 < π x) (hrev : IsReversible π K) :
    bind μ K = fun z => π z * act K (fun x => μ x / π x) z := by
  funext z
  simp only [bind, act, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  calc
    μ x * K x z = (π x * K x z) * (μ x / π x) := by field_simp [(hπpos x).ne']
    _ = (π z * K z x) * (μ x / π x) := by rw [hrev]
    _ = π z * (K z x * (μ x / π x)) := by ring

/-- A finite reversible spacing kernel with centered L2 contraction `ρ`
mixes every dominated unnormalized survivor within `ρ/4` in TV. -/
theorem survivor_mixing_of_centered_l2 (π : X → ℝ) (K : X → X → ℝ) (ρ : ℝ)
    (hπ : IsProbability π) (hπpos : ∀ x, 0 < π x) (hK : IsMarkov K)
    (hrev : IsReversible π K) (hρ : 0 ≤ ρ)
    (hL2 : CenteredL2Contraction π K ρ) : SurvivorMixing π K (ρ/4) := by
  intro μ hμ
  let g : X → ℝ := fun x => μ x / π x
  let h : X → ℝ := fun x => g x - mean π g
  have hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1 := survivor_density π μ hπpos hμ
  have hm : mean π h = 0 := centered_mean_zero π g hπ
  have hv : energy π h ≤ 1/4 := dominated_centered_energy π g hπ hg
  have hc := hL2 h hm
  have hb := mul_le_mul_of_nonneg_left hv (sq_nonneg ρ)
  have heq : tv (bind μ K) (fun x => mass μ * π x) = (∑ x, π x * |act K h x|)/2 := by
    unfold tv
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    rw [reversible_density_action π μ K hπpos hrev]
    have ha : act K h x = act K g x - mass μ := by
      rw [show h = (fun x => g x - mean π g) from rfl, act_centered K g (mean π g) hK]
      rw [show mean π g = mass μ from density_mean π μ hπpos]
    rw [ha]
    change |π x * act K g x - mass μ * π x| = π x * |act K g x - mass μ|
    have he : π x * act K g x - mass μ * π x = π x * (act K g x - mass μ) := by ring
    rw [he, abs_mul, abs_of_nonneg (hπ.nonneg x)]
  have hcs := weighted_cauchy_schwarz π (act K h) hπ
  have hn := tv_nonneg (bind μ K) (fun x => mass μ * π x)
  rw [heq] at hn ⊢
  nlinarith [sq_nonneg ((∑ x, π x * |act K h x|)/2 - ρ/4)]

lemma stationary_success_le_one (π : X → ℝ) (A : X → Y → ℝ)
    (ν : Y → ℝ) (s : ℝ) (hπ : IsProbability π) (hν : IsProbability ν)
    (hA : IsTerminal A) (hsuccess : bind π A = fun y => s * ν y) : s ≤ 1 := by
  have hn : 0 ≤ mass (survive π A) :=
    Finset.sum_nonneg (fun x _ => mul_nonneg (hπ.nonneg x) (failure_nonneg A hA x))
  rw [stationary_failure_mass π A ν s hπ hν hsuccess] at hn
  linarith

/-- The burn-once dependent-attempt bound with its certified centered L2
premise fully exposed. `R+1` is the positive number of marks. -/
theorem burn_once_l2_bound (α π : X → ℝ) (K : X → X → ℝ)
    (A : X → Y → ℝ) (ν : Y → ℝ) (y₀ : Y) (s ρ : ℝ)
    (hπ : IsProbability π) (hπpos : ∀ x, 0 < π x) (hν : IsProbability ν)
    (hK : IsMarkov K) (hA : IsTerminal A) (hrev : IsReversible π K)
    (hsuccess : bind π A = fun y => s * ν y) (hρ : 0 ≤ ρ)
    (hL2 : CenteredL2Contraction π K ρ) (R : ℕ) :
    tv (bind α (output K A y₀ (R + 1))) ν ≤
      tv α π + (1-s) ^ (R + 1) + (R : ℝ) * (ρ/4) := by
  exact burn_once_bound α π K A ν y₀ s (ρ/4) hπ hν hK hA
    (reversible_stationary π K hK hrev) hsuccess
    (stationary_success_le_one π A ν s hπ hν hA hsuccess)
    (survivor_mixing_of_centered_l2 π K ρ hπ hπpos hK hrev hρ hL2) R

/-- The positive-mark-count form matching the documented sampler bound.
The initial endpoint-TV allowance `δ₀` is paid once, irrespective of `R`. -/
theorem spaced_terminal_bound (α π : X → ℝ) (K : X → X → ℝ)
    (A : X → Y → ℝ) (ν : Y → ℝ) (y₀ : Y) (s ρ δ₀ : ℝ)
    (hπ : IsProbability π) (hπpos : ∀ x, 0 < π x) (hν : IsProbability ν)
    (hK : IsMarkov K) (hA : IsTerminal A) (hrev : IsReversible π K)
    (hsuccess : bind π A = fun y => s * ν y) (hρ : 0 ≤ ρ)
    (hL2 : CenteredL2Contraction π K ρ) (hδ : tv α π ≤ δ₀)
    (R : ℕ) (hR : 0 < R) :
    tv (bind α (output K A y₀ R)) ν ≤
      δ₀ + (1-s) ^ R + ((R-1 : ℕ) : ℝ) * (ρ/4) := by
  cases R with
  | zero => omega
  | succ R =>
      simp only [Nat.succ_eq_add_one, Nat.add_sub_cancel]
      have hb := burn_once_l2_bound α π K A ν y₀ s ρ hπ hπpos hν hK hA hrev
        hsuccess hρ hL2 R
      linarith

end
end Marked.Survivor
