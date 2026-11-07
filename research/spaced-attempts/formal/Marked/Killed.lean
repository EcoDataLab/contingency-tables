import Marked.L2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.QuadraticDiscriminant

namespace Marked.Survivor
open scoped BigOperators Classical
noncomputable section
variable {X Y : Type*} [Fintype X] [Fintype Y]

def inner (π u v : X → ℝ) : ℝ := ∑ x, π x * u x * v x

def IsPSD (π : X → ℝ) (K : X → X → ℝ) : Prop :=
  ∀ u : X → ℝ, 0 ≤ inner π u (act K u)

lemma inner_self (π u : X → ℝ) : inner π u u = energy π u := by
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma inner_comm (π u v : X → ℝ) : inner π u v = inner π v u := by
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma energy_nonneg (π u : X → ℝ) (hπ : IsProbability π) : 0 ≤ energy π u :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (hπ.nonneg x) (sq_nonneg (u x)))

lemma inner_cs (π u v : X → ℝ) (hπ : IsProbability π) :
    (inner π u v)^2 ≤ energy π u * energy π v := by
  have h := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (Finset.univ : Finset X))
    (r := fun x => π x * u x * v x)
    (f := fun x => π x * (u x)^2) (g := fun x => π x * (v x)^2)
    (fun x _ => mul_nonneg (hπ.nonneg x) (sq_nonneg _))
    (fun x _ => mul_nonneg (hπ.nonneg x) (sq_nonneg _))
    (fun x _ => by ring_nf; exact le_rfl)
  exact h

lemma mean_act (π g : X → ℝ) (K : X → X → ℝ)
    (hstat : bind π K = π) : mean π (act K g) = mean π g := by
  simp only [mean, act, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [← mul_assoc, ← Finset.sum_mul]
  simp_rw [show ∀ z, (∑ x, π x * K x z) = π z from fun z => congrFun hstat z]

lemma inner_centered_act (π g : X → ℝ) (K : X → X → ℝ)
    (hπ : IsProbability π) (hK : IsMarkov K) (hstat : bind π K = π) :
    inner π (fun x => g x - mean π g) (act K (fun x => g x - mean π g)) =
      inner π g (act K g) - (mean π g)^2 := by
  rw [act_centered K g (mean π g) hK]
  calc
    inner π (fun x => g x - mean π g) (fun x => act K g x - mean π g) =
      inner π g (act K g) - mean π g * mean π g - mean π g * mean π (act K g) +
        (mean π g)^2 * mass π := by
      calc
        _ = ∑ x, (π x * g x * act K g x - mean π g * (π x * g x) -
          mean π g * (π x * act K g x) + (mean π g)^2 * π x) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = _ := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
          rfl
    _ = _ := by rw [hπ.total, mean_act π g K hstat]; ring

/-- Centered L2 contraction yields the finite quadratic comparison with refresh. -/
lemma quadratic_comparison (π g : X → ℝ) (K : X → X → ℝ) (ρ : ℝ)
    (hπ : IsProbability π) (hK : IsMarkov K) (hstat : bind π K = π)
    (hρ : 0 ≤ ρ) (hL2 : CenteredL2Contraction π K ρ) :
    inner π g (act K g) ≤ ρ * energy π g + (1-ρ) * (mean π g)^2 := by
  let h : X → ℝ := fun x => g x - mean π g
  have he := energy_nonneg π h hπ
  have hc := inner_cs π h (act K h) hπ
  have hl := hL2 h (centered_mean_zero π g hπ)
  have hm := mul_le_mul_of_nonneg_left hl he
  have hb : inner π h (act K h) ≤ ρ * energy π h := by
    have hc' : (inner π h (act K h))^2 ≤ (ρ * energy π h)^2 := by
      nlinarith only [hc, hm]
    have hn := mul_nonneg hρ he
    nlinarith only [hc', hn, sq_nonneg (inner π h (act K h) - ρ * energy π h)]
  dsimp [h] at hb
  rw [inner_centered_act π g K hπ hK hstat, energy_centered π g hπ] at hb
  nlinarith

lemma act_reversible_inner (π u v : X → ℝ) (K : X → X → ℝ)
    (hrev : IsReversible π K) : inner π u (act K v) = inner π v (act K u) := by
  simp only [inner, act, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  calc
    π z * u z * (K z x * v x) = (π z * K z x) * v x * u z := by ring
    _ = (π x * K x z) * v x * u z := by rw [hrev z x]
    _ = π x * v x * (K x z * u z) := by ring

/-- The symmetric killed operator. No division by failure probabilities occurs. -/
def killed (K : X → X → ℝ) (f u : X → ℝ) : X → ℝ :=
  fun x => Real.sqrt (f x) * act K (fun z => Real.sqrt (f z) * u z) x

lemma killed_inner (π u v f : X → ℝ) (K : X → X → ℝ) :
    inner π u (killed K f v) =
      inner π (fun x => Real.sqrt (f x) * u x) (act K (fun x => Real.sqrt (f x) * v x)) := by
  apply Finset.sum_congr rfl
  intro x _
  dsimp [killed]
  ring

lemma killed_symmetric (π u v f : X → ℝ) (K : X → X → ℝ)
    (hrev : IsReversible π K) : inner π u (killed K f v) = inner π v (killed K f u) := by
  rw [killed_inner, killed_inner, act_reversible_inner π _ _ K hrev]

lemma sqrt_energy (π u f : X → ℝ) (hf : ∀ x, 0 ≤ f x) :
    energy π (fun x => Real.sqrt (f x) * u x) = ∑ x, π x * f x * (u x)^2 := by
  simp only [energy, mul_pow, Real.sq_sqrt (hf _)]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The killing quadratic is bounded by lambda = rho + (1-rho) pi(f). -/
theorem killed_quadratic_bound (π u f : X → ℝ) (K : X → X → ℝ) (ρ : ℝ)
    (hπ : IsProbability π) (hK : IsMarkov K) (hrev : IsReversible π K)
    (hρ : 0 ≤ ρ) (hρone : ρ ≤ 1)
    (hL2 : CenteredL2Contraction π K ρ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    inner π u (killed K f u) ≤ (ρ + (1-ρ)*mean π f) * energy π u := by
  rw [killed_inner]
  have hq := quadratic_comparison π (fun x => Real.sqrt (f x) * u x) K ρ hπ hK
    (reversible_stationary π K hK hrev) hρ hL2
  have he : energy π (fun x => Real.sqrt (f x) * u x) ≤ energy π u := by
    rw [sqrt_energy π u f (fun x => (hf x).1)]
    apply Finset.sum_le_sum
    intro x _
    have := mul_le_mul_of_nonneg_left (hf x).2 (mul_nonneg (hπ.nonneg x) (sq_nonneg (u x)))
    nlinarith
  have hc := inner_cs π (fun x => Real.sqrt (f x)) u hπ
  have hs : energy π (fun x => Real.sqrt (f x)) = mean π f := by
    simp only [energy, mean, Real.sq_sqrt (hf _).1]
  have hm : mean π (fun x => Real.sqrt (f x) * u x) = inner π (fun x => Real.sqrt (f x)) u := by
    apply Finset.sum_congr rfl
    intro x _
    ring
  rw [hs, ← hm] at hc
  have h1 := mul_le_mul_of_nonneg_left he hρ
  have h2 := mul_le_mul_of_nonneg_left hc (sub_nonneg.mpr hρone)
  nlinarith

lemma inner_add_right (π u v w : X → ℝ) :
    inner π u (fun x => v x + w x) = inner π u v + inner π u w := by
  simp [inner, mul_add, Finset.sum_add_distrib]

lemma inner_scale_right (π u v : X → ℝ) (c : ℝ) :
    inner π u (fun x => c * v x) = c * inner π u v := by
  simp only [inner, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma inner_add_left (π u v w : X → ℝ) :
    inner π (fun x => u x + v x) w = inner π u w + inner π v w := by
  simp [inner, add_mul, mul_add, Finset.sum_add_distrib]

lemma inner_scale_left (π u v : X → ℝ) (c : ℝ) :
    inner π (fun x => c * u x) v = c * inner π u v := by
  rw [inner_comm, inner_scale_right, inner_comm π v u]

lemma killed_add_scale (K : X → X → ℝ) (f u v : X → ℝ) (c : ℝ) :
    killed K f (fun x => u x + c * v x) =
      fun x => killed K f u x + c * killed K f v x := by
  funext x
  simp only [killed, act, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro z _
  ring

lemma killed_psd_cs (π u v f : X → ℝ) (K : X → X → ℝ)
    (hrev : IsReversible π K) (hPSD : IsPSD π K) :
    (inner π u (killed K f v))^2 ≤
      inner π u (killed K f u) * inner π v (killed K f v) := by
  have hp : ∀ c : ℝ, 0 ≤ inner π (fun x => v x + c * u x)
      (killed K f (fun x => v x + c * u x)) := by
    intro c
    rw [killed_inner]
    exact hPSD _
  have hd := discrim_le_zero (a := inner π u (killed K f u))
    (b := 2 * inner π u (killed K f v)) (c := inner π v (killed K f v)) (by
      intro c
      have h := hp c
      rw [killed_add_scale, inner_add_right, inner_scale_right,
        inner_add_left, inner_scale_left, inner_add_left, inner_scale_left,
        killed_symmetric π v u f K hrev] at h
      nlinarith only [h])
  dsimp [discrim] at hd
  nlinarith only [hd]

/-- PSD and the proved quadratic comparison imply a full energy contraction. -/
theorem killed_energy_bound (π u f : X → ℝ) (K : X → X → ℝ) (ρ : ℝ)
    (hπ : IsProbability π) (hK : IsMarkov K) (hrev : IsReversible π K)
    (hPSD : IsPSD π K) (hρ : 0 ≤ ρ) (hρone : ρ ≤ 1)
    (hL2 : CenteredL2Contraction π K ρ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    energy π (killed K f u) ≤ (ρ + (1-ρ)*mean π f)^2 * energy π u := by
  let lam := ρ + (1-ρ)*mean π f
  have hlam : 0 ≤ lam := by
    apply add_nonneg hρ
    exact mul_nonneg (sub_nonneg.mpr hρone)
      (Finset.sum_nonneg (fun x _ => mul_nonneg (hπ.nonneg x) (hf x).1))
  have hcs := killed_psd_cs π u (killed K f u) f K hrev hPSD
  have heq : inner π u (killed K f (killed K f u)) = energy π (killed K f u) := by
    rw [killed_symmetric π u (killed K f u) f K hrev, inner_self]
  rw [heq] at hcs
  have hu := killed_quadratic_bound π u f K ρ hπ hK hrev hρ hρone hL2 hf
  have hv := killed_quadratic_bound π (killed K f u) f K ρ hπ hK hrev hρ hρone hL2 hf
  have hn : 0 ≤ inner π (killed K f u) (killed K f (killed K f u)) := by
    rw [killed_inner]
    exact hPSD _
  have heu := energy_nonneg π u hπ
  have hev := energy_nonneg π (killed K f u) hπ
  have hm := mul_le_mul hu hv hn (mul_nonneg hlam heu)
  change _ ≤ lam^2 * energy π u
  change _ ≤ lam * energy π u at hu
  change _ ≤ lam * energy π (killed K f u) at hv
  have hs : (energy π (killed K f u))^2 ≤
      (lam^2 * energy π u) * energy π (killed K f u) := by
    nlinarith only [hcs, hm]
  by_cases hz : energy π (killed K f u) = 0
  · rw [hz]
    exact mul_nonneg (sq_nonneg lam) heu
  · have hpos : 0 < energy π (killed K f u) := lt_of_le_of_ne hev (Ne.symm hz)
    nlinarith only [hs, hpos]

def killedIter (K : X → X → ℝ) (f u : X → ℝ) : ℕ → X → ℝ
  | 0 => u
  | n+1 => killed K f (killedIter K f u n)

lemma killed_iter_energy (π u f : X → ℝ) (K : X → X → ℝ) (lam : ℝ)
    (_hπ : IsProbability π) (_hlam : 0 ≤ lam)
    (hbound : ∀ v, energy π (killed K f v) ≤ lam^2 * energy π v) (n : ℕ) :
    energy π (killedIter K f u n) ≤ (lam^n)^2 * energy π u := by
  induction n with
  | zero => simp [killedIter]
  | succ n ih =>
    calc
      energy π (killedIter K f u (n+1)) ≤ lam^2 * energy π (killedIter K f u n) := hbound _
      _ ≤ lam^2 * ((lam^n)^2 * energy π u) := mul_le_mul_of_nonneg_left ih (sq_nonneg lam)
      _ = (lam^(n+1))^2 * energy π u := by rw [pow_succ]; ring

lemma killed_iter_inner_bound (π u f : X → ℝ) (K : X → X → ℝ) (lam : ℝ)
    (hπ : IsProbability π) (hlam : 0 ≤ lam)
    (hbound : ∀ v, energy π (killed K f v) ≤ lam^2 * energy π v) (n : ℕ) :
    inner π u (killedIter K f u n) ≤ lam^n * energy π u := by
  have he := killed_iter_energy π u f K lam hπ hlam hbound n
  have hc := inner_cs π u (killedIter K f u n) hπ
  have heu := energy_nonneg π u hπ
  have hm := mul_le_mul_of_nonneg_left he heu
  have hs : (inner π u (killedIter K f u n))^2 ≤ (lam^n * energy π u)^2 := by
    nlinarith only [hc, hm]
  have hn := mul_nonneg (pow_nonneg hlam n) heu
  nlinarith only [hs, hn, sq_nonneg (inner π u (killedIter K f u n) - lam^n * energy π u)]

/-- Unnormalized state mass after n+1 failures and n intervening blocks. -/
def killedSurvivor (π : X → ℝ) (K : X → X → ℝ) (f : X → ℝ) : ℕ → X → ℝ
  | 0 => fun x => π x * f x
  | n+1 => fun x => bind (killedSurvivor π K f n) K x * f x

/-- Exact sandwich representation; it remains valid where failure is zero. -/
lemma killed_survivor_density (π f : X → ℝ) (K : X → X → ℝ)
    (hrev : IsReversible π K) (hf : ∀ x, 0 ≤ f x) (n : ℕ) :
    killedSurvivor π K f n = fun x => π x * Real.sqrt (f x) *
      killedIter K f (fun z => Real.sqrt (f z)) n x := by
  induction n with
  | zero =>
    funext x
    simp only [killedSurvivor, killedIter]
    calc
      π x * f x = π x * (Real.sqrt (f x))^2 := by rw [Real.sq_sqrt (hf x)]
      _ = _ := by ring
  | succ n ih =>
    funext x
    simp only [killedSurvivor, ih, killedIter, killed, bind, act, Finset.sum_mul,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    calc
      π z * Real.sqrt (f z) * killedIter K f (fun z => Real.sqrt (f z)) n z * K z x * f x =
        (π z * K z x) * (Real.sqrt (f z) * killedIter K f (fun z => Real.sqrt (f z)) n z) * f x := by ring
      _ = (π x * K x z) * (Real.sqrt (f z) * killedIter K f (fun z => Real.sqrt (f z)) n z) * f x := by
        rw [hrev z x]
      _ = π x * Real.sqrt (f x) * (Real.sqrt (f x) *
        (K x z * (Real.sqrt (f z) * killedIter K f (fun z => Real.sqrt (f z)) n z))) := by
        calc
          _ = (π x * K x z) * (Real.sqrt (f z) * killedIter K f (fun z => Real.sqrt (f z)) n z) * (Real.sqrt (f x))^2 := by
            rw [Real.sq_sqrt (hf x)]
          _ = _ := by ring

lemma killed_survivor_mass (π f : X → ℝ) (K : X → X → ℝ)
    (hrev : IsReversible π K) (hf : ∀ x, 0 ≤ f x) (n : ℕ) :
    mass (killedSurvivor π K f n) =
      inner π (fun x => Real.sqrt (f x)) (killedIter K f (fun x => Real.sqrt (f x)) n) := by
  rw [killed_survivor_density π f K hrev hf n]
  rfl

/-- Actual finite killed-chain exhaustion. The assumptions are on the original
finite kernel, not an assumed power bound or exhaustion estimate. The index n
represents n+1 marks, with n intervening Markov blocks. -/
theorem killed_survivor_mass_bound (π f : X → ℝ) (K : X → X → ℝ) (ρ : ℝ)
    (hπ : IsProbability π) (hK : IsMarkov K) (hrev : IsReversible π K)
    (hPSD : IsPSD π K) (hρ : 0 ≤ ρ) (hρone : ρ ≤ 1)
    (hL2 : CenteredL2Contraction π K ρ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (n : ℕ) :
    mass (killedSurvivor π K f n) ≤
      mean π f * (ρ + (1-ρ)*mean π f)^n := by
  have hlam : 0 ≤ ρ + (1-ρ)*mean π f := by
    apply add_nonneg hρ
    exact mul_nonneg (sub_nonneg.mpr hρone)
      (Finset.sum_nonneg (fun x _ => mul_nonneg (hπ.nonneg x) (hf x).1))
  rw [killed_survivor_mass π f K hrev (fun x => (hf x).1) n]
  have hb := killed_iter_inner_bound π (fun x => Real.sqrt (f x)) f K
    (ρ + (1-ρ)*mean π f) hπ hlam
    (fun u => killed_energy_bound π u f K ρ hπ hK hrev hPSD hρ hρone hL2 hf) n
  have hs : energy π (fun x => Real.sqrt (f x)) = mean π f := by
    simp only [energy, mean, Real.sq_sqrt (hf _).1]
  rw [hs, mul_comm] at hb
  exact hb

/-- The terminal-subkernel form of the sharp finite exhaustion bound.
It includes zero or certain acceptance and does not need positive pi. -/
theorem terminal_exhaustion_bound (π : X → ℝ) (K : X → X → ℝ)
    (A : X → Y → ℝ) (ν : Y → ℝ) (s ρ : ℝ)
    (hπ : IsProbability π) (hν : IsProbability ν) (hK : IsMarkov K)
    (hA : IsTerminal A) (hrev : IsReversible π K) (hPSD : IsPSD π K)
    (hsuccess : bind π A = fun y => s * ν y) (hρ : 0 ≤ ρ) (hρone : ρ ≤ 1)
    (hL2 : CenteredL2Contraction π K ρ) (n : ℕ) :
    mass (killedSurvivor π K (failure A) n) ≤
      (1-s) * (1-(1-ρ)*s)^n := by
  have hb := killed_survivor_mass_bound π (failure A) K ρ hπ hK hrev hPSD hρ hρone hL2
    (fun x => ⟨failure_nonneg A hA x, failure_le_one A hA x⟩) n
  have hm : mean π (failure A) = 1-s :=
    stationary_failure_mass π A ν s hπ hν hsuccess
  rw [hm] at hb
  have he : ρ + (1-ρ)*(1-s) = 1-(1-ρ)*s := by ring
  rwa [he] at hb

lemma killed_survivor_zero (π : X → ℝ) (K : X → X → ℝ) (A : X → Y → ℝ) :
    killedSurvivor π K (failure A) 0 = survive π A := rfl

lemma killed_survivor_succ (π : X → ℝ) (K : X → X → ℝ) (A : X → Y → ℝ) (n : ℕ) :
    killedSurvivor π K (failure A) (n+1) =
      survive (bind (killedSurvivor π K (failure A) n) K) A := rfl

lemma killed_survivor_nonneg (π : X → ℝ) (K : X → X → ℝ) (f : X → ℝ)
    (hπ : IsProbability π) (hK : IsMarkov K) (hf : ∀ x, 0 ≤ f x) (n : ℕ) :
    ∀ x, 0 ≤ killedSurvivor π K f n x := by
  induction n with
  | zero => intro x; exact mul_nonneg (hπ.nonneg x) (hf x)
  | succ n ih =>
    intro x
    exact mul_nonneg (Finset.sum_nonneg (fun z _ => mul_nonneg (ih z) (hK.nonneg z x))) (hf x)

/-- R positive marks, in the indexing used by the sampler documentation. -/
theorem terminal_exhaustion_bound_positive_marks (π : X → ℝ) (K : X → X → ℝ)
    (A : X → Y → ℝ) (ν : Y → ℝ) (s ρ : ℝ)
    (hπ : IsProbability π) (hν : IsProbability ν) (hK : IsMarkov K)
    (hA : IsTerminal A) (hrev : IsReversible π K) (hPSD : IsPSD π K)
    (hsuccess : bind π A = fun y => s * ν y) (hρ : 0 ≤ ρ) (hρone : ρ ≤ 1)
    (hL2 : CenteredL2Contraction π K ρ) (R : ℕ) (_hR : 0 < R) :
    mass (killedSurvivor π K (failure A) (R-1)) ≤
      (1-s) * (1-(1-ρ)*s)^(R-1) :=
  terminal_exhaustion_bound π K A ν s ρ hπ hν hK hA hrev hPSD hsuccess hρ hρone hL2 (R-1)

end
end Marked.Survivor
