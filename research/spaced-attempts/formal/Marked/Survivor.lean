import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-! Finite dependent attempts with rejection retaining the state.

This module assumes a certified TV bound for mixing each dominated survivor.
It does not obtain that premise from a spectral gap or an L2 estimate.
-/
namespace Marked.Survivor
open scoped BigOperators Classical
noncomputable section

variable {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

def mass (μ : X → ℝ) : ℝ := ∑ x, μ x
def bind (μ : X → ℝ) (K : X → Y → ℝ) : Y → ℝ :=
  fun y => ∑ x, μ x * K x y
def tv (μ ν : X → ℝ) : ℝ := (∑ x, |μ x - ν x|) / 2

structure IsProbability (μ : X → ℝ) : Prop where
  nonneg : ∀ x, 0 ≤ μ x
  total : mass μ = 1

structure IsMarkov (K : X → Y → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ K x y
  total : ∀ x, ∑ y, K x y = 1

structure IsTerminal (A : X → Y → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ A x y
  total_le : ∀ x, ∑ y, A x y ≤ 1

def failure (A : X → Y → ℝ) (x : X) : ℝ := 1 - ∑ y, A x y
def survive (μ : X → ℝ) (A : X → Y → ℝ) : X → ℝ :=
  fun x => μ x * failure A x
def refresh (π : X → ℝ) : X → X → ℝ := fun _ z => π z
def point (y₀ : Y) : Y → ℝ := fun y => if y = y₀ then 1 else 0

/-- The kernel from a retained state to final output. There are at most `R`
marks. `R = 0` means immediate fallback. The transition following the last
failure is algebraically harmless because the zero-mark output is constant. -/
def output (K : X → X → ℝ) (A : X → Y → ℝ) (y₀ : Y) : ℕ → X → Y → ℝ
  | 0 => fun _ => point y₀
  | R + 1 => fun x y => A x y + failure A x * ∑ z, K x z * output K A y₀ R z y

omit [Fintype X] in
lemma failure_nonneg (A : X → Y → ℝ) (hA : IsTerminal A) (x : X) :
    0 ≤ failure A x := by
  exact sub_nonneg.mpr (hA.total_le x)

omit [Fintype X] in
lemma failure_le_one (A : X → Y → ℝ) (hA : IsTerminal A) (x : X) :
    failure A x ≤ 1 := by
  have h := Finset.sum_nonneg (fun y (_ : y ∈ Finset.univ) => hA.nonneg x y)
  dsimp [failure]
  linarith

omit [Fintype X] in
lemma survive_dominated (π μ : X → ℝ) (A : X → Y → ℝ)
    (hμ : ∀ x, 0 ≤ μ x ∧ μ x ≤ π x)
    (hA : IsTerminal A) :
    ∀ x, 0 ≤ survive μ A x ∧ survive μ A x ≤ π x := by
  intro x
  exact ⟨mul_nonneg (hμ x).1 (failure_nonneg A hA x),
    (mul_le_of_le_one_right (hμ x).1 (failure_le_one A hA x)).trans (hμ x).2⟩

lemma bind_dominated (π μ : X → ℝ) (K : X → X → ℝ)
    (hμ : ∀ x, 0 ≤ μ x ∧ μ x ≤ π x) (hK : IsMarkov K)
    (hstationary : bind π K = π) :
    ∀ z, 0 ≤ bind μ K z ∧ bind μ K z ≤ π z := by
  intro z
  constructor
  · exact Finset.sum_nonneg (fun x _ => mul_nonneg (hμ x).1 (hK.nonneg x z))
  · calc
      bind μ K z ≤ bind π K z :=
        Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_right (hμ x).2 (hK.nonneg x z))
      _ = π z := congrFun hstationary z

lemma mass_bind (μ : X → ℝ) (K : X → Y → ℝ) (hK : IsMarkov K) :
    mass (bind μ K) = mass μ := by
  simp only [mass, bind]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hK.total, mul_one]

lemma bind_probability (μ : X → ℝ) (K : X → Y → ℝ)
    (hμ : IsProbability μ) (hK : IsMarkov K) : IsProbability (bind μ K) := by
  constructor
  · intro y
    exact Finset.sum_nonneg (fun x _ => mul_nonneg (hμ.nonneg x) (hK.nonneg x y))
  · rw [mass_bind μ K hK, hμ.total]

lemma bind_refresh (μ π : X → ℝ) :
    bind μ (refresh π) = fun x => mass μ * π x := by
  funext x
  simp [bind, refresh, mass, Finset.sum_mul]

lemma refresh_markov (π : X → ℝ) (hπ : IsProbability π) :
    IsMarkov (refresh π) := ⟨fun _ x => hπ.nonneg x, fun _ => hπ.total⟩

lemma output_markov (K : X → X → ℝ) (A : X → Y → ℝ) (y₀ : Y)
    (hK : IsMarkov K) (hA : IsTerminal A) (R : ℕ) :
    IsMarkov (output K A y₀ R) := by
  induction R with
  | zero =>
      constructor
      · intro x y
        dsimp [output, point]
        split_ifs <;> norm_num
      · intro x
        simp [output, point]
  | succ R ih =>
      constructor
      · intro x y
        exact add_nonneg (hA.nonneg x y) (mul_nonneg (failure_nonneg A hA x)
          (Finset.sum_nonneg (fun z _ => mul_nonneg (hK.nonneg x z) (ih.nonneg z y))))
      · intro x
        simp only [output, Finset.sum_add_distrib, ← Finset.mul_sum]
        rw [Finset.sum_comm]
        simp_rw [← Finset.mul_sum, ih.total, mul_one]
        rw [hK.total]
        simp [failure]

lemma tv_nonneg (μ ν : X → ℝ) : 0 ≤ tv μ ν := by
  exact div_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (by norm_num)

lemma tv_triangle (μ ν ξ : X → ℝ) : tv μ ξ ≤ tv μ ν + tv ν ξ := by
  have h : (∑ x, |μ x - ξ x|) ≤ (∑ x, |μ x - ν x|) + ∑ x, |ν x - ξ x| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    have he : μ x - ξ x = (μ x - ν x) + (ν x - ξ x) := by ring
    rw [he]
    exact abs_add_le _ _
  unfold tv
  linarith

lemma tv_common_add (μ ν c : X → ℝ) :
    tv (fun x => c x + μ x) (fun x => c x + ν x) = tv μ ν := by
  unfold tv
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  ring

lemma tv_bind_contract (μ ν : X → ℝ) (K : X → Y → ℝ) (hK : IsMarkov K) :
    tv (bind μ K) (bind ν K) ≤ tv μ ν := by
  have hpoint : ∀ y, |bind μ K y - bind ν K y| ≤ ∑ x, |μ x - ν x| * K x y := by
    intro y
    calc
      |bind μ K y - bind ν K y| = |∑ x, (μ x - ν x) * K x y| := by
        congr 1
        simp [bind, sub_mul, Finset.sum_sub_distrib]
      _ ≤ ∑ x, |(μ x - ν x) * K x y| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ x, |μ x - ν x| * K x y := by
        simp_rw [abs_mul, abs_of_nonneg (hK.nonneg _ _)]
  have h := Finset.sum_le_sum (fun y (_ : y ∈ Finset.univ) => hpoint y)
  rw [Finset.sum_comm] at h
  simp_rw [← Finset.mul_sum, hK.total, mul_one] at h
  unfold tv
  linarith

lemma bind_output_succ (μ : X → ℝ) (K : X → X → ℝ)
    (A : X → Y → ℝ) (y₀ : Y) (R : ℕ) :
    bind μ (output K A y₀ (R + 1)) = fun y =>
      bind μ A y + bind (bind (survive μ A) K) (output K A y₀ R) y := by
  funext y
  simp only [bind, output, survive, mul_add, Finset.sum_add_distrib]
  congr 1
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro z _
  ring

omit [Fintype Y] in
lemma bind_scale (μ : X → ℝ) (K : X → Y → ℝ) (c : ℝ) :
    bind (fun x => c * μ x) K = fun y => c * bind μ K y := by
  funext y
  simp only [bind, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma bind_output_zero (μ : X → ℝ) (K : X → X → ℝ)
    (A : X → Y → ℝ) (y₀ : Y) :
    bind μ (output K A y₀ 0) = fun y => mass μ * point y₀ y := by
  funext y
  simp [bind, output, mass, Finset.sum_mul]

lemma output_one (K : X → X → ℝ) (A : X → Y → ℝ) (y₀ : Y)
    (hK : IsMarkov K) :
    output K A y₀ 1 = fun x y => A x y + failure A x * point y₀ y := by
  funext x y
  simp only [output, ← Finset.sum_mul, hK.total, one_mul]

/-- Every actual-prefix survivor is dominated by the stationary probability.
The block estimate applies to the unnormalized survivor, including mass zero;
its comparison measure is its own mass times `π`. -/
def SurvivorMixing (π : X → ℝ) (K : X → X → ℝ) (ε : ℝ) : Prop :=
  ∀ μ : X → ℝ, (∀ x, 0 ≤ μ x ∧ μ x ≤ π x) →
    tv (bind μ K) (fun x => mass μ * π x) ≤ ε

/-- Finite dependent-attempt hybrid estimate. Only `R` inter-mark blocks are
charged for `R+1` marks; the common first mark contributes no discrepancy. -/
theorem hybrid_bound (π : X → ℝ) (K : X → X → ℝ)
    (A : X → Y → ℝ) (y₀ : Y) (ε : ℝ)
    (hπ : IsProbability π) (hK : IsMarkov K) (hA : IsTerminal A)
    (hstationary : bind π K = π) (hmix : SurvivorMixing π K ε)
    (R : ℕ) : ∀ μ : X → ℝ, (∀ x, 0 ≤ μ x ∧ μ x ≤ π x) →
    tv (bind μ (output K A y₀ (R + 1)))
      (bind μ (output (refresh π) A y₀ (R + 1))) ≤ (R : ℝ) * ε := by
  induction R with
  | zero =>
      intro μ hμ
      rw [output_one K A y₀ hK, output_one (refresh π) A y₀ (refresh_markov π hπ)]
      simp [tv]
  | succ R ih =>
      intro μ hμ
      let v := survive μ A
      have hv : ∀ x, 0 ≤ v x ∧ v x ≤ π x := survive_dominated π μ A hμ hA
      have hw : ∀ x, 0 ≤ bind v K x ∧ bind v K x ≤ π x :=
        bind_dominated π v K hv hK hstationary
      rw [bind_output_succ μ K A y₀ (R + 1),
        bind_output_succ μ (refresh π) A y₀ (R + 1), tv_common_add]
      have hb := ih (bind v K) hw
      have hm := hmix v hv
      rw [← bind_refresh v π] at hm
      have hc := tv_bind_contract (bind v K) (bind v (refresh π))
        (output (refresh π) A y₀ (R + 1))
        (output_markov (refresh π) A y₀ (refresh_markov π hπ) hA (R + 1))
      have ht := tv_triangle
        (bind (bind v K) (output K A y₀ (R + 1)))
        (bind (bind v K) (output (refresh π) A y₀ (R + 1)))
        (bind (bind v (refresh π)) (output (refresh π) A y₀ (R + 1)))
      change tv (bind (bind v K) (output K A y₀ (R + 1)))
        (bind (bind v (refresh π)) (output (refresh π) A y₀ (R + 1))) ≤ _
      push_cast
      linarith

lemma mass_survive (μ : X → ℝ) (A : X → Y → ℝ) :
    mass (survive μ A) = mass μ - mass (bind μ A) := by
  simp only [mass, survive, failure, mul_sub, mul_one, Finset.sum_sub_distrib, bind]
  congr 1
  rw [Finset.sum_comm]
  simp_rw [Finset.mul_sum]

lemma stationary_failure_mass (π : X → ℝ) (A : X → Y → ℝ)
    (ν : Y → ℝ) (s : ℝ) (hπ : IsProbability π) (hν : IsProbability ν)
    (hsuccess : bind π A = fun y => s * ν y) :
    mass (survive π A) = 1 - s := by
  rw [mass_survive, hπ.total, hsuccess]
  simp only [mass, ← Finset.mul_sum]
  rw [show (∑ y, ν y) = 1 from hν.total]
  ring

/-- Complete refresh after each failure gives the exact independent-reference
mixture. This is a fact about the reference kernel, not the actual chain. -/
theorem refresh_output_law (π : X → ℝ) (A : X → Y → ℝ)
    (ν : Y → ℝ) (y₀ : Y) (s : ℝ) (hπ : IsProbability π) (hν : IsProbability ν)
    (hsuccess : bind π A = fun y => s * ν y) (R : ℕ) :
    bind π (output (refresh π) A y₀ R) =
      fun y => (1 - (1 - s) ^ R) * ν y + (1 - s) ^ R * point y₀ y := by
  induction R with
  | zero =>
      rw [bind_output_zero, hπ.total]
      funext y
      simp
  | succ R ih =>
      rw [bind_output_succ, hsuccess, bind_refresh,
        stationary_failure_mass π A ν s hπ hν hsuccess, bind_scale, ih]
      funext y
      simp only [pow_succ]
      ring

lemma tv_probability_le_one (μ ν : X → ℝ) (hμ : IsProbability μ)
    (hν : IsProbability ν) : tv μ ν ≤ 1 := by
  have hp : ∀ x, |μ x - ν x| ≤ μ x + ν x := by
    intro x
    calc
      |μ x - ν x| ≤ |μ x| + |ν x| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (μ x) (-ν x)
      _ = μ x + ν x := by rw [abs_of_nonneg (hμ.nonneg x), abs_of_nonneg (hν.nonneg x)]
  have h := Finset.sum_le_sum (fun x (_ : x ∈ Finset.univ) => hp x)
  rw [Finset.sum_add_distrib, show (∑ x, μ x) = 1 from hμ.total,
    show (∑ x, ν x) = 1 from hν.total] at h
  unfold tv
  linarith

lemma point_probability (y₀ : Y) : IsProbability (point y₀) := by
  constructor
  · intro y
    dsimp [point]
    split_ifs <;> norm_num
  · simp [mass, point]

lemma mixture_error (ν : Y → ℝ) (y₀ : Y) (c : ℝ) (hc : 0 ≤ c)
    (hν : IsProbability ν) :
    tv (fun y => (1-c) * ν y + c * point y₀ y) ν ≤ c := by
  have ht : tv (fun y => (1-c) * ν y + c * point y₀ y) ν =
      c * tv (point y₀) ν := by
    unfold tv
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, Finset.mul_sum]
    apply congrArg (fun t : ℝ => t * (2 : ℝ)⁻¹)
    apply Finset.sum_congr rfl
    intro y _
    have he : (1-c) * ν y + c * point y₀ y - ν y = c * (point y₀ y - ν y) := by ring
    rw [he, abs_mul, abs_of_nonneg hc]
  rw [ht]
  exact (mul_le_mul_of_nonneg_left
    (tv_probability_le_one (point y₀) ν (point_probability y₀) hν) hc).trans_eq (mul_one c)

/-- The initial endpoint error is charged once through the whole output
kernel. Actual attempts are dependent; `ε` is a survivor block-TV allowance.
No reversibility, gap estimate, or sampler refinement is hidden in this bound. -/
theorem burn_once_bound (α π : X → ℝ) (K : X → X → ℝ)
    (A : X → Y → ℝ) (ν : Y → ℝ) (y₀ : Y) (s ε : ℝ)
    (hπ : IsProbability π) (hν : IsProbability ν)
    (hK : IsMarkov K) (hA : IsTerminal A)
    (hstationary : bind π K = π) (hsuccess : bind π A = fun y => s * ν y)
    (hs : s ≤ 1) (hmix : SurvivorMixing π K ε) (R : ℕ) :
    tv (bind α (output K A y₀ (R + 1))) ν ≤
      tv α π + (1-s) ^ (R + 1) + (R : ℝ) * ε := by
  have hinitial := tv_bind_contract α π (output K A y₀ (R + 1))
    (output_markov K A y₀ hK hA (R + 1))
  have hhybrid := hybrid_bound π K A y₀ ε hπ hK hA hstationary hmix R π
    (fun x => ⟨hπ.nonneg x, le_rfl⟩)
  have href := mixture_error ν y₀ ((1-s) ^ (R + 1))
    (pow_nonneg (sub_nonneg.mpr hs) _) hν
  rw [← refresh_output_law π A ν y₀ s hπ hν hsuccess] at href
  have ht₁ := tv_triangle
    (bind α (output K A y₀ (R + 1)))
    (bind π (output K A y₀ (R + 1))) ν
  have ht₂ := tv_triangle
    (bind π (output K A y₀ (R + 1)))
    (bind π (output (refresh π) A y₀ (R + 1))) ν
  linarith

end
end Marked.Survivor
