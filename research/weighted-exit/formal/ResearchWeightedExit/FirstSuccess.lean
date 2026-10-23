/-
SPDX-License-Identifier: Apache-2.0
Bounded first-success laws for a weighted target, including a fixed-word
realization. The physical one-trial mass and approximation bound are explicit
premises; no physical exit or rational trace clock is implemented here.
-/
import Math115.CompletionBooleanRetry

set_option maxHeartbeats 800000

namespace Math115.WeightedExit

open OAI.ContingencyTables FirstSuccess ResidualMixture
open Math115.CompletionRetryBudget Math115.CompletionBooleanRetry
open scoped BigOperators Classical

noncomputable section
variable {X D : Type*} [Fintype X] [Fintype D] [DecidableEq D]

lemma failure_of_weighted_success (q : RationalLaw X) (trial : X → Option D)
    (target : RationalLaw D) (a : ℚ)
    (hs : ∀ d, successMass q trial d = a * target.mass d) :
    failureMass q trial = 1 - a := by
  have ht := success_failure_total q trial
  simp_rw [hs] at ht
  rw [← Finset.mul_sum, target.total, mul_one] at ht
  linarith

lemma weighted_output_mass (target : RationalLaw D) (a : ℚ)
    (J : ℕ) (fallback d : D) :
    outputMass (fun e => a * target.mass e) (1 - a) J fallback d =
      (1 - (1 - a)^J) * target.mass d +
        if d = fallback then (1 - a)^J else 0 := by
  have hg := geometric_balance (1 - a) J
  have hg' : a * (∑ j ∈ Finset.range J, (1 - a)^j) = 1 - (1 - a)^J := by
    nlinarith [hg]
  dsimp [outputMass]
  rw [mul_assoc, mul_comm (target.mass d), ← mul_assoc, hg']

/-- The bounded ideal retry is the weighted target mixed with fallback.
The supplied success-mass identity determines its actual failure probability. -/
theorem weighted_retry_mass (q : RationalLaw X) (trial : X → Option D)
    (target : RationalLaw D) (a : ℚ)
    (hs : ∀ d, successMass q trial d = a * target.mass d)
    (fallback d : D) (J : ℕ) :
    (retryLaw q trial fallback J).mass d =
      (1 - (1 - a)^J) * target.mass d +
        if d = fallback then (1 - a)^J else 0 := by
  have he : successMass q trial = fun e => a * target.mass e := funext hs
  rw [retryLaw_mass, he, failure_of_weighted_success q trial target a hs]
  exact weighted_output_mass target a J fallback d

theorem weighted_retry_variation (q : RationalLaw X) (trial : X → Option D)
    (target : RationalLaw D) (a : ℚ)
    (hs : ∀ d, successMass q trial d = a * target.mass d)
    (fallback : D) (J : ℕ) :
    variation (retryLaw q trial fallback J) target ≤ (1 - a)^J := by
  letI : Nonempty D := ⟨fallback⟩
  have hf0 : 0 ≤ (1 - a)^J := by
    rw [← failure_of_weighted_success q trial target a hs]
    exact pow_nonneg (failure_nonnegative q trial) J
  have hpoint := point_mass_variation target fallback
  have he (d : D) : |(retryLaw q trial fallback J).mass d - target.mass d| =
      (1 - a)^J * |(if d = fallback then (1 : ℚ) else 0) - target.mass d| := by
    rw [weighted_retry_mass q trial target a hs fallback d J]
    have halg : (1 - (1 - a)^J) * target.mass d +
        (if d = fallback then (1 - a)^J else 0) - target.mass d =
        (1 - a)^J * ((if d = fallback then (1 : ℚ) else 0) - target.mass d) := by
      split_ifs <;> ring
    rw [halg, abs_mul, abs_of_nonneg hf0]
  unfold variation
  simp_rw [he]
  rw [← Finset.mul_sum]
  nlinarith [mul_le_mul_of_nonneg_left hpoint hf0]

/-- Compare whole independent trial banks before taking first success.
The approximation error is not divided by an acceptance probability. -/
theorem approximate_weighted_retry_variation (p q : RationalLaw X)
    (trial : X → Option D) (target : RationalLaw D) (a : ℚ)
    (hs : ∀ d, successMass q trial d = a * target.mass d)
    (fallback : D) (J : ℕ) (δ : ℚ) (happrox : variation p q ≤ δ) :
    variation (retryLaw p trial fallback J) target ≤ (1 - a)^J + (J : ℚ) * δ := by
  have ht := variation_triangle (retryLaw p trial fallback J)
    (retryLaw q trial fallback J) target
  have hr := retryLaw_variation p q trial fallback J
  have hi := weighted_retry_variation q trial target a hs fallback J
  have hm := mul_le_mul_of_nonneg_left happrox (show (0 : ℚ) ≤ J by positivity)
  linarith

/-- Symbolic normalized star conductances; no algorithm evaluates these weights. -/
def starLaw (S : D → ℚ) (hS : ∀ d, 0 ≤ S d) (hpos : 0 < ∑ d, S d) : RationalLaw D where
  mass := fun d => S d / (∑ e, S e)
  nonnegative := fun d => div_nonneg (hS d) hpos.le
  total := by rw [← Finset.sum_div, div_self (ne_of_gt hpos)]

lemma star_success_normalized (q : RationalLaw X) (trial : X → Option D)
    (S : D → ℚ) (hS : ∀ d, 0 ≤ S d) (hpos : 0 < ∑ d, S d)
    (ρ w : ℚ) (hw : 0 < w)
    (hs : ∀ d, successMass q trial d = ρ * S d / w) (d : D) :
    successMass q trial d = (ρ * (∑ e, S e) / w) * (starLaw S hS hpos).mass d := by
  rw [hs]
  dsimp [starLaw]
  field_simp [ne_of_gt hpos, ne_of_gt hw]

/-- Weighted-star specialization. Positive total star mass is explicit;
the physical one-trial successful masses still have to be established. -/
theorem star_retry_mass (q : RationalLaw X) (trial : X → Option D)
    (S : D → ℚ) (hS : ∀ d, 0 ≤ S d) (hpos : 0 < ∑ d, S d)
    (ρ w : ℚ) (hw : 0 < w)
    (hs : ∀ d, successMass q trial d = ρ * S d / w)
    (fallback d : D) (J : ℕ) :
    (retryLaw q trial fallback J).mass d =
      (1 - (1 - ρ * (∑ e, S e) / w)^J) * (S d / ∑ e, S e) +
        if d = fallback then (1 - ρ * (∑ e, S e) / w)^J else 0 :=
  weighted_retry_mass q trial (starLaw S hS hpos) (ρ * (∑ e, S e) / w)
    (star_success_normalized q trial S hS hpos ρ w hw hs) fallback d J

/-- A finite bank of exactly J*k fair bits realizes the bounded retry.
Successful-mass and one-trial accuracy are the only algorithm-specific premises.
The draw/trial functions do not receive or compute the symbolic star weights. -/
theorem flat_star_retry_variation [DecidableEq X] {k : ℕ}
    (draw : (Fin k → Bool) → X) (trial : X → Option D) (q : RationalLaw X)
    (S : D → ℚ) (hS : ∀ d, 0 ≤ S d) (hpos : 0 < ∑ d, S d)
    (ρ w : ℚ) (hw : 0 < w)
    (hs : ∀ d, successMass q trial d = ρ * S d / w)
    (fallback : D) (J : ℕ) (δ : ℚ)
    (happrox : variation (mapLaw (uniformLaw (α := Fin k → Bool)) draw) q ≤ δ) :
    variation
      (mapLaw (uniformLaw (α := Fin (J * k) → Bool))
        (flatRetry (fun word => trial (draw word)) fallback J))
      (starLaw S hS hpos) ≤ (1 - ρ * (∑ e, S e) / w)^J + (J : ℚ) * δ := by
  rw [flatRetry_law draw trial fallback J]
  exact approximate_weighted_retry_variation _ q trial (starLaw S hS hpos)
    (ρ * (∑ e, S e) / w) (star_success_normalized q trial S hS hpos ρ w hw hs)
    fallback J δ happrox

end
end Math115.WeightedExit
