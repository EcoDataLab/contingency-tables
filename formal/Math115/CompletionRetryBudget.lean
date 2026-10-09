/-
SPDX-License-Identifier: Apache-2.0
Generic bounded rejection with equal accepted masses and a concrete dyadic
error budget. Acceptance/count geometry and finite-bit realization are inputs,
not conclusions of this module. The retryLaw uses fresh independent trials.
-/
import OAI.Combinatorics.ContingencyTables.Transport.RejectionLaw
import Mathlib.Data.Nat.Log

namespace Math115.CompletionRetryBudget

open OAI.ContingencyTables FirstSuccess ResidualMixture
open scoped BigOperators Classical

noncomputable section
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- Uniform source mass of one successful decoder fibre, without a bijection
assumption. Equal fibre cardinalities can therefore discharge equal masses. -/
theorem uniform_success_mass [Nonempty S] (trial : S → Option A) (a : A) :
    successMass (uniformLaw (α := S)) trial a =
      (Fintype.card {x : S // trial x = some a} : ℚ) / (Fintype.card S : ℚ) := by
  unfold successMass
  simp only [uniformLaw]
  rw [← Finset.sum_filter, Finset.sum_const, ← Fintype.card_subtype]
  simp only [nsmul_eq_mul, uniformMass, mul_one_div]

theorem uniform_success_mass_of_card [Nonempty S]
    (trial : S → Option A) (m : ℕ)
    (hcard : ∀ a, Fintype.card {x : S // trial x = some a} = m) (a : A) :
    successMass (uniformLaw (α := S)) trial a = (m : ℚ) / (Fintype.card S : ℚ) := by
  rw [uniform_success_mass, hcard]

lemma failure_nonnegative (q : RationalLaw S) (trial : S → Option A) :
    0 ≤ failureMass q trial := by
  unfold failureMass
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact q.nonnegative x
  · rfl

lemma success_nonnegative (q : RationalLaw S) (trial : S → Option A) (a : A) :
    0 ≤ successMass q trial a := by
  unfold successMass
  apply Finset.sum_nonneg
  intro x _
  split_ifs
  · exact q.nonnegative x
  · rfl

lemma failure_le_one (q : RationalLaw S) (trial : S → Option A) :
    failureMass q trial ≤ 1 := by
  have hs : 0 ≤ ∑ a, successMass q trial a :=
    Finset.sum_nonneg fun a _ => success_nonnegative q trial a
  have ht := success_failure_total q trial
  linarith

/-- Equal unconditioned accepted masses identify the success component.
The constant may later be established by an exact finite-fibre bijection. -/
theorem equal_success_normalized (q : RationalLaw S) (trial : S → Option A)
    (w : ℚ) (hequal : ∀ a, successMass q trial a = w) (a : A) :
    successMass q trial a = (1 - failureMass q trial) * uniformMass (α := A) := by
  have ht := success_failure_total q trial
  simp only [hequal, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ht
  have hcard : (Fintype.card A : ℚ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := A)).ne'
  rw [hequal]
  unfold uniformMass
  rw [mul_one_div]
  apply (eq_div_iff hcard).mpr
  linarith

/-- The ideal bounded retry law is a normalized uniform/fallback mixture. -/
theorem equal_success_retry_mass (q : RationalLaw S) (trial : S → Option A)
    (w : ℚ) (hequal : ∀ a, successMass q trial a = w)
    (fallback a : A) (n : ℕ) :
    (retryLaw q trial fallback n).mass a =
      (1 - (failureMass q trial)^n) * uniformMass (α := A) +
        if a = fallback then (failureMass q trial)^n else 0 := by
  have hg : successMass q trial =
      fun _ => (1 - failureMass q trial) * uniformMass (α := A) := by
    funext x
    exact equal_success_normalized q trial w hequal x
  rw [retryLaw_mass, hg]
  simpa only [sub_sub_cancel] using
    stationary_output_mass (1 - failureMass q trial) n fallback a

/-- Exact equal-mass trials incur only the all-failed probability. -/
theorem equal_success_retry_variation (q : RationalLaw S) (trial : S → Option A)
    (w : ℚ) (hequal : ∀ a, successMass q trial a = w) (fallback : A) (n : ℕ) :
    variation (retryLaw q trial fallback n) (uniformLaw (α := A)) ≤
      (failureMass q trial)^n := by
  have hg : successMass q trial =
      fun _ => (1 - failureMass q trial) * uniformMass (α := A) := by
    funext x
    exact equal_success_normalized q trial w hequal x
  unfold variation
  simp only [retryLaw_mass, hg, uniformLaw]
  simpa only [sub_sub_cancel] using
    stationary_variation (1 - failureMass q trial)
      (sub_nonneg.mpr (failure_le_one q trial))
      (by have h := failure_nonnegative q trial; linarith) n fallback

/-- Approximation is charged on entire fresh trials, before rejection.
No conditioning or division by the implemented acceptance rate occurs. -/
theorem approximate_retry_variation (p q : RationalLaw S) (trial : S → Option A)
    (w : ℚ) (hequal : ∀ a, successMass q trial a = w)
    (fallback : A) (n : ℕ) (ε : ℚ) (happrox : variation p q ≤ ε) :
    variation (retryLaw p trial fallback n) (uniformLaw (α := A)) ≤
      (failureMass q trial)^n + (n : ℚ) * ε := by
  have ht := variation_triangle (retryLaw p trial fallback n)
    (retryLaw q trial fallback n) (uniformLaw (α := A))
  have hr := retryLaw_variation p q trial fallback n
  have hi := equal_success_retry_variation q trial w hequal fallback n
  have hm := mul_le_mul_of_nonneg_left happrox (show (0 : ℚ) ≤ n by positivity)
  linarith

/-- Any ideal success lower bound can be inserted without an oracle assumption. -/
theorem approximate_retry_variation_of_success
    (p q : RationalLaw S) (trial : S → Option A)
    (w : ℚ) (hequal : ∀ a, successMass q trial a = w)
    (fallback : A) (n : ℕ) (ε s : ℚ) (happrox : variation p q ≤ ε)
    (hs : s ≤ 1 - failureMass q trial) :
    variation (retryLaw p trial fallback n) (uniformLaw (α := A)) ≤
      (1 - s)^n + (n : ℚ) * ε := by
  apply (approximate_retry_variation p q trial w hequal fallback n ε happrox).trans
  exact add_le_add (pow_le_pow_left₀ (failure_nonnegative q trial) (by linarith) n) le_rfl

/-- Rational dyadic accuracy avoids real exponential/logarithm arguments. -/
def dyadic (h : ℕ) : ℚ := 1 / (2 : ℚ)^h

def retries (h : ℕ) : ℕ := 4 * (h + 2)

def finePrecision (h : ℕ) : ℕ := h + 2 + Nat.clog 2 (retries h)

lemma retries_positive (h : ℕ) : 0 < retries h := by
  unfold retries
  omega

lemma dyadic_positive (h : ℕ) : 0 < dyadic h := by
  unfold dyadic
  exact div_pos (by norm_num) (pow_pos (by norm_num) h)

lemma dyadic_succ (h : ℕ) : dyadic (h + 1) = dyadic h / 2 := by
  unfold dyadic
  rw [pow_succ, div_mul_eq_div_div]

lemma dyadic_antitone_step (h : ℕ) : dyadic (h + 1) ≤ dyadic h := by
  rw [dyadic_succ]
  have hp := dyadic_positive h
  linarith

/-- Four retries buy at least one binary digit of failure accuracy. -/
theorem geometric_budget (h : ℕ) : (3 / 4 : ℚ)^(retries h) ≤ dyadic (h + 2) := by
  unfold retries
  rw [pow_mul]
  calc
    _ ≤ (1 / 2 : ℚ)^(h + 2) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = dyadic (h + 2) := by rw [div_pow]; simp [dyadic]

/-- Ceiling log makes the total fine-draw error at most one quarter-budget. -/
theorem fine_draw_budget (h : ℕ) :
    (retries h : ℚ) * dyadic (finePrecision h) ≤ dyadic (h + 2) := by
  have hclog : (retries h : ℚ) ≤ (2 : ℚ)^Nat.clog 2 (retries h) := by
    exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (retries h)
  calc
    _ ≤ (2 : ℚ)^Nat.clog 2 (retries h) * dyadic (finePrecision h) :=
      mul_le_mul_of_nonneg_right hclog (dyadic_positive _).le
    _ = dyadic (h + 2) := by
      unfold dyadic finePrecision
      rw [pow_add]
      field_simp

/-- The claimed concrete schedule has a half-target safety margin. -/
theorem retry_budget (h : ℕ) :
    (3 / 4 : ℚ)^(retries h) + (retries h : ℚ) * dyadic (finePrecision h) ≤
      dyadic (h + 1) := by
  have hg := geometric_budget h
  have hf := fine_draw_budget h
  have hd := dyadic_succ (h + 1)
  linarith

theorem retry_budget_target (h : ℕ) :
    (3 / 4 : ℚ)^(retries h) + (retries h : ℚ) * dyadic (finePrecision h) ≤
      dyadic h := (retry_budget h).trans (dyadic_antitone_step h)

/-- A conditional completion-oracle law: equal ideal accepted masses,
ideal success at least 1/4, and fresh fine-law TV accuracy suffice.
The constant acceptance/volume proof is explicitly left as an input. -/
theorem completion_retry_variation_half
    (p q : RationalLaw S) (trial : S → Option A)
    (w : ℚ) (hequal : ∀ a, successMass q trial a = w)
    (hsuccess : (1 / 4 : ℚ) ≤ 1 - failureMass q trial)
    (fallback : A) (h : ℕ) (happrox : variation p q ≤ dyadic (finePrecision h)) :
    variation (retryLaw p trial fallback (retries h)) (uniformLaw (α := A)) ≤
      dyadic (h + 1) := by
  have hb := approximate_retry_variation_of_success p q trial w hequal fallback
    (retries h) (dyadic (finePrecision h)) (1 / 4) happrox hsuccess
  norm_num only at hb
  exact hb.trans (retry_budget h)

theorem completion_retry_variation
    (p q : RationalLaw S) (trial : S → Option A)
    (w : ℚ) (hequal : ∀ a, successMass q trial a = w)
    (hsuccess : (1 / 4 : ℚ) ≤ 1 - failureMass q trial)
    (fallback : A) (h : ℕ) (happrox : variation p q ≤ dyadic (finePrecision h)) :
    variation (retryLaw p trial fallback (retries h)) (uniformLaw (α := A)) ≤ dyadic h :=
  (completion_retry_variation_half p q trial w hequal hsuccess fallback h happrox).trans
    (dyadic_antitone_step h)

end
end Math115.CompletionRetryBudget
