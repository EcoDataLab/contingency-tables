/-
SPDX-License-Identifier: Apache-2.0
Finite rational completion law on the literal upstream Table types.
The full accepted-fibre equivalence gives equal successful masses. The constant
acceptance bound is an explicit input; no volume or runtime theorem is asserted.
-/
import Math115.LatticeCompletionFinite
import Math115.CompletionRetryBudget

namespace Math115.LatticeCompletionLaw

open OAI.ContingencyTables FirstSuccess ResidualMixture
open LatticeCompletionFinite CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section
variable {a b : ℕ}

/-- Signed prefix decoding, returning an actual original table only when its
finite cells are all nonnegative. -/
def trial (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (Z : FineTable k R P) : Option (Table R P) :=
  if h : Accepted k R P Z then some (decodeAccepted k hk R P ⟨Z, h⟩) else none

lemma trial_eq_none (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (Z : FineTable k R P) : trial k hk R P Z = none ↔ ¬ Accepted k R P Z := by
  unfold trial
  split_ifs <;> simp_all

/-- The Option-success fibre is exactly the adapter's full accepted fibre. -/
def successfulFiberEquiv (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (X : Table R P) :
    {Z : AcceptedFine k R P // decodeAccepted k hk R P Z = X} ≃
      {Z : FineTable k R P // trial k hk R P Z = some X} where
  toFun Z := ⟨Z.val.val, by simp [trial, Z.val.property, Z.property]⟩
  invFun Z := by
    have ha : Accepted k R P Z.val := by
      by_contra hn
      have hZ := Z.property
      simp [trial, hn] at hZ
    refine ⟨⟨Z.val, ha⟩, ?_⟩
    simpa [trial, ha] using Z.property
  left_inv Z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv Z := by apply Subtype.ext; rfl

theorem successfulFiber_card (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (X : Table R P) :
    Fintype.card {Z : FineTable k R P // trial k hk R P Z = some X} =
      k ^ ((a - 1) * (b - 1)) := by
  calc
    _ = Fintype.card {Z : AcceptedFine k R P // decodeAccepted k hk R P Z = X} :=
      Fintype.card_congr (successfulFiberEquiv k hk R P X).symm
    _ = _ := by
      simpa only [Nat.card_eq_fintype_card] using fixedFiber_card k hk R P X

lemma fine_nonempty_of_fallback (k : ℕ) (hk : 0 < k)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (fallback : Table R P) :
    Nonempty (FineTable k R P) :=
  ⟨encodeTable k hk R P fallback (fun _ _ => ⟨0, hk⟩)⟩

section Laws
variable (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
variable [Nonempty (Table R P)] [Nonempty (FineTable k R P)]

/-- Every original has exactly the same unconditioned ideal accepted mass. -/
theorem ideal_success_mass (X : Table R P) :
    successMass (uniformLaw (α := FineTable k R P)) (trial k hk R P) X =
      (k ^ ((a - 1) * (b - 1)) : ℚ) / (Fintype.card (FineTable k R P) : ℚ) := by
  rw [uniform_success_mass, successfulFiber_card]
  simp only [Nat.cast_pow]

/-- Ideal acceptance is the exact accepted/fine cardinality ratio. -/
theorem ideal_success_probability :
    1 - failureMass (uniformLaw (α := FineTable k R P)) (trial k hk R P) =
      (Fintype.card (AcceptedFine k R P) : ℚ) / (Fintype.card (FineTable k R P) : ℚ) := by
  have ht := success_failure_total (uniformLaw (α := FineTable k R P)) (trial k hk R P)
  simp only [ideal_success_mass, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at ht
  have hc : Fintype.card (AcceptedFine k R P) =
      Fintype.card (Table R P) * k^((a - 1) * (b - 1)) := by
    simpa only [Nat.card_eq_fintype_card] using accepted_card k hk R P
  rw [hc, Nat.cast_mul, Nat.cast_pow, mul_div_assoc]
  linarith

theorem ideal_retry_mass (fallback X : Table R P) (n : ℕ) :
    (retryLaw (uniformLaw (α := FineTable k R P)) (trial k hk R P) fallback n).mass X =
      (1 - (failureMass (uniformLaw (α := FineTable k R P)) (trial k hk R P))^n) *
        uniformMass (α := Table R P) +
        if X = fallback then
          (failureMass (uniformLaw (α := FineTable k R P)) (trial k hk R P))^n else 0 :=
  equal_success_retry_mass _ _ _ (ideal_success_mass k hk R P) fallback X n

/-- Whole-law comparison includes both dense-draw and all-failed fallback
errors, and uses fresh independent fine draws through retryLaw. -/
theorem approximate_retry_bound (p : RationalLaw (FineTable k R P))
    (fallback : Table R P) (n : ℕ) (ε : ℚ)
    (happrox : variation p (uniformLaw (α := FineTable k R P)) ≤ ε) :
    variation (retryLaw p (trial k hk R P) fallback n) (uniformLaw (α := Table R P)) ≤
      (1 - (Fintype.card (AcceptedFine k R P) : ℚ) /
        (Fintype.card (FineTable k R P) : ℚ))^n + (n : ℚ) * ε := by
  have hf : failureMass (uniformLaw (α := FineTable k R P)) (trial k hk R P) =
      1 - (Fintype.card (AcceptedFine k R P) : ℚ) / (Fintype.card (FineTable k R P) : ℚ) := by
    have h := ideal_success_probability k hk R P
    linarith
  simpa only [hf] using approximate_retry_variation p (uniformLaw (α := FineTable k R P))
    (trial k hk R P) _ (ideal_success_mass k hk R P) fallback n ε happrox

/-- Conditional finite-table completion oracle at the explicit dyadic schedule.
The cardinality lower bound is the still-separate geometric obligation. -/
theorem completion_accuracy_half (p : RationalLaw (FineTable k R P))
    (fallback : Table R P) (h : ℕ)
    (haccept : (1 / 4 : ℚ) ≤
      (Fintype.card (AcceptedFine k R P) : ℚ) / (Fintype.card (FineTable k R P) : ℚ))
    (happrox : variation p (uniformLaw (α := FineTable k R P)) ≤ dyadic (finePrecision h)) :
    variation (retryLaw p (trial k hk R P) fallback (retries h))
      (uniformLaw (α := Table R P)) ≤ dyadic (h + 1) := by
  apply completion_retry_variation_half p (uniformLaw (α := FineTable k R P))
    (trial k hk R P) _ (ideal_success_mass k hk R P) _ fallback h happrox
  rw [ideal_success_probability]
  exact haccept

theorem completion_accuracy (p : RationalLaw (FineTable k R P))
    (fallback : Table R P) (h : ℕ)
    (haccept : (1 / 4 : ℚ) ≤
      (Fintype.card (AcceptedFine k R P) : ℚ) / (Fintype.card (FineTable k R P) : ℚ))
    (happrox : variation p (uniformLaw (α := FineTable k R P)) ≤ dyadic (finePrecision h)) :
    variation (retryLaw p (trial k hk R P) fallback (retries h))
      (uniformLaw (α := Table R P)) ≤ dyadic h :=
  (completion_accuracy_half k hk R P p fallback h haccept happrox).trans (dyadic_antitone_step h)

end Laws
end
end Math115.LatticeCompletionLaw
