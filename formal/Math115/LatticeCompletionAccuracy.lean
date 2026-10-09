/-
SPDX-License-Identifier: Apache-2.0
Actual finite-table completion accuracy under concrete strong-margin hypotheses.
The volume/count sandwich and analytic constant are supplied by proved modules.
The approximate fine-law accuracy and fresh independent trial semantics remain
explicit; no dense finite-bit realizer or machine-cost theorem is asserted.
-/
import Math115.CompletionAcceptance
import Math115.CompletionCountBound
import Math115.LatticeCompletionLaw

namespace Math115.LatticeCompletionAccuracy

open OAI.ContingencyTables FirstSuccess ResidualMixture
open CompletionAcceptance CompletionCountBound LatticeCompletionFinite
open LatticeCompletionLaw CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section
variable {a b : ℕ}

lemma inflation_three_d (d k : ℕ) : inflation k (3 * d) = dilationFactor d k := by
  simp only [inflation, dilationFactor, Nat.cast_mul, Nat.cast_ofNat]

/-- A supplied feasible fallback supplies both finite-law nonemptiness inputs. -/
theorem ideal_acceptance_quarter (d k : ℕ) (hd : 1 ≤ d) (hk : 2 * d ≤ k)
    (he : (a - 1) * (b - 1) ≤ d - 1)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (htotal : ∑ i, R i = ∑ j, P j)
    (hR : ∀ i, b * (3 * d) ≤ R i) (hP : ∀ j, a * (3 * d) ≤ P j)
    (fallback : Table R P) :
    (1 / 4 : ℚ) ≤ (Fintype.card (AcceptedFine k R P) : ℚ) /
      (Fintype.card (FineTable k R P) : ℚ) := by
  have hkpos : 0 < k := by omega
  letI := fine_nonempty_of_fallback k hkpos R P fallback
  have hAccepted : Fintype.card (AcceptedFine k R P) =
      k^((a - 1) * (b - 1)) * Fintype.card (Table R P) := by
    simpa only [Nat.card_eq_fintype_card, Nat.mul_comm] using accepted_card k hkpos R P
  have hCount := fine_card_le k (3 * d) hkpos (by omega) R P htotal hR hP
  rw [inflation_three_d] at hCount
  exact acceptance_lower_rat d ((a - 1) * (b - 1)) k
    (Fintype.card (FineTable k R P)) (Fintype.card (Table R P))
    (Fintype.card (AcceptedFine k R P)) hd he hk (Fintype.card_pos) hAccepted hCount

def originalUniform (R : Fin a → ℕ) (P : Fin b → ℕ) (fallback : Table R P) :
    RationalLaw (Table R P) := by
  letI : Nonempty (Table R P) := ⟨fallback⟩
  exact uniformLaw

def fineUniform (k : ℕ) (hk : 0 < k) (R : Fin a → ℕ) (P : Fin b → ℕ)
    (fallback : Table R P) : RationalLaw (FineTable k R P) := by
  letI := fine_nonempty_of_fallback k hk R P fallback
  exact uniformLaw

/-- Whole output-law accuracy for the actual finite-table decoder. The quarter
acceptance premise is discharged from strong margins and dimensions. -/
theorem completion_accuracy_half (d k : ℕ) (hd : 1 ≤ d) (hk : 2 * d ≤ k)
    (he : (a - 1) * (b - 1) ≤ d - 1)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (htotal : ∑ i, R i = ∑ j, P j)
    (hR : ∀ i, b * (3 * d) ≤ R i) (hP : ∀ j, a * (3 * d) ≤ P j)
    (fallback : Table R P) (p : RationalLaw (FineTable k R P)) (h : ℕ)
    (happrox : variation p (fineUniform k (by omega) R P fallback) ≤ dyadic (finePrecision h)) :
    variation (retryLaw p (trial k (by omega) R P) fallback (retries h))
      (originalUniform R P fallback) ≤ dyadic (h + 1) := by
  have hkpos : 0 < k := by omega
  letI : Nonempty (Table R P) := ⟨fallback⟩
  letI := fine_nonempty_of_fallback k hkpos R P fallback
  change variation p (uniformLaw (α := FineTable k R P)) ≤ dyadic (finePrecision h) at happrox
  change variation (retryLaw p (trial k hkpos R P) fallback (retries h))
    (uniformLaw (α := Table R P)) ≤ dyadic (h + 1)
  exact LatticeCompletionLaw.completion_accuracy_half k hkpos R P p fallback h
    (ideal_acceptance_quarter d k hd hk he R P htotal hR hP fallback) happrox

theorem completion_accuracy (d k : ℕ) (hd : 1 ≤ d) (hk : 2 * d ≤ k)
    (he : (a - 1) * (b - 1) ≤ d - 1)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (htotal : ∑ i, R i = ∑ j, P j)
    (hR : ∀ i, b * (3 * d) ≤ R i) (hP : ∀ j, a * (3 * d) ≤ P j)
    (fallback : Table R P) (p : RationalLaw (FineTable k R P)) (h : ℕ)
    (happrox : variation p (fineUniform k (by omega) R P fallback) ≤ dyadic (finePrecision h)) :
    variation (retryLaw p (trial k (by omega) R P) fallback (retries h))
      (originalUniform R P fallback) ≤ dyadic h :=
  (completion_accuracy_half d k hd hk he R P htotal hR hP fallback p h happrox).trans
    (dyadic_antitone_step h)

theorem chosen_dilation_acceptance_quarter (d : ℕ) (hd : 2 ≤ d)
    (he : (a - 1) * (b - 1) ≤ d - 1)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (htotal : ∑ i, R i = ∑ j, P j)
    (hR : ∀ i, b * (3 * d) ≤ R i) (hP : ∀ j, a * (3 * d) ≤ P j)
    (fallback : Table R P) :
    (1 / 4 : ℚ) ≤ (Fintype.card (AcceptedFine (d^12) R P) : ℚ) /
      (Fintype.card (FineTable (d^12) R P) : ℚ) :=
  ideal_acceptance_quarter d (d^12) (by omega) (two_mul_le_power_twelve d hd)
    he R P htotal hR hP fallback

/-- Specialization to the exact dilation selected by the completion planner. -/
theorem chosen_dilation_accuracy (d : ℕ) (hd : 2 ≤ d)
    (he : (a - 1) * (b - 1) ≤ d - 1)
    (R : Fin a → ℕ) (P : Fin b → ℕ) (htotal : ∑ i, R i = ∑ j, P j)
    (hR : ∀ i, b * (3 * d) ≤ R i) (hP : ∀ j, a * (3 * d) ≤ P j)
    (fallback : Table R P) (p : RationalLaw (FineTable (d^12) R P)) (h : ℕ)
    (happrox : variation p
      (fineUniform (d^12) (by have hp := two_mul_le_power_twelve d hd; omega) R P fallback) ≤
        dyadic (finePrecision h)) :
    variation (retryLaw p
      (trial (d^12) (by have hp := two_mul_le_power_twelve d hd; omega) R P)
      fallback (retries h)) (originalUniform R P fallback) ≤ dyadic h :=
  completion_accuracy d (d^12) (by omega) (two_mul_le_power_twelve d hd)
    he R P htotal hR hP fallback p h happrox

end
end Math115.LatticeCompletionAccuracy
