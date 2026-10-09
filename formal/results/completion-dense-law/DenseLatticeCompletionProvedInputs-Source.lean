/-
SPDX-License-Identifier: Apache-2.0
Discharge the exact published analytic propositions for the dense lattice
completion law using their unchanged pinned source proofs. Numeric dimensions,
actual margin bounds, and a feasible fallback remain explicit inputs.
-/
import Math115.DenseLatticeCompletion
import OAI.Combinatorics.ContingencyTables.Dense.FiniteBoxPrekopa
import OAI.Combinatorics.ContingencyTables.Dense.FiniteCheegerProof

namespace Math115.DenseLatticeCompletionProvedInputs

open OAI.ContingencyTables FirstSuccess
open DenseLatticeCompletion CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

theorem fineLaw_variation (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (fallback : Table R P)
    (hdimR : m + 1 ≤ d) (hdimP : n + 1 ≤ d) (hfree : m * n ≤ d) (precision : ℕ) :
    variation (fineLaw d hd R P htotal precision)
      (LatticeCompletionAccuracy.fineUniform (d^12) (dilation_positive d hd)
        R P fallback) ≤ dyadic precision :=
  DenseLatticeCompletion.fineLaw_variation d hd R P htotal fallback hdimR hdimP hfree
    (PublishedInputs.finiteBoxPrekopaLeindler (m * n))
    (CheegerProof.finiteCheeger
      (X := GridBoundary.Grid (I := Fin (m * n)) (4 * d^8))) precision

/-- Actual fresh finite-word dense completion with no assumed law accuracy,
count comparison, acceptance probability, or analytic proposition. -/
theorem completionLaw_variation (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hdimR : m + 1 ≤ d) (hdimP : n + 1 ≤ d) (hfree : m * n ≤ d - 1)
    (hR : ∀ i, (n + 1) * (3 * d) ≤ R i) (hP : ∀ j, (m + 1) * (3 * d) ≤ P j)
    (fallback : Table R P) (h : ℕ) :
    variation (completionLaw d hd R P htotal fallback h)
      (LatticeCompletionAccuracy.originalUniform R P fallback) ≤ dyadic h :=
  DenseLatticeCompletion.completionLaw_variation d hd R P htotal hdimR hdimP hfree
    hR hP fallback (PublishedInputs.finiteBoxPrekopaLeindler (m * n))
    (CheegerProof.finiteCheeger
      (X := GridBoundary.Grid (I := Fin (m * n)) (4 * d^8))) h

theorem completionDraw_variation (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hdimR : m + 1 ≤ d) (hdimP : n + 1 ≤ d) (hfree : m * n ≤ d - 1)
    (hR : ∀ i, (n + 1) * (3 * d) ≤ R i) (hP : ∀ j, (m + 1) * (3 * d) ≤ P j)
    (fallback : Table R P) (h : ℕ) :
    variation (mapLaw (uniformLaw (α := Fin (completionBits d R P h) → Bool))
      (completionDraw d hd R P htotal fallback h))
      (LatticeCompletionAccuracy.originalUniform R P fallback) ≤ dyadic h := by
  rw [completionDraw_law]
  exact completionLaw_variation d hd R P htotal hdimR hdimP hfree hR hP fallback h

end
end Math115.DenseLatticeCompletionProvedInputs
