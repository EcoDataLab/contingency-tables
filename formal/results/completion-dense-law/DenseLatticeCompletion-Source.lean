/-
SPDX-License-Identifier: Apache-2.0
Explicit finite Boolean-word dense draws followed by lattice completion.
The analytic inputs are exact published source propositions, discharged in a
separate wrapper. No fine-law accuracy premise is assumed by the final bound.
Compiled codec/retry realization and composed machine cost remain separate.
-/
import Math115.LatticeCompletionAccuracy
import Math115.CompletionBooleanRetry
import OAI.Combinatorics.ContingencyTables.Dense.DenseCanonicalSemantics

namespace Math115.DenseLatticeCompletion

open OAI.ContingencyTables FirstSuccess ResidualMixture FairBits DensePrograms
open LatticeCompletionFinite LatticeCompletionLaw CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma dilation_positive (d : ℕ) (hd : 14 ≤ d) : 0 < d^12 := by
  have hp : 0 < d := by omega
  exact pow_pos hp _

def denseRows (k n : ℕ) (R : Fin (m + 1) → ℕ) : Option (Fin m) → ℕ :=
  fun i => fineMargin k (n + 1) R ((finSuccEquiv m).symm i)

def denseColumns (k m : ℕ) (P : Fin (n + 1) → ℕ) : Option (Fin n) → ℕ :=
  fun j => fineMargin k (m + 1) P ((finSuccEquiv n).symm j)

/-- This preserves the original finite cell order after a dense Option draw. -/
def fineOptionEquiv (k : ℕ) (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ) :
    FineTable k R P ≃ Table (denseRows k n R) (denseColumns k m P) :=
  tableReindex (finSuccEquiv m).symm (finSuccEquiv n).symm
    (fineMargin k (n + 1) R) (fineMargin k (m + 1) P)

lemma optionMargin_code (f : Fin (m + 1) → ℕ) :
    marginCode (fun i => f ((finSuccEquiv m).symm i)) = List.ofFn f := by
  rw [marginCode_ofFn]
  apply congrArg List.ofFn
  funext i
  exact congrArg f ((finSuccEquiv m).symm_apply_apply i)

lemma fineOption_tableOutput (k : ℕ) (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (X : FineTable k R P) :
    tableOutput ((fineOptionEquiv k R P) X) = matrixCode X.val := by
  change matrixCode (fun i j => X.val
    ((finSuccEquiv m).symm (finSuccEquiv m i))
    ((finSuccEquiv n).symm (finSuccEquiv n j))) = _
  simp only [Equiv.symm_apply_apply]

lemma denseRows_minimum (d : ℕ) (R : Fin (m + 1) → ℕ) (i : Option (Fin m)) :
    d^12 ≤ denseRows (d^12) n R i := by
  have h : 1 ≤ R ((finSuccEquiv m).symm i) + 2 * (n + 1) := by omega
  simpa only [denseRows, fineMargin, Nat.mul_one] using Nat.mul_le_mul_left (d^12) h

lemma denseColumns_minimum (d : ℕ) (P : Fin (n + 1) → ℕ) (j : Option (Fin n)) :
    d^12 ≤ denseColumns (d^12) m P j := by
  have h : 1 ≤ P ((finSuccEquiv n).symm j) + 2 * (m + 1) := by omega
  simpa only [denseColumns, fineMargin, Nat.mul_one] using Nat.mul_le_mul_left (d^12) h

lemma dense_totals (k : ℕ) (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) :
    (∑ i, denseRows k n R i) = ∑ j, denseColumns k m P j := by
  unfold denseRows denseColumns
  rw [(finSuccEquiv m).symm.sum_comp, (finSuccEquiv n).symm.sum_comp]
  simp only [fineMargin, ← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  rw [htotal]
  ring

def fineBits (d : ℕ) (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ) (precision : ℕ) : ℕ :=
  normalizedDrawBits (denseRows (d^12) n R) (denseColumns (d^12) m P) d precision

lemma fineBits_pos (d : ℕ) (hd : 0 < d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ) (precision : ℕ) :
    0 < fineBits d R P precision := by
  unfold fineBits normalizedDrawBits GridBoundary.denseDrawBits
  exact Nat.mul_pos (Nat.mul_pos (pow_pos hd _) (by omega))
    (denseTrialBits_pos hd _ _ precision)

/-- One explicit fixed-width word, with canonical computed dense initialization
and fallback, transported back to the literal fine-table type. -/
def fineDraw (d : ℕ) (hd : 14 ≤ d) (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (precision : ℕ)
    (bits : Fin (fineBits d R P precision) → Bool) : FineTable (d^12) R P :=
  (fineOptionEquiv (d^12) R P).symm
    (normalizedBooleanDraw (denseRows (d^12) n R) (denseColumns (d^12) m P) hd
      (denseRows_minimum d R) (denseColumns_minimum d P) (dense_totals (d^12) R P htotal)
      precision (canonicalOrigin (m * n) d (by omega))
      (canonicalFallback _ _ (dense_totals (d^12) R P htotal)) bits)

/-- The typed draw is exactly the output of the unchanged canonical program,
in its documented Option-index matrix encoding. -/
theorem fineDraw_canonicalCode (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (precision : ℕ)
    (bits : Fin (fineBits d R P precision) → Bool) :
    canonicalDenseDraw (((marginCode (denseRows (d^12) n R),
      marginCode (denseColumns (d^12) m P)), (d, precision)), List.ofFn bits) =
      tableOutput ((fineOptionEquiv (d^12) R P) (fineDraw d hd R P htotal precision bits)) := by
  simp only [fineDraw, Equiv.apply_symm_apply]
  exact canonicalDenseDraw_eq _ _ hd (denseRows_minimum d R) (denseColumns_minimum d P)
    (dense_totals (d^12) R P htotal) precision bits

theorem fineDraw_matrixCode (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (precision : ℕ)
    (bits : Fin (fineBits d R P precision) → Bool) :
    canonicalDenseDraw (((marginCode (denseRows (d^12) n R),
      marginCode (denseColumns (d^12) m P)), (d, precision)), List.ofFn bits) =
      matrixCode (fineDraw d hd R P htotal precision bits).val := by
  rw [← fineOption_tableOutput (d^12) R P]
  exact fineDraw_canonicalCode d hd R P htotal precision bits

def fineLaw (d : ℕ) (hd : 14 ≤ d) (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (precision : ℕ) : RationalLaw (FineTable (d^12) R P) :=
  mapLaw (uniformLaw (α := Fin (fineBits d R P precision) → Bool))
    (fineDraw d hd R P htotal precision)

lemma dyadic_cast (precision : ℕ) :
    (dyadic precision : ℝ) = (2 : ℝ)^(-(precision : ℝ)) := by
  unfold dyadic
  simp only [one_div, Rat.cast_inv, Rat.cast_pow, Rat.cast_ofNat,
    Real.rpow_neg_natCast, zpow_neg, zpow_natCast]

/-- The rational fine-law error follows from the actual uniform Boolean-word
experiment; no approximate-oracle assumption is made. Zero tail dimensions
are allowed, with full row/column dimensions kept explicit. -/
theorem fineLaw_variation (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (fallback : Table R P)
    (hdimR : m + 1 ≤ d) (hdimP : n + 1 ≤ d) (hfree : m * n ≤ d)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (m * n))
    (hCheeger : PublishedInputs.FiniteCheeger
      (GridBoundary.Grid (I := Fin (m * n)) (4 * d^8))) (precision : ℕ) :
    variation (fineLaw d hd R P htotal precision)
      (LatticeCompletionAccuracy.fineUniform (d^12) (dilation_positive d hd)
        R P fallback) ≤ dyadic precision := by
  have hk : 0 < d^12 := dilation_positive d hd
  letI := fine_nonempty_of_fallback (d^12) hk R P fallback
  let E := fineOptionEquiv (d^12) R P
  letI : Nonempty (Table (denseRows (d^12) n R) (denseColumns (d^12) m P)) :=
    ⟨canonicalFallback _ _ (dense_totals (d^12) R P htotal)⟩
  have hv := canonicalDenseDraw_variation (denseRows (d^12) n R) (denseColumns (d^12) m P)
    hd (denseRows_minimum d R) (denseColumns_minimum d P)
    (by simpa only [Fintype.card_option, Fintype.card_fin] using hdimR)
    (by simpa only [Fintype.card_option, Fintype.card_fin] using hdimP)
    (by simpa only [Fintype.card_prod, Fintype.card_fin] using hfree)
    (dense_totals (d^12) R P htotal) hPL hCheeger precision
  apply (Rat.cast_le (K := ℝ)).mp
  rw [dyadic_cast]
  change (variation (mapLaw (uniformLaw (α :=
      Fin (normalizedDrawBits (denseRows (d^12) n R) (denseColumns (d^12) m P) d precision) → Bool))
    (fun bits => E.symm (normalizedBooleanDraw _ _ hd (denseRows_minimum d R)
      (denseColumns_minimum d P) (dense_totals (d^12) R P htotal) precision
      (canonicalOrigin (m * n) d (by omega))
      (canonicalFallback _ _ (dense_totals (d^12) R P htotal)) bits)))
    (uniformLaw (α := FineTable (d^12) R P)) : ℝ) ≤ _
  rw [mapLaw_equiv_output, ← uniform_equiv E.symm, variation_equiv]
  exact hv

theorem fineBits_polynomial (d C b precision : ℕ)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (hfree : m * n ≤ d) (hR : ∀ i, denseRows (d^12) n R i ≤ C)
    (hb : Nat.clog 2 (C + 2) ≤ b) :
    fineBits d R P precision ≤ 25 * (d + b + precision + 1)^62 :=
  normalizedDrawBits_polynomial _ _ d C b precision hfree hR hb

def completionLaw (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (fallback : Table R P) (h : ℕ) :
    RationalLaw (Table R P) :=
  retryLaw (fineLaw d hd R P htotal (finePrecision h))
    (trial (d^12) (dilation_positive d hd) R P) fallback (retries h)

/-- Dense fine draws instantiated into the proven lattice completion schedule.
The remaining hypotheses are numeric/geometric input margins and the published
analytic propositions, not a fine-law TV assumption. -/
theorem completionLaw_variation (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hdimR : m + 1 ≤ d) (hdimP : n + 1 ≤ d) (hfree : m * n ≤ d - 1)
    (hR : ∀ i, (n + 1) * (3 * d) ≤ R i) (hP : ∀ j, (m + 1) * (3 * d) ≤ P j)
    (fallback : Table R P)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (m * n))
    (hCheeger : PublishedInputs.FiniteCheeger
      (GridBoundary.Grid (I := Fin (m * n)) (4 * d^8))) (h : ℕ) :
    variation (completionLaw d hd R P htotal fallback h)
      (LatticeCompletionAccuracy.originalUniform R P fallback) ≤ dyadic h := by
  unfold completionLaw
  apply LatticeCompletionAccuracy.chosen_dilation_accuracy d (by omega)
    (by simpa only [Nat.add_sub_cancel] using hfree) R P htotal hR hP fallback
    (fineLaw d hd R P htotal (finePrecision h)) h
  exact fineLaw_variation d hd R P htotal fallback hdimR hdimP (by omega)
    hPL hCheeger (finePrecision h)

def completionBits (d : ℕ) (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ) (h : ℕ) : ℕ :=
  retries h * fineBits d R P (finePrecision h)

/-- A random-bit allowance only, without a machine running-time assertion. -/
theorem completionBits_bound (d C b h : ℕ)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (hfree : m * n ≤ d) (hR : ∀ i, denseRows (d^12) n R i ≤ C)
    (hb : Nat.clog 2 (C + 2) ≤ b) :
    completionBits d R P h ≤ retries h * (25 * (d + b + finePrecision h + 1)^62) :=
  Nat.mul_le_mul_left (retries h)
    (fineBits_polynomial d C b (finePrecision h) R P hfree hR hb)

/-- One whole Boolean word, partitioned into fresh dense-trial words. -/
def completionDraw (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (fallback : Table R P) (h : ℕ)
    (bits : Fin (completionBits d R P h) → Bool) : Table R P :=
  CompletionBooleanRetry.flatRetry
    (fun word => CompletionBooleanRetry.tableTrial (d^12) (dilation_positive d hd) R P
      (fineDraw d hd R P htotal (finePrecision h) word)) fallback (retries h) bits

/-- The complete Boolean source has exactly the bounded independent-retry law. -/
theorem completionDraw_law (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j) (fallback : Table R P) (h : ℕ) :
    mapLaw (uniformLaw (α := Fin (completionBits d R P h) → Bool))
      (completionDraw d hd R P htotal fallback h) = completionLaw d hd R P htotal fallback h :=
  CompletionBooleanRetry.completion_flat_law (d^12) (dilation_positive d hd) R P
    (fineDraw d hd R P htotal (finePrecision h)) fallback (retries h)

theorem completionDraw_variation (d : ℕ) (hd : 14 ≤ d)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hdimR : m + 1 ≤ d) (hdimP : n + 1 ≤ d) (hfree : m * n ≤ d - 1)
    (hR : ∀ i, (n + 1) * (3 * d) ≤ R i) (hP : ∀ j, (m + 1) * (3 * d) ≤ P j)
    (fallback : Table R P)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (m * n))
    (hCheeger : PublishedInputs.FiniteCheeger
      (GridBoundary.Grid (I := Fin (m * n)) (4 * d^8))) (h : ℕ) :
    variation (mapLaw (uniformLaw (α := Fin (completionBits d R P h) → Bool))
      (completionDraw d hd R P htotal fallback h))
      (LatticeCompletionAccuracy.originalUniform R P fallback) ≤ dyadic h := by
  rw [completionDraw_law]
  exact completionLaw_variation d hd R P htotal hdimR hdimP hfree hR hP fallback hPL hCheeger h

end
end Math115.DenseLatticeCompletion
