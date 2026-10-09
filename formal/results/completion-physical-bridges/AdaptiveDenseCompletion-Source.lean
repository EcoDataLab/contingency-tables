/-
SPDX-License-Identifier: Apache-2.0
Optional additive candidate: independent dense dimension D, geometric dimension
 g, and positive integer dilation k. This draft does not select those parameters,
assemble a physical oracle, or replace any d^12 baseline declaration.

The exact canonical dense order and computed maximum normalization are retained.
A new finite Boolean experiment is defined; equality with a different approximate
baseline law is not asserted. Analytic and numerical hypotheses remain explicit.
-/
import Math115.DenseLatticeCompletion
import OAI.Combinatorics.ContingencyTables.Transport.FiniteDeterministicJoint

namespace Math115.AdaptiveDenseCompletion

open OAI.ContingencyTables FirstSuccess ResidualMixture FairBits DensePrograms
open LatticeCompletionFinite LatticeCompletionLaw CompletionRetryBudget
open DenseLatticeCompletion
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}

lemma denseRows_lower (D k : ℕ) (R : Fin (m + 1) → ℕ)
    (hR : ∀ i, D^12 ≤ fineMargin k (n + 1) R i) (i : Option (Fin m)) :
    D^12 ≤ denseRows k n R i := hR ((finSuccEquiv m).symm i)

lemma denseColumns_lower (D k : ℕ) (P : Fin (n + 1) → ℕ)
    (hP : ∀ j, D^12 ≤ fineMargin k (m + 1) P j) (j : Option (Fin n)) :
    D^12 ≤ denseColumns k m P j := hP ((finSuccEquiv n).symm j)

/-- Exact width of the new canonical fine experiment, with its actual computed
maximum normalization. Both full dimensions are positive; either tail may be zero. -/
def fineBits (D k : ℕ) (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (precision : ℕ) : ℕ :=
  normalizedDrawBits (denseRows k n R) (denseColumns k m P) D precision

lemma fineBits_pos (D k : ℕ) (hD : 0 < D)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ) (precision : ℕ) :
    0 < fineBits D k R P precision := by
  unfold fineBits normalizedDrawBits GridBoundary.denseDrawBits
  exact Nat.mul_pos (Nat.mul_pos (pow_pos hD _) (by omega))
    (denseTrialBits_pos hD _ _ precision)

/-- The canonical dense draw at D, with fine margins determined by k, transported
back into the literal finite-cell order used by the signed prefix decoder. -/
def fineDraw (D k : ℕ) (hD : 14 ≤ D)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hFineR : ∀ i, D^12 ≤ fineMargin k (n + 1) R i)
    (hFineP : ∀ j, D^12 ≤ fineMargin k (m + 1) P j) (precision : ℕ)
    (bits : Fin (fineBits D k R P precision) → Bool) : FineTable k R P :=
  (fineOptionEquiv k R P).symm
    (normalizedBooleanDraw (denseRows k n R) (denseColumns k m P) hD
      (denseRows_lower D k R hFineR) (denseColumns_lower D k P hFineP)
      (dense_totals k R P htotal) precision
      (canonicalOrigin (m * n) D (by omega))
      (canonicalFallback _ _ (dense_totals k R P htotal)) bits)

/-- Every Boolean input agrees with the unchanged canonical program called with
these explicit margins and D, including the dense all-rejected fallback. -/
theorem fineDraw_canonicalCode (D k : ℕ) (hD : 14 ≤ D)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hFineR : ∀ i, D^12 ≤ fineMargin k (n + 1) R i)
    (hFineP : ∀ j, D^12 ≤ fineMargin k (m + 1) P j) (precision : ℕ)
    (bits : Fin (fineBits D k R P precision) → Bool) :
    canonicalDenseDraw (((marginCode (denseRows k n R), marginCode (denseColumns k m P)),
      (D, precision)), List.ofFn bits) =
      tableOutput ((fineOptionEquiv k R P)
        (fineDraw D k hD R P htotal hFineR hFineP precision bits)) := by
  simp only [fineDraw, Equiv.apply_symm_apply]
  exact canonicalDenseDraw_eq _ _ hD (denseRows_lower D k R hFineR)
    (denseColumns_lower D k P hFineP) (dense_totals k R P htotal) precision bits

theorem fineDraw_matrixCode (D k : ℕ) (hD : 14 ≤ D)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hFineR : ∀ i, D^12 ≤ fineMargin k (n + 1) R i)
    (hFineP : ∀ j, D^12 ≤ fineMargin k (m + 1) P j) (precision : ℕ)
    (bits : Fin (fineBits D k R P precision) → Bool) :
    canonicalDenseDraw (((marginCode (denseRows k n R), marginCode (denseColumns k m P)),
      (D, precision)), List.ofFn bits) =
      matrixCode (fineDraw D k hD R P htotal hFineR hFineP precision bits).val := by
  rw [← fineOption_tableOutput k R P]
  exact fineDraw_canonicalCode D k hD R P htotal hFineR hFineP precision bits

def fineLaw (D k : ℕ) (hD : 14 ≤ D)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hFineR : ∀ i, D^12 ≤ fineMargin k (n + 1) R i)
    (hFineP : ∀ j, D^12 ≤ fineMargin k (m + 1) P j) (precision : ℕ) :
    RationalLaw (FineTable k R P) :=
  mapLaw (uniformLaw (α := Fin (fineBits D k R P precision) → Bool))
    (fineDraw D k hD R P htotal hFineR hFineP precision)

/-- Fine-law TV is supplied by the actual canonical finite Boolean experiment at
D. No approximate fine-law premise is assumed; the two analytic inputs are explicit. -/
theorem fineLaw_variation (D k : ℕ) (hD : 14 ≤ D) (hk : 0 < k)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hFineR : ∀ i, D^12 ≤ fineMargin k (n + 1) R i)
    (hFineP : ∀ j, D^12 ≤ fineMargin k (m + 1) P j) (fallback : Table R P)
    (hdimR : m + 1 ≤ D) (hdimP : n + 1 ≤ D) (hfree : m * n ≤ D)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (m * n))
    (hCheeger : PublishedInputs.FiniteCheeger
      (GridBoundary.Grid (I := Fin (m * n)) (4 * D^8))) (precision : ℕ) :
    variation (fineLaw D k hD R P htotal hFineR hFineP precision)
      (LatticeCompletionAccuracy.fineUniform k hk R P fallback) ≤ dyadic precision := by
  letI := fine_nonempty_of_fallback k hk R P fallback
  let E := fineOptionEquiv k R P
  letI : Nonempty (Table (denseRows k n R) (denseColumns k m P)) :=
    ⟨canonicalFallback _ _ (dense_totals k R P htotal)⟩
  have hv := canonicalDenseDraw_variation (denseRows k n R) (denseColumns k m P)
    hD (denseRows_lower D k R hFineR) (denseColumns_lower D k P hFineP)
    (by simpa only [Fintype.card_option, Fintype.card_fin] using hdimR)
    (by simpa only [Fintype.card_option, Fintype.card_fin] using hdimP)
    (by simpa only [Fintype.card_prod, Fintype.card_fin] using hfree)
    (dense_totals k R P htotal) hPL hCheeger precision
  apply (Rat.cast_le (K := ℝ)).mp
  rw [DenseLatticeCompletion.dyadic_cast]
  change (variation (mapLaw (uniformLaw (α := Fin
      (normalizedDrawBits (denseRows k n R) (denseColumns k m P) D precision) → Bool))
    (fun bits => E.symm (normalizedBooleanDraw _ _ hD
      (denseRows_lower D k R hFineR) (denseColumns_lower D k P hFineP)
      (dense_totals k R P htotal) precision (canonicalOrigin (m * n) D (by omega))
      (canonicalFallback _ _ (dense_totals k R P htotal)) bits)))
    (uniformLaw (α := FineTable k R P)) : ℝ) ≤ _
  rw [mapLaw_equiv_output, ← uniform_equiv E.symm, variation_equiv]
  exact hv

theorem fineBits_polynomial (D k C b precision : ℕ)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (hfree : m * n ≤ D) (hR : ∀ i, denseRows k n R i ≤ C)
    (hb : Nat.clog 2 (C + 2) ≤ b) :
    fineBits D k R P precision ≤ 25 * (D + b + precision + 1)^62 :=
  normalizedDrawBits_polynomial _ _ D C b precision hfree hR hb

/-- New normalized bounded completion law. The geometric dimension g does not
enter its execution; it is a proof parameter in its accuracy theorem. -/
def completionLaw (D k : ℕ) (hD : 14 ≤ D) (hk : 0 < k)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hFineR : ∀ i, D^12 ≤ fineMargin k (n + 1) R i)
    (hFineP : ∀ j, D^12 ≤ fineMargin k (m + 1) P j)
    (fallback : Table R P) (h : ℕ) : RationalLaw (Table R P) :=
  retryLaw (fineLaw D k hD R P htotal hFineR hFineP (finePrecision h))
    (trial k hk R P) fallback (retries h)

/-- Dense correctness uses D, while quarter acceptance uses g. No comparison
between D and g is required. All-failed lattice mass is retained in the bound. -/
theorem completionLaw_variation_half (D g k : ℕ) (hD : 14 ≤ D) (hg : 1 ≤ g)
    (hk : 0 < k) (hkg : 2 * g ≤ k)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hFineR : ∀ i, D^12 ≤ fineMargin k (n + 1) R i)
    (hFineP : ∀ j, D^12 ≤ fineMargin k (m + 1) P j)
    (hdimR : m + 1 ≤ D) (hdimP : n + 1 ≤ D) (hfreeD : m * n ≤ D)
    (hfreeG : m * n ≤ g - 1)
    (hR : ∀ i, (n + 1) * (3 * g) ≤ R i)
    (hP : ∀ j, (m + 1) * (3 * g) ≤ P j) (fallback : Table R P)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (m * n))
    (hCheeger : PublishedInputs.FiniteCheeger
      (GridBoundary.Grid (I := Fin (m * n)) (4 * D^8))) (h : ℕ) :
    variation (completionLaw D k hD hk R P htotal hFineR hFineP fallback h)
      (LatticeCompletionAccuracy.originalUniform R P fallback) ≤ dyadic (h + 1) := by
  unfold completionLaw
  apply LatticeCompletionAccuracy.completion_accuracy_half g k hg hkg
    (by simpa only [Nat.add_sub_cancel] using hfreeG) R P htotal hR hP fallback
    (fineLaw D k hD R P htotal hFineR hFineP (finePrecision h)) h
  exact fineLaw_variation D k hD hk R P htotal hFineR hFineP fallback
    hdimR hdimP hfreeD hPL hCheeger (finePrecision h)

theorem completionLaw_variation (D g k : ℕ) (hD : 14 ≤ D) (hg : 1 ≤ g)
    (hk : 0 < k) (hkg : 2 * g ≤ k)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hFineR : ∀ i, D^12 ≤ fineMargin k (n + 1) R i)
    (hFineP : ∀ j, D^12 ≤ fineMargin k (m + 1) P j)
    (hdimR : m + 1 ≤ D) (hdimP : n + 1 ≤ D) (hfreeD : m * n ≤ D)
    (hfreeG : m * n ≤ g - 1)
    (hR : ∀ i, (n + 1) * (3 * g) ≤ R i)
    (hP : ∀ j, (m + 1) * (3 * g) ≤ P j) (fallback : Table R P)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (m * n))
    (hCheeger : PublishedInputs.FiniteCheeger
      (GridBoundary.Grid (I := Fin (m * n)) (4 * D^8))) (h : ℕ) :
    variation (completionLaw D k hD hk R P htotal hFineR hFineP fallback h)
      (LatticeCompletionAccuracy.originalUniform R P fallback) ≤ dyadic h :=
  (completionLaw_variation_half D g k hD hg hk hkg R P htotal hFineR hFineP
    hdimR hdimP hfreeD hfreeG hR hP fallback hPL hCheeger h).trans (dyadic_antitone_step h)

def completionBits (D k : ℕ) (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ) (h : ℕ) : ℕ :=
  retries h * fineBits D k R P (finePrecision h)

/-- Bit reservation only. A composed encoded realizer and machine cost are not
provided by this candidate. -/
theorem completionBits_bound (D k C b h : ℕ)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (hfree : m * n ≤ D) (hR : ∀ i, denseRows k n R i ≤ C)
    (hb : Nat.clog 2 (C + 2) ≤ b) :
    completionBits D k R P h ≤ retries h * (25 * (D + b + finePrecision h + 1)^62) :=
  Nat.mul_le_mul_left (retries h)
    (fineBits_polynomial D k C b (finePrecision h) R P hfree hR hb)

/-- One flat word uses disjoint fresh fine words in retry order, preserving the
supplied ordinary fallback on all failures. -/
def completionDraw (D k : ℕ) (hD : 14 ≤ D) (hk : 0 < k)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hFineR : ∀ i, D^12 ≤ fineMargin k (n + 1) R i)
    (hFineP : ∀ j, D^12 ≤ fineMargin k (m + 1) P j) (fallback : Table R P) (h : ℕ)
    (bits : Fin (completionBits D k R P h) → Bool) : Table R P :=
  CompletionBooleanRetry.flatRetry
    (fun word => CompletionBooleanRetry.tableTrial k hk R P
      (fineDraw D k hD R P htotal hFineR hFineP (finePrecision h) word))
    fallback (retries h) bits

theorem completionDraw_law (D k : ℕ) (hD : 14 ≤ D) (hk : 0 < k)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hFineR : ∀ i, D^12 ≤ fineMargin k (n + 1) R i)
    (hFineP : ∀ j, D^12 ≤ fineMargin k (m + 1) P j) (fallback : Table R P) (h : ℕ) :
    mapLaw (uniformLaw (α := Fin (completionBits D k R P h) → Bool))
      (completionDraw D k hD hk R P htotal hFineR hFineP fallback h) =
      completionLaw D k hD hk R P htotal hFineR hFineP fallback h :=
  CompletionBooleanRetry.completion_flat_law k hk R P
    (fineDraw D k hD R P htotal hFineR hFineP (finePrecision h)) fallback (retries h)

theorem completionDraw_variation (D g k : ℕ) (hD : 14 ≤ D) (hg : 1 ≤ g)
    (hk : 0 < k) (hkg : 2 * g ≤ k)
    (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (htotal : ∑ i, R i = ∑ j, P j)
    (hFineR : ∀ i, D^12 ≤ fineMargin k (n + 1) R i)
    (hFineP : ∀ j, D^12 ≤ fineMargin k (m + 1) P j)
    (hdimR : m + 1 ≤ D) (hdimP : n + 1 ≤ D) (hfreeD : m * n ≤ D)
    (hfreeG : m * n ≤ g - 1)
    (hR : ∀ i, (n + 1) * (3 * g) ≤ R i)
    (hP : ∀ j, (m + 1) * (3 * g) ≤ P j) (fallback : Table R P)
    (hPL : PublishedInputs.FiniteBoxPrekopaLeindler (m * n))
    (hCheeger : PublishedInputs.FiniteCheeger
      (GridBoundary.Grid (I := Fin (m * n)) (4 * D^8))) (h : ℕ) :
    variation (mapLaw (uniformLaw (α := Fin (completionBits D k R P h) → Bool))
      (completionDraw D k hD hk R P htotal hFineR hFineP fallback h))
      (LatticeCompletionAccuracy.originalUniform R P fallback) ≤ dyadic h := by
  rw [completionDraw_law]
  exact completionLaw_variation D g k hD hg hk hkg R P htotal hFineR hFineP
    hdimR hdimP hfreeD hfreeG hR hP fallback hPL hCheeger h

/-- At most one full row includes the empty case. When a cell exists, its
column equation determines it; no table nonemptiness premise is needed. -/
lemma table_subsingleton_of_row_card_le_one {I J : Type*} [Fintype I] [Fintype J]
    (R : I → ℕ) (P : J → ℕ) (hI : Fintype.card I ≤ 1) :
    Subsingleton (Table R P) := by
  letI : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hI
  refine ⟨fun X Y => ?_⟩
  apply Subtype.ext
  funext i j
  letI : Unique I := ⟨⟨i⟩, fun x => Subsingleton.elim x i⟩
  have hdefault : (default : I) = i := Subsingleton.elim _ _
  simpa only [Fintype.sum_unique, hdefault] using (X.property.2 j).trans (Y.property.2 j).symm

/-- At most one full column includes the empty case. Every existing cell is
determined by its row equation, including zero margins. -/
lemma table_subsingleton_of_column_card_le_one {I J : Type*} [Fintype I] [Fintype J]
    (R : I → ℕ) (P : J → ℕ) (hJ : Fintype.card J ≤ 1) :
    Subsingleton (Table R P) := by
  letI : Subsingleton J := Fintype.card_le_one_iff_subsingleton.mp hJ
  refine ⟨fun X Y => ?_⟩
  apply Subtype.ext
  funext i j
  letI : Unique J := ⟨⟨j⟩, fun y => Subsingleton.elim y j⟩
  have hdefault : (default : J) = j := Subsingleton.elim _ _
  simpa only [Fintype.sum_unique, hdefault] using (X.property.1 i).trans (Y.property.1 i).symm

/-- A zero tail is a one-row or one-column full table, not an empty full index
set. The generic cardinality lemmas supply uniqueness without assuming it. -/
lemma table_subsingleton_of_zero_tail (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (hs : m = 0 ∨ n = 0) : Subsingleton (Table R P) := by
  rcases hs with hm | hn
  · exact table_subsingleton_of_row_card_le_one R P (by simp [hm])
  · exact table_subsingleton_of_column_card_le_one R P (by simp [hn])

/-- Optional zero-bit singleton draw. No dense or geometric hypothesis is
needed. It is a separate branch, not installed into completionDraw above. -/
def singletonDraw (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (fallback : Table R P) (_bits : Fin 0 → Bool) : Table R P := fallback

theorem singletonDraw_pointLaw (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (fallback : Table R P) :
    mapLaw (uniformLaw (α := Fin 0 → Bool)) (singletonDraw R P fallback) =
      pointLaw fallback := by
  let p : RationalLaw (Fin 0 → Bool) := uniformLaw
  change mapLaw p (fun _ => fallback) = pointLaw fallback
  apply RationalLaw.ext
  funext X
  by_cases h : fallback = X
  · subst X
    change (∑ bits : Fin 0 → Bool, if fallback = fallback then p.mass bits else 0) =
      (if fallback = fallback then (1 : ℚ) else 0)
    simpa only [ite_eq_left rfl, ite_true] using p.total
  · simp [mapLaw, pointLaw, h, Ne.symm h]

theorem singletonDraw_law (R : Fin (m + 1) → ℕ) (P : Fin (n + 1) → ℕ)
    (fallback : Table R P) (hs : m = 0 ∨ n = 0) :
    mapLaw (uniformLaw (α := Fin 0 → Bool)) (singletonDraw R P fallback) =
      LatticeCompletionAccuracy.originalUniform R P fallback := by
  letI : Nonempty (Table R P) := ⟨fallback⟩
  letI : Subsingleton (Table R P) := table_subsingleton_of_zero_tail R P hs
  rw [singletonDraw_pointLaw]
  change pointLaw fallback = uniformLaw
  exact pointLaw_eq_uniform fallback

/- Full empty row/column types are outside this Fin (tail+1) interface. They
remain the existing physical exact unit branch and require no empty minima.
The generic dense proofs above themselves allow m=0 or n=0, but the optional
singletonDraw avoids dense bits without changing the baseline branch policy. -/

end
end Math115.AdaptiveDenseCompletion
