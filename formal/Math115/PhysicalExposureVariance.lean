/-
SPDX-License-Identifier: Apache-2.0
Connects the unchanged physical word-prefix decomposition to localized
adjacent contrasts and the sharper path inequality.
-/
import Math115.PhysicalLeafEnergy
import Math115.PathVariance
import OAI.Combinatorics.ContingencyTables.Transport.WordContextVariance

namespace Math115.PhysicalExposureVariance

open OAI.ContingencyTables
open scoped BigOperators Classical
open SmallContextCoordinates SmallContextEnumeration SmallContextFibres
open PhysicalCompletionFibres LargePairEnumeration BalancedFamily BalancedBox
open ExcessContextProfiles SmallGraphProfiles FiniteExposureVariance IntegerWeightedTransport
open FirstPaperContextTransport FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open RowMajorEnumeration
open Math115.PhysicalLeafEnergy Math115.PathVariance

universe u

/-- Exact exposure telescoping, retaining the sum of the individual prefix
budgets rather than replacing each depth by one common bound. -/
theorem variance_eq_sum_prefixContribution {A : Type*} [Fintype A] {q : ℕ}
    (w H : (Fin q → A) → ℝ) (hw : ∀ a, 0 ≤ w a) :
    variance w H = ∑ k : Fin q, prefixContribution w H k := by
  have hacc : ∀ k (hk : k ≤ q), variance w H = prefixVariance w H k hk +
      ∑ j : Fin k, prefixContribution w H ⟨j.val, lt_of_lt_of_le j.isLt hk⟩ := by
    intro k
    induction k with
    | zero =>
      intro hk
      rw [prefixVariance_zero]
      simp
    | succ k ih =>
      intro hk
      have hkl : k < q := by omega
      have hp := ih (Nat.le_of_lt hkl)
      rw [prefixVariance_step w H hw ⟨k, hkl⟩] at hp
      rw [Fin.sum_univ_castSucc]
      change variance w H = prefixVariance w H (k + 1) hk +
        ((∑ j : Fin k, prefixContribution w H ⟨j.val, lt_trans j.isLt hkl⟩) +
          prefixContribution w H ⟨k, hkl⟩)
      have hp' : variance w H =
          (prefixVariance w H (k + 1) hk + prefixContribution w H ⟨k, hkl⟩) +
            ∑ j : Fin k, prefixContribution w H ⟨j.val, lt_trans j.isLt hkl⟩ := hp
      linarith
  have h := hacc q le_rfl
  rw [prefixVariance_final w H hw, zero_add] at h
  exact h

variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

noncomputable def canonicalContextWeight (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) (s : Cells small)
    (τ : Earlier small s.val → Fin (U + 1)) :
    (LocalCoordinates U (Fintype.card (Later small s.val)) → ℕ) → ℝ :=
  contextHard small B r c L _ (contextEquiv small s.val s.property
    (suffixEnumeration small s.val) U)
    (prefixRaw small s.val (prefixExtension small s.val U τ) U)

noncomputable def canonicalChildMass (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) (s : Cells small)
    (τ : Earlier small s.val → Fin (U + 1)) (j : ℕ) : ℝ :=
  eliminate (widths (fun _ : Fin (Fintype.card (Later small s.val)) => U))
    (canonicalContextWeight small B r c L U s τ) (childProfile U j)

noncomputable def canonicalChildMean (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) (s : Cells small)
    (τ : Earlier small s.val → Fin (U + 1)) (H : SmallProfile small → ℝ) (j : ℕ) : ℝ :=
  eliminate (widths (fun _ : Fin (Fintype.card (Later small s.val)) => U))
    (fun p => canonicalContextWeight small B r c L U s τ p *
      H (assemble small s.val s.property (prefixExtension small s.val U τ) U
        (suffixEnumeration small s.val) p)) (childProfile U j) /
    canonicalChildMass small B r c L U s τ j

lemma ownerContrast_eq_canonical (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) (s : Cells small)
    (τ : Earlier small s.val → Fin (U + 1)) (H : SmallProfile small → ℝ) (j : Fin U) :
    ownerContrast small B r c L U ⟨s, j, τ⟩ H =
      min (canonicalChildMass small B r c L U s τ j.val)
        (canonicalChildMass small B r c L U s τ (j.val + 1)) *
      (canonicalChildMean small B r c L U s τ H j.val -
        canonicalChildMean small B r c L U s τ H (j.val + 1))^2 := rfl

/-- The actual hard child weights satisfy the sharper path variance bound,
with the sum of all their localized adjacent contrasts retained. -/
theorem canonical_context_variance_le_contrasts
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) (hU : 2 ≤ U)
    (hlarge : ∀ i j, small i j = false → 2 ≤ B i j)
    (s : Cells small) (τ : Earlier small s.val → Fin (U + 1))
    (H : SmallProfile small → ℝ) :
    variance (fun j : Fin (U + 1) => canonicalChildMass small B r c L U s τ j.val)
      (fun j => canonicalChildMean small B r c L U s τ H j.val) ≤
      ((U : ℝ) * ((U : ℝ) + 1) / 2) *
        ∑ j : Fin U, ownerContrast small B r c L U ⟨s, j, τ⟩ H := by
  have hp := weighted_path_variance_bound
    (canonicalChildMass small B r c L U s τ)
    (canonicalChildMean small B r c L U s τ H) U
    (fun j _ => eliminate_nonnegative _ _ (contextHard_nonnegative small B r c L _ _ _) _)
    (fun a j b haj hjb hbU => context_child_minimum small B r c L _
      (contextEquiv small s.val s.property (suffixEnumeration small s.val) U)
      (prefixRaw small s.val (prefixExtension small s.val U τ) U) (fun _ => U) U
      (prefixRaw_inBox small s.val _ U (prefixExtension_bounded small s.val U τ))
      hlarge (fun w hw => by rw [widths_constant_mem U w hw]; exact hU)
      a j b haj hjb hbU)
  unfold pathEnergy at hp
  rw [← Fin.sum_univ_eq_sum_range] at hp
  simpa only [← ownerContrast_eq_canonical] using hp

/-- Zeroth and first moments are independent of the chosen suffix
enumeration. Here the canonical enumeration is connected to actual words. -/
theorem canonical_eliminate_eq_word_fibre (small : I → J → Bool) (B : I → J → ℕ)
    (U : ℕ) (hB : ∀ i j, small i j = true → B i j = U)
    (k : Fin (Fintype.card (Cells small))) (τ : Fin k.val → Fin (U + 1))
    (j : Fin (U + 1)) (F : SmallProfile small → ℝ) :
    let s := enumeration small k
    let σ := prefixExtension small s.val U (earlierWordChoices small U k τ)
    eliminate (widths (fun _ : Fin (Fintype.card (Later small s.val)) => U))
      (fun p => F (assemble small s.val s.property σ U (suffixEnumeration small s.val) p))
      (childProfile U j.val) =
      ∑ a, fibreWeight (fibreWeight (fun a => F (rawChoice small U (wordChoices small U a)))
        (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j a := by
  dsimp only
  rw [eliminate_context_eq_choice_fibre small B _ _ U hB]
  exact (word_fibre_sum small U k τ j (fun x => F (rawChoice small U x))).symm

theorem word_context_variance_le_ownerContrasts
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) (hU : 2 ≤ U)
    (hB : ∀ i j, small i j = true → B i j = U)
    (hlarge : ∀ i j, small i j = false → 2 ≤ B i j)
    (k : Fin (Fintype.card (Cells small))) (τ : Fin k.val → Fin (U + 1))
    (H : SmallProfile small → ℝ) :
    let w := wordWeight small B r c L U
    let G := wordObservable small U H
    let cw := fun j : Fin (U + 1) => fibreWeight
      (fibreWeight w (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j
    variance (fun j => ∑ a, cw j a) (fun j => mean (cw j) G) ≤
      ((U : ℝ) * ((U : ℝ) + 1) / 2) *
        ∑ j : Fin U, ownerContrast small B r c L U
          ⟨enumeration small k, j, earlierWordChoices small U k τ⟩ H := by
  dsimp only
  let s := enumeration small k
  let η := earlierWordChoices small U k τ
  let cw := fun j : Fin (U + 1) => fibreWeight
    (fibreWeight (wordWeight small B r c L U)
      (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j
  have hz (j : Fin (U + 1)) : (∑ a, cw j a) =
      canonicalChildMass small B r c L U s η j.val :=
    (canonical_eliminate_eq_word_fibre small B U hB k τ j (hardMarginal small B r c L)).symm
  have hm (j : Fin (U + 1)) : (∑ a, cw j a * wordObservable small U H a) =
      eliminate (widths (fun _ : Fin (Fintype.card (Later small s.val)) => U))
        (fun p => canonicalContextWeight small B r c L U s η p *
          H (assemble small s.val s.property (prefixExtension small s.val U η) U
            (suffixEnumeration small s.val) p)) (childProfile U j.val) := by
    have h := canonical_eliminate_eq_word_fibre small B U hB k τ j
      (fun x => hardMarginal small B r c L x * H x)
    calc
      _ = ∑ a, fibreWeight (fibreWeight
          (fun a => wordWeight small B r c L U a * wordObservable small U H a)
          (restriction k.val (Nat.le_of_lt k.isLt)) τ) (fun a => a k) j a := by
        apply Finset.sum_congr rfl
        intro a _
        exact (double_fibreWeight_mul _ _ _ _ _ _ a).symm
      _ = _ := h.symm
  have hμ (j : Fin (U + 1)) : mean (cw j) (wordObservable small U H) =
      canonicalChildMean small B r c L U s η H j.val := by
    unfold mean canonicalChildMean
    rw [hm, hz]
  change variance (fun j => ∑ a, cw j a) (fun j => mean (cw j) (wordObservable small U H)) ≤ _
  simp_rw [hz, hμ]
  exact canonical_context_variance_le_contrasts small B r c L U hU hlarge s η H

theorem prefixContribution_le_ownerContrasts
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) (hU : 2 ≤ U)
    (hB : ∀ i j, small i j = true → B i j = U)
    (hlarge : ∀ i j, small i j = false → 2 ≤ B i j)
    (k : Fin (Fintype.card (Cells small))) (H : SmallProfile small → ℝ) :
    prefixContribution (wordWeight small B r c L U) (wordObservable small U H) k ≤
      ((U : ℝ) * ((U : ℝ) + 1) / 2) *
        ∑ τ : Earlier small (enumeration small k).val → Fin (U + 1),
          ∑ j : Fin U, ownerContrast small B r c L U ⟨enumeration small k, j, τ⟩ H := by
  let E := fun τ : Earlier small (enumeration small k).val → Fin (U + 1) =>
    ∑ j : Fin U, ownerContrast small B r c L U ⟨enumeration small k, j, τ⟩ H
  have hsum : (∑ τ : Fin k.val → Fin (U + 1), E (earlierWordChoices small U k τ)) =
      ∑ τ, E τ := by
    apply Fintype.sum_equiv (earlierWordChoices small U k)
    intro τ
    rfl
  calc
    _ ≤ ∑ τ : Fin k.val → Fin (U + 1),
        ((U : ℝ) * ((U : ℝ) + 1) / 2) * E (earlierWordChoices small U k τ) := by
      unfold prefixContribution partitionContribution
      apply Finset.sum_le_sum
      intro τ _
      exact word_context_variance_le_ownerContrasts small B r c L U hU hB hlarge k τ H
    _ = _ := by rw [← Finset.mul_sum, hsum]

/-- Exact prefix telescoping and reindexing charge every canonical owner
once, including zero-weight word fibres. -/
theorem variance_le_sum_ownerContrasts
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) (hU : 2 ≤ U)
    (hB : ∀ i j, small i j = true → B i j = U)
    (hlarge : ∀ i j, small i j = false → 2 ≤ B i j)
    (H : SmallProfile small → ℝ) :
    variance (wordWeight small B r c L U) (wordObservable small U H) ≤
      ((U : ℝ) * ((U : ℝ) + 1) / 2) *
        ∑ o : Owner small U, ownerContrast small B r c L U o H := by
  have hw (a : Fin (Fintype.card (Cells small)) → Fin (U + 1)) :
      0 ≤ wordWeight small B r c L U a := hardMarginal_nonnegative small B r c L _
  rw [variance_eq_sum_prefixContribution (wordWeight small B r c L U)
    (wordObservable small U H) hw]
  calc
    _ ≤ ∑ k : Fin (Fintype.card (Cells small)), ((U : ℝ) * ((U : ℝ) + 1) / 2) *
        ∑ τ : Earlier small (enumeration small k).val → Fin (U + 1),
          ∑ j : Fin U, ownerContrast small B r c L U ⟨enumeration small k, j, τ⟩ H :=
      Finset.sum_le_sum (fun k _ => prefixContribution_le_ownerContrasts small B r c L U hU hB hlarge k H)
    _ = ((U : ℝ) * ((U : ℝ) + 1) / 2) *
        ∑ s : Cells small, ∑ τ : Earlier small s.val → Fin (U + 1),
          ∑ j : Fin U, ownerContrast small B r c L U ⟨s, j, τ⟩ H := by
      rw [← Finset.mul_sum]
      congr 1
      exact (enumeration small).sum_comp
        (fun s => ∑ τ : Earlier small s.val → Fin (U + 1),
          ∑ j : Fin U, ownerContrast small B r c L U ⟨s, j, τ⟩ H)
    _ = _ := by
      congr 1
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro s _
      rw [Fintype.sum_prod_type, Finset.sum_comm]

/-- Localized transversal Poincare inequality for the actual physical
completion-weighted words. The source capacities and residual-table bound
are explicit; no depth or adjacent-level multiplicity is added. -/
theorem physical_transversal_variance_localized
    (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L U : ℕ) (hU : 2 ≤ U)
    (hB : ∀ i j, small i j = true → B i j = U)
    (hlarge : ∀ i j, small i j = false → 2 ≤ B i j)
    (hcap : ∀ T : ResidualTables small r c
      (fun i => r i + rowLargeCount small i * L) (fun j => c j + columnLargeCount small j * L),
      ∀ i j, T.val.val i j ≤ B i j)
    (H : SmallProfile small → ℝ) :
    variance (wordWeight small B r c L U) (wordObservable small U H) ≤
      (((U : ℝ) * ((U : ℝ) + 1) / 2) *
        (2 + ((Fintype.card (Cells small) - 1 : ℕ) : ℝ) * ((U : ℝ) + 1)^2 / 2)) *
        physicalEnergy small B (hardMarginal small B r c L) H := by
  have h := mul_le_mul_of_nonneg_left
    (sum_ownerContrast_le_physicalEnergy small B r c L U hU hB hlarge hcap H)
    (show 0 ≤ (U : ℝ) * ((U : ℝ) + 1) / 2 by positivity)
  exact (variance_le_sum_ownerContrasts small B r c L U hU hB hlarge H).trans
    (by simpa only [mul_assoc] using h)

end Math115.PhysicalExposureVariance
