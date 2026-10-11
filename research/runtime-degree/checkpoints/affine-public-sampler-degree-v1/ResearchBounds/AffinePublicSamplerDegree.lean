/-
SPDX-License-Identifier: Apache-2.0
Source-only refinement of ResearchBounds.PublicSamplerDegree (2026-10-10).
Derived from that project's checked conditional public bridge and OpenAI's
pinned openai-math machine, codec and finite-word semantics. Imported machine
and compiled helpers are unchanged; only the conditional degree is refined.
-/
import ResearchBounds.AffineFiniteWordDegreeBounds
import ResearchBounds.PublicSamplerDegree

namespace Math115.AffinePublicSamplerDegree
open OAI OAI.ContingencyTables OAI.MatchingFPRAS
open FirstSuccess ResidualMixture
open scoped BigOperators Classical

def publicDegree (countDegree drawDegree : ℕ) : ℕ :=
  340 * max (max countDegree 6) drawDegree

/-- The preserved checked public formula remains available; the new
conditional exponent is no larger for any natural degree parameters. -/
lemma publicDegree_le_original (e t : ℕ) :
    publicDegree e t ≤ PublicSamplerDegree.publicDegree e t := by
  simp only [publicDegree, PublicSamplerDegree.publicDegree]
  calc
    _ ≤ 340 * (max 1 t * max e 6) := Nat.mul_le_mul_left 340
      (AffineFiniteWordDegree.completeOnlineDegree_le_original e t)
    _ = _ := by ring

/-- A single positive coefficient works uniformly over all dimensions,
equal-total margins and numeric precisions h >= 1, for the exact realizers. -/
theorem machineTime_public_degree {e t : ℕ}
    (hN : DegreeBounds.Typed PublicLatticeSampler.wordCountRealizer e)
    (hF : DegreeBounds.Typed PublicLatticeSampler.publicDrawRealizer t) :
    ∃ Ctime : ℕ, 0 < Ctime ∧
      ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
        (∑ i, r i = ∑ j, c j) → ∀ h : ℕ, 1 ≤ h →
          PublicLatticeSampler.machineTime (Algorithms.encodeSamplingInput r c h) ≤
            Ctime * (Algorithms.samplingSize n r h) ^ publicDegree e t := by
  obtain ⟨P, hdegree, hP⟩ := AffineFiniteWordDegree.machineTime_degree hN hF
  let A := CompletionPublicSize.wordMeasureCoefficient
  refine ⟨P.eval A + 1, by omega, ?_⟩
  intro m n r c htotal h hh
  have hs : 1 ≤ Algorithms.samplingSize n r h := by
    have hx := CompletionPublicSize.samplingSize_at_least_two (n := n) r h hh
    omega
  have hdegree' : 170 * P.natDegree ≤ publicDegree e t := by
    calc
      _ ≤ 170 * (2 * AffineFiniteWordDegree.completeOnlineDegree e t) :=
        Nat.mul_le_mul_left 170 hdegree
      _ = _ := by
        simp only [publicDegree, AffineFiniteWordDegree.completeOnlineDegree]
        ring
  calc
    _ ≤ P.eval (FiniteWordExecution.wordMeasure PublicLatticeSampler.wordCount
        (Algorithms.encodeSamplingInput r c h)) := hP _
    _ ≤ P.eval (A * (Algorithms.samplingSize n r h) ^ 170) :=
      OAI.MatchingFPRAS.TreeTyped.polynomial_eval_monotone P
        (PublicLatticeSampler.public_wordMeasure_bound r c htotal h hh)
    _ ≤ P.eval A * (Algorithms.samplingSize n r h) ^ (170 * P.natDegree) :=
      ProfilePrograms.polynomial_scaled_power P A (Algorithms.samplingSize n r h) 170 hs
    _ ≤ (P.eval A + 1) * (Algorithms.samplingSize n r h) ^ publicDegree e t :=
      Nat.mul_le_mul (Nat.le_succ _) (Nat.pow_le_pow_right hs hdegree')

/-- Same exact fixed machine, Algorithms input/output codec, every-tape
table output and total-variation bound. The count/draw degrees stay explicit
hypotheses. Empty dimensions are covered by the imported machine theorems. -/
theorem fixedMachineBoundedSampling_with_degree {e t : ℕ}
    (hN : DegreeBounds.Typed PublicLatticeSampler.wordCountRealizer e)
    (hF : DegreeBounds.Typed PublicLatticeSampler.publicDrawRealizer t) :
    ∃ Ctime : ℕ, 0 < Ctime ∧
      ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
        (∑ i, r i) = ∑ j, c j → ∀ h : ℕ, 1 ≤ h →
          let input := Algorithms.encodeSamplingInput r c h
          let time := Ctime * (Algorithms.samplingSize n r h) ^ publicDegree e t
          (∀ bits : Fin time → Bool, ∃ X : Table r c,
            Algorithms.OutputsTable PublicLatticeSampler.machine input bits X.val) ∧
          (∑ X : Table r c,
            |Algorithms.tableMass PublicLatticeSampler.machine input time X.val -
              (Fintype.card (Table r c) : ℝ)⁻¹|) / 2 ≤ ((2 : ℝ) ^ h)⁻¹ := by
  obtain ⟨Ctime, hC, hbound⟩ := machineTime_public_degree hN hF
  refine ⟨Ctime, hC, ?_⟩
  intro m n r c htotal h hh
  dsimp only
  have ht := hbound m n r c htotal h hh
  refine ⟨PublicLatticeSampler.machine_outputs r c htotal h _ ht, ?_⟩
  letI := OAI.ContingencyTables.table_nonempty r c htotal
  have hv := PublicLatticeSampler.tableDraw_variation r c htotal h
  simp_rw [PublicLatticeSampler.machine_mass r c htotal h _ ht]
  simpa only [variation, Rat.cast_div, Rat.cast_sum, Rat.cast_abs, Rat.cast_sub,
    Rat.cast_ofNat, Rat.cast_inv, uniformLaw, uniformMass, Rat.cast_one, Rat.cast_natCast,
    one_div, CompletionRetryBudget.dyadic, Rat.cast_pow] using hv

end Math115.AffinePublicSamplerDegree
