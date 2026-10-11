/-
SPDX-License-Identifier: Apache-2.0
Conditional degree of the fixed public lattice sampler. The complete count
and draw certificates are explicit hypotheses, not supplied numerical results.
-/
import ResearchBounds.FiniteWordDegreeBounds
import Math115.PublicLatticeSampler

namespace Math115.PublicSamplerDegree
open OAI OAI.ContingencyTables OAI.MatchingFPRAS
open FirstSuccess ResidualMixture
open scoped BigOperators Classical

/-- Physical execution degree in the original public sampling size, conditional
on certificates for the exact count and supplied-word draw realizers. -/
def publicDegree (countDegree drawDegree : ℕ) : ℕ :=
  340 * max 1 drawDegree * max countDegree 6

theorem machineTime_public_degree {e t : ℕ}
    (hN : DegreeBounds.Typed PublicLatticeSampler.wordCountRealizer e)
    (hF : DegreeBounds.Typed PublicLatticeSampler.publicDrawRealizer t) :
    ∃ Ctime : ℕ, 0 < Ctime ∧
      ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
        (∑ i, r i = ∑ j, c j) → ∀ h : ℕ, 1 ≤ h →
          PublicLatticeSampler.machineTime (Algorithms.encodeSamplingInput r c h) ≤
            Ctime * (Algorithms.samplingSize n r h) ^ publicDegree e t := by
  obtain ⟨P, hdegree, hP⟩ := DegreeBounds.machineTime_degree hN hF
  let A := CompletionPublicSize.wordMeasureCoefficient
  refine ⟨P.eval A + 1, by omega, ?_⟩
  intro m n r c htotal h hh
  have hs : 1 ≤ Algorithms.samplingSize n r h := by
    have hx := CompletionPublicSize.samplingSize_at_least_two (n := n) r h hh
    omega
  have hdegree' : 170 * P.natDegree ≤ publicDegree e t := by
    calc
      _ ≤ 170 * (2 * DegreeBounds.completeOnlineDegree e t) :=
        Nat.mul_le_mul_left 170 hdegree
      _ = _ := by simp only [publicDegree, DegreeBounds.completeOnlineDegree]; ring
  calc
    _ ≤ P.eval (FiniteWordExecution.wordMeasure PublicLatticeSampler.wordCount
        (Algorithms.encodeSamplingInput r c h)) := hP _
    _ ≤ P.eval (A * (Algorithms.samplingSize n r h) ^ 170) :=
      polynomial_eval_monotone P
        (PublicLatticeSampler.public_wordMeasure_bound r c htotal h hh)
    _ ≤ P.eval A * (Algorithms.samplingSize n r h) ^ (170 * P.natDegree) :=
      ProfilePrograms.polynomial_scaled_power P A (Algorithms.samplingSize n r h) 170 hs
    _ ≤ (P.eval A + 1) * (Algorithms.samplingSize n r h) ^ publicDegree e t :=
      Nat.mul_le_mul (Nat.le_succ _) (Nat.pow_le_pow_right hs hdegree')

/-- Exact public output and uniform-law statement at the explicit conditional
degree. The machine, encoding, precision convention and both program branches
are the existing compiled ones. Only the two realizer-degree hypotheses remain. -/
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

end Math115.PublicSamplerDegree
