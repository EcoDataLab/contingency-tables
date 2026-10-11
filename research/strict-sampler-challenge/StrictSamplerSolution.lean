/- SPDX-License-Identifier: Apache-2.0
Source-only strict challenge candidate. No compilation or Comparator result is
claimed for these new entrypoints. The imported theorem is the pinned, compiled
round-nine revised-sampler theorem; no original exact-sampling/counting result.
-/
import Math115.LatticeBoundedSampling

namespace Math115.StrictSampler
open OAI OAI.ContingencyTables
open FirstSuccess ResidualMixture
open scoped BigOperators Classical

/-- Original bounded-sampling quantifiers, with the public literal machine fixed. -/
def FixedMachineBoundedSamplingStatement : Prop :=
  ∃ (C d : ℕ), 0 < C ∧
    ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
      (∑ i, r i) = ∑ j, c j → ∀ k : ℕ, 1 ≤ k →
        let input := Algorithms.encodeSamplingInput r c k
        let t := C * (Algorithms.samplingSize n r k) ^ d
        (∀ bits : Fin t → Bool, ∃ X : Table r c,
          Algorithms.OutputsTable PublicLatticeSampler.machine input bits X.val) ∧
        (∑ X : Table r c,
          |Algorithms.tableMass PublicLatticeSampler.machine input t X.val -
            (Fintype.card (Table r c) : ℝ)⁻¹|) / 2 ≤ ((2 : ℝ) ^ k)⁻¹

/-- Direct alias of the actual revised-sampler theorem. -/
theorem boundedSampling : Algorithms.BoundedSamplingStatement :=
  Math115.LatticeBoundedSampling.boundedSampling

/-- The same proof construction, retaining its specific machine in the type. -/
theorem fixedMachineBoundedSampling : FixedMachineBoundedSamplingStatement := by
  obtain ⟨Ctime, Dtime, hC, hbound⟩ := PublicLatticeSampler.machineTime_public_bound
  refine ⟨Ctime, Dtime, hC, ?_⟩
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

end Math115.StrictSampler
