/- SPDX-License-Identifier: Apache-2.0
Separate revised-sampler challenge. The two sorry bodies are statement-side
holes only; neither is permitted in the solution's dependency closure.
-/
import Math115.PublicLatticeSampler

namespace Math115.StrictSampler
open OAI OAI.ContingencyTables
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

/-- Exactly the original existential public statement, selected on its own. -/
theorem boundedSampling : Algorithms.BoundedSamplingStatement := by sorry

/-- Additional explicit attribution to this same closed, finite fair-bit machine. -/
theorem fixedMachineBoundedSampling : FixedMachineBoundedSamplingStatement := by sorry

end Math115.StrictSampler
