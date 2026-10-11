/-
SPDX-License-Identifier: Apache-2.0
Source-only proposed instantiation of the original bounded-sampling statement
for the NEW computed ideal-scale public machine. No exact sampler or counting
extension is supplied. Independent review and compilation remain necessary.
-/
import Math115.PublicLatticeSampler

namespace Math115.LatticeBoundedSampling
open OAI OAI.ContingencyTables OAI.MatchingFPRAS
open FirstSuccess ResidualMixture
open scoped BigOperators Classical

noncomputable section

/-- A fixed public RandomMachine, every-tape bounded halting/feasibility, and
normalized TV at the same fixed execution time. No explicit complete runtime
degree is claimed: it is the physical compiler witness's degree. -/
theorem boundedSampling : Algorithms.BoundedSamplingStatement := by
  obtain ⟨Ctime, Dtime, hC, hbound⟩ := PublicLatticeSampler.machineTime_public_bound
  refine ⟨PublicLatticeSampler.machine, Ctime, Dtime, hC, ?_⟩
  intro m n r c htotal h hh
  dsimp only
  have ht := hbound m n r c htotal h hh
  refine ⟨PublicLatticeSampler.machine_outputs r c htotal h _ ht, ?_⟩
  letI := OAI.ContingencyTables.table_nonempty r c htotal
  have hv := PublicLatticeSampler.tableDraw_variation r c htotal h
  dsimp only at hv
  simp_rw [PublicLatticeSampler.machine_mass r c htotal h _ ht]
  simpa only [variation, Rat.cast_div, Rat.cast_sum, Rat.cast_abs, Rat.cast_sub,
    Rat.cast_ofNat, Rat.cast_inv, uniformLaw, uniformMass, Rat.cast_one, Rat.cast_natCast,
    one_div, CompletionRetryBudget.dyadic, Rat.cast_pow] using hv

end
end Math115.LatticeBoundedSampling
