/-
SPDX-License-Identifier: Apache-2.0
One public contract for the complete ordinary list-and-bit program.
The explicit computed width, pointwise feasible output and uniform-word
accuracy are tied to rawHybridSamplerCode. No encoded machine or charged
runtime bound is asserted.
-/
import ResearchPhysicalTraceJoin.GeneralProgramCode

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open DensePrograms FirstSuccess ResidualMixture CompletionCounts
open Math115.CompletionRetryBudget
open scoped BigOperators Classical
noncomputable section

/-- Every equal-total input, including zero margins and empty lists, has
exactly the computed reserved width. On every word the ordinary program
outputs a feasible table; uniform fair words have total variation at most
`2^-t` from uniform tables. The witness is the checked hybrid sampler,
which uses the stronger trace on its recomputed reference branch. -/
theorem executableSampler_contract (xs ys : List ℕ) (hs : xs.sum = ys.sum) (t : ℕ) :
    let htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j := by
      simpa only [← List.sum_ofFn, ofFn_listMargin] using hs
    letI := table_nonempty (listMargin xs) (listMargin ys) htotal
    ∃ (q : ℕ) (sample : (Fin q → Bool) → Table (listMargin xs) (listMargin ys)),
      q = rawHybridWordWidth xs ys t ∧
      (∀ word, rawHybridSamplerCode xs ys t (List.ofFn word) =
        matrixCode (sample word).val) ∧
      (variation (mapLaw (uniformLaw (α := Fin q → Bool)) sample)
        (uniformLaw (α := Table (listMargin xs) (listMargin ys))) : ℝ) ≤
          (dyadic t : ℝ) := by
  dsimp only
  let htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j := by
    simpa only [← List.sum_ofFn, ofFn_listMargin] using hs
  letI := table_nonempty (listMargin xs) (listMargin ys) htotal
  refine ⟨(hybridSampler xs ys htotal t).1, (hybridSampler xs ys htotal t).2,
    (rawHybridWordWidth_eq xs ys htotal t).symm, ?_, ?_⟩
  · exact rawHybridSamplerCode_eq xs ys htotal t
  · exact hybridWord_accuracy xs ys htotal t

end
end Math115.PhysicalTraceJoin
