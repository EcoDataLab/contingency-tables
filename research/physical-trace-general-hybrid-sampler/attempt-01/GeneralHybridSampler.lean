/-
SPDX-License-Identifier: Apache-2.0
A total typed finite-word sampler: stronger trace in the reduced reference
branch, zero-bit deterministic output, and the checked legacy backend on
the remaining shapes. Each backend uses its own proved scales. This is not
an encoded hybrid machine and carries no new charged-time claim.
-/
import ResearchPhysicalTraceJoin.GeneralCompleteReference
import ResearchPhysicalTraceJoin.GeneralLegacyFallback

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open FirstSuccess ResidualMixture CompletionCounts
open Math115.CompletionRetryBudget
open scoped BigOperators Classical
noncomputable section
variable (xs ys : List ℕ)

/-- The reserved width and map are chosen together, without padding an
inapplicable backend. The classifier is computed from the positive lists. -/
def hybridSampler
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) (t : ℕ) :
    (q : ℕ) × ((Fin q → Bool) → Table (listMargin xs) (listMargin ys)) :=
  if hd : positiveTraceBranch xs ys = .deterministic then
    ⟨0, positiveDeterministicWord xs ys htotal⟩
  else if hb : positiveTraceBranch xs ys = .reference then
    ⟨positiveReferenceWordWidth xs ys t, positiveReferenceWord xs ys htotal hb t⟩
  else
    ⟨positiveLegacyWordWidth xs ys t, positiveLegacyWord xs ys htotal t⟩

def hybridWordLaw
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) (t : ℕ) :
    RationalLaw (Table (listMargin xs) (listMargin ys)) :=
  mapLaw (uniformLaw (α := Fin (hybridSampler xs ys htotal t).1 → Bool))
    (hybridSampler xs ys htotal t).2

/-- The complete dispatcher actually uses the new reference word at every
input whose recomputed classifier returns reference. -/
theorem hybridSampler_reference
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hb : positiveTraceBranch xs ys = .reference) (t : ℕ) :
    hybridSampler xs ys htotal t =
      ⟨positiveReferenceWordWidth xs ys t, positiveReferenceWord xs ys htotal hb t⟩ := by
  have hd : ¬ positiveTraceBranch xs ys = .deterministic := by rw [hb]; decide
  simp only [hybridSampler, dif_neg hd, dif_pos hb]

theorem hybridSampler_deterministic
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hd : positiveTraceBranch xs ys = .deterministic) (t : ℕ) :
    hybridSampler xs ys htotal t = ⟨0, positiveDeterministicWord xs ys htotal⟩ := by
  simp only [hybridSampler, dif_pos hd]

theorem hybridSampler_legacy
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (hd : positiveTraceBranch xs ys ≠ .deterministic)
    (hb : positiveTraceBranch xs ys ≠ .reference) (t : ℕ) :
    hybridSampler xs ys htotal t =
      ⟨positiveLegacyWordWidth xs ys t, positiveLegacyWord xs ys htotal t⟩ := by
  simp only [hybridSampler, dif_neg hd, dif_neg hb]

/-- Uniform fair bits give the requested dyadic error for every equal-total
natural margin pair, including zeros, empty lists and all computed branches. -/
theorem hybridWord_accuracy
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) (t : ℕ) :
    letI := table_nonempty (listMargin xs) (listMargin ys) htotal
    (variation (hybridWordLaw xs ys htotal t)
      (uniformLaw (α := Table (listMargin xs) (listMargin ys))) : ℝ) ≤
        (dyadic t : ℝ) := by
  letI := table_nonempty (listMargin xs) (listMargin ys) htotal
  by_cases hd : positiveTraceBranch xs ys = .deterministic
  · unfold hybridWordLaw
    rw [hybridSampler_deterministic xs ys htotal hd]
    rw [positiveDeterministicWord_law xs ys htotal hd]
    simp only [variation_self, Rat.cast_zero]
    exact_mod_cast (dyadic_positive t).le
  by_cases hb : positiveTraceBranch xs ys = .reference
  · unfold hybridWordLaw
    rw [hybridSampler_reference xs ys htotal hb]
    exact_mod_cast positiveReferenceWord_accuracy xs ys htotal hb t
  · unfold hybridWordLaw
    rw [hybridSampler_legacy xs ys htotal hd hb]
    exact positiveLegacyWord_accuracy xs ys htotal t

/-- Feasibility holds pointwise, not only with high probability. -/
theorem hybridWord_feasible
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) (t : ℕ)
    (bits : Fin (hybridSampler xs ys htotal t).1 → Bool) :
    HasMargins ((hybridSampler xs ys htotal t).2 bits).val (listMargin xs) (listMargin ys) :=
  ((hybridSampler xs ys htotal t).2 bits).property

end
end Math115.PhysicalTraceJoin
