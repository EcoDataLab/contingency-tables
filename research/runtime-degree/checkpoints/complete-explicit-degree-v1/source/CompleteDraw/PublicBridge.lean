import CompleteDraw.Seams
import ResearchBounds.AffinePublicSamplerDegree
namespace Math115.CompleteDrawNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped
open FirstSuccess ResidualMixture
open scoped BigOperators Classical
noncomputable section

/-- The affine public-machine bridge with the closed degree-1008 count field. -/
def publicDegree (referenceDegree : ℕ) : ℕ := 340*max 1008 (drawDegree referenceDegree)

lemma publicDegree_eq_affine (r : ℕ) :
    publicDegree r = Math115.AffinePublicSamplerDegree.publicDegree 1008 (drawDegree r) := by
  simp [publicDegree,Math115.AffinePublicSamplerDegree.publicDegree]

/-- Full machine-time conclusion with exactly one visible reference-field seam. -/
theorem machineTime_public_of_reference {r : ℕ}
    (hReference : Math115.DegreeBounds.Typed Math115.LatticeOuterProgram.packedTrialRealizer r) :
    ∃ Ctime : ℕ, 0 < Ctime ∧ ∀ (m n : ℕ) (rows : Fin m→ℕ) (cols : Fin n→ℕ),
      (∑ i, rows i = ∑ j, cols j) → ∀ h : ℕ, 1 ≤ h →
        Math115.PublicLatticeSampler.machineTime (Algorithms.encodeSamplingInput rows cols h) ≤
          Ctime*(Algorithms.samplingSize n rows h)^publicDegree r := by
  exact Math115.AffinePublicSamplerDegree.machineTime_public_degree
      Math115.TightCountDegreeV2.typed_complete_wordCount_1008 (typed_publicDraw_of_reference hReference)

/-- Exact unchanged public machine, Algorithms codec, every supplied tape,
empty dimensions and total-variation conclusion, with one explicit seam. -/
theorem fixedMachineBoundedSampling_of_reference {r : ℕ}
    (hReference : Math115.DegreeBounds.Typed Math115.LatticeOuterProgram.packedTrialRealizer r) :
    ∃ Ctime : ℕ, 0 < Ctime ∧ ∀ (m n : ℕ) (rows : Fin m→ℕ) (cols : Fin n→ℕ),
      (∑ i, rows i) = ∑ j, cols j → ∀ h : ℕ, 1 ≤ h →
        let input := Algorithms.encodeSamplingInput rows cols h
        let time := Ctime*(Algorithms.samplingSize n rows h)^publicDegree r
        (∀ bits : Fin time→Bool, ∃ X : Table rows cols,
          Algorithms.OutputsTable Math115.PublicLatticeSampler.machine input bits X.val) ∧
        (∑ X : Table rows cols,
          |Algorithms.tableMass Math115.PublicLatticeSampler.machine input time X.val -
            (Fintype.card (Table rows cols) : ℝ)⁻¹|)/2 ≤ ((2:ℝ)^h)⁻¹ := by
  exact Math115.AffinePublicSamplerDegree.fixedMachineBoundedSampling_with_degree
      Math115.TightCountDegreeV2.typed_complete_wordCount_1008 (typed_publicDraw_of_reference hReference)

end
end Math115.CompleteDrawNext
