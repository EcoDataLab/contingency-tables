import Research.PhysicalDefectTraceFinal
import Research.AggregateCorrectionCap
import Research.UniformContextVariance

set_option maxHeartbeats 800000

namespace Math115.AggregateDefectTrace
open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts SmallContextCoordinates SmallContextFibres
open SmallGraphProfiles FiniteExposureVariance
open Math115.ReducedSmallChain Math115.RetainedChainSquare
open Math115.PhysicalDefectTrace Math115.RetainedContextVariance
open Research.UniformContextVariance Research.ResidualSelectedBudget

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

/-- The actual original-margin aggregate budget, including all small lines. -/
def aggregateK0 (r : I → ℕ) (c : J → ℕ) (U : ℕ) : ℝ :=
  (((smallLineCount r U+smallLineCount c U)*U^2+
    Fintype.card (Cells (firstPaperSmall r c U))*U:ℕ):ℝ)

def aggregateCT (r : I → ℕ) (c : J → ℕ) (U : ℕ) : ℝ :=
  (U:ℝ)*((U:ℝ)-1)+4*aggregateK0 r c U

lemma aggregateK0_nonnegative (r : I → ℕ) (c : J → ℕ) (U : ℕ) :
    0 ≤ aggregateK0 r c U := Nat.cast_nonneg _

lemma aggregateCT_at_least_six (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (hU : 2 ≤ U) (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U))) :
    6 ≤ aggregateCT r c U := by
  have hkN : 4 ≤ (smallLineCount r U+smallLineCount c U)*U^2+
      Fintype.card (Cells (firstPaperSmall r c U))*U := by
    have hh := Nat.mul_le_mul hp hU
    omega
  have hk : 4 ≤ aggregateK0 r c U := by unfold aggregateK0; exact_mod_cast hkN
  have hUR : (2:ℝ) ≤ U := by exact_mod_cast hU
  unfold aggregateCT
  nlinarith

/-- The complete actual same-box cap, with genuine source capacity premises
proved internally, is supplied to the uniform-context integration theorem. -/
theorem uniformCorrectionCap_aggregate (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :
    UniformCorrectionCap r c U L (capacity r c U L) (2*aggregateK0 r c U) := by
  intro s hs σ hσ n e l hl0 hlU
  have hcap := paper_residual_capacity r c (dimensionAllowance (I:=I) (J:=J)) L U dimension_le_allowance
  have hh := Math115.AggregateCorrectionCap.physical_correction_le_aggregate_adjacent
    r c U L (capacity r c U L) s hs σ l hl0 hlU (capacity_small r c U L) hσ e hcap
  simpa only [correction,hl0,hlU,and_self,ite_true,boxedWeight,contextWeight,childMass,aggregateK0] using hh

/-- Actual full-state variance is derived from the aggregate cap, original
finite exposure owners and the existing full repair law. No variance premise. -/
theorem state_variance_aggregate (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hU : 2 ≤ U) (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (H : States r c U L → ℝ) :
    variance (weight r c U L) H ≤ (2*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^2*aggregateCT r c U)*
        graphEnergy r c U L H := by
  exact state_variance_of_uniform_correction_cap r c U L hU hp
    (2*aggregateK0 r c U) (mul_nonneg (by norm_num) (aggregateK0_nonnegative r c U))
    (uniformCorrectionCap_aggregate r c U L) (aggregateCT r c U)
    (aggregateCT_at_least_six r c U hU hp) (by unfold aggregateCT; ring_nf; exact le_rfl) H

/-- A generic physical interface parameterized by Cfull. The concrete aggregate
headline below discharges this interface; it is not a new variance assumption. -/
theorem rationalPhysicalTrace_of_full_variance (r : I → ℕ) (c : J → ℕ) (U L Q : ℕ)
    [Nonempty (DefectVertices r c U L)] (hL : 7 ≤ L) (hQ : 1 ≤ Q)
    (hdegree : ∀ d : DefectVertices r c U L,
      (Finset.univ.filter (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) d.val)).card ≤ Q)
    (Cfull : ℝ) (hC : 0 ≤ Cfull)
    (hfull : ∀ H : States r c U L → ℝ,variance (weight r c U L) H ≤ Cfull*graphEnergy r c U L H)
    (g : DefectVertices r c U L → ℝ) :
    (rationalPhysicalTrace r c U L Q hQ hdegree).variance g ≤ (4*(Q:ℝ)*Cfull)*(rationalPhysicalTrace r c U L Q hQ hdegree).energy g := by
  apply Research.WeightedHarmonicTrace.rational_poincare_transfer
    (balancedWeight r c U L) (defectWeight r c U L)
    (fun b => (weight_positive r c U L b.val).le) (fun d => weight_positive r c U L d.val)
    (ddConductance r c U L) (crossConductance r c U L)
    (fun d e => acceptedConductance_nonnegative r c U L d.val e.val)
    (fun d e => acceptedConductance_symmetric r c U L d.val e.val)
    (fun b d => acceptedConductance_nonnegative r c U L b.val d.val)
    Q hQ (accepted_defect_row_of_degree r c U L Q hdegree) (splitMinimum r c U L) Cfull hC
  · intro F
    rw [split_variance_identity,split_energy_identity]
    exact hfull _
  · exact split_half_accepted r c U L hL

/-- The unchanged actual rational trace, in both reference and unit branches,
has the aggregate full-variance coefficient with all analytic premises proved. -/
theorem actualRationalTrace_poincare_aggregate (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    [Nonempty (DefectVertices r c U L)] (hU : 2 ≤ U) (hL : 7 ≤ L)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U))) (g : DefectVertices r c U L → ℝ) :
    (actualRationalTrace r c U L hp).variance g ≤ (32*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^3*aggregateCT r c U)*
        (actualRationalTrace r c U L hp).energy g := by
  let p := Fintype.card (Cells (firstPaperSmall r c U))
  have hv := rationalPhysicalTrace_of_full_variance r c U L (defectAllowance r c U) hL
    (defectAllowance_positive r c U hp) (actual_defect_degree r c U L)
    (2*(p:ℝ)^2*aggregateCT r c U)
    (mul_nonneg (by positivity) (by have := aggregateCT_at_least_six r c U hU hp; linarith))
    (state_variance_aggregate r c U L hU hp) g
  have hQ : (defectAllowance r c U:ℝ) ≤ 4*(p:ℝ) := by
    have hh : defectAllowance r c U ≤ 4*p := Nat.sub_le _ _
    exact_mod_cast hh
  have hc : 4*(defectAllowance r c U:ℝ)*(2*(p:ℝ)^2*aggregateCT r c U) ≤ 32*(p:ℝ)^3*aggregateCT r c U := by
    calc
      _ ≤ 4*(4*(p:ℝ))*(2*(p:ℝ)^2*aggregateCT r c U) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hQ (by norm_num : (0:ℝ) ≤ 4))
          (mul_nonneg (by positivity) (by have := aggregateCT_at_least_six r c U hU hp; linarith))
      _ = _ := by ring
  exact hv.trans (mul_le_mul_of_nonneg_right hc (FiniteChain.energy_nonneg _ g))

end
end Math115.AggregateDefectTrace
