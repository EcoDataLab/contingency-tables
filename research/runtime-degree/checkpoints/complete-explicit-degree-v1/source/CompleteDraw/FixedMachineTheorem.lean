/- Explicit-degree theorem for the same existing compiled d17 public machine.
The final binding imports an exact numerical reference packed-trial certificate;
no runtime-degree premise remains in the theorem below. -/
import CompleteDraw.FinalBinding
namespace Math115.CompleteDrawNext
open OAI OAI.ContingencyTables
open scoped BigOperators Classical
noncomputable section

/-- A fixed literal-natural expression; it is independent of dimensions,
margins and precision. The reference constant is fixed in FinalBinding. -/
def explicitPublicDegree : ℕ := publicDegree referenceTrialDegree

/-- One positive coefficient bounds the same fixed compiled public machine's
running time, uniformly over the original margins and precision domain. -/
theorem machineTime_public_explicit_degree :
    ∃ C : ℕ, 0 < C ∧
      ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
        (∑ i, r i) = ∑ j, c j → ∀ h : ℕ, 1 ≤ h →
          Math115.PublicLatticeSampler.machineTime (Algorithms.encodeSamplingInput r c h) ≤
            C * (Algorithms.samplingSize n r h) ^ explicitPublicDegree :=
  machineTime_public_of_reference typed_actual_referencePackedTrial

/-- Same fixed compiled public machine and Algorithms codecs. One positive
coefficient is uniform over all equal-total margins and every precision h≥1;
all tapes produce feasible tables and the resulting law has TV error≤2⁻ʰ. -/
theorem fixedMachineBoundedSampling_explicit_degree :
    ∃ C : ℕ, 0 < C ∧
      ∀ (m n : ℕ) (r : Fin m → ℕ) (c : Fin n → ℕ),
        (∑ i, r i) = ∑ j, c j → ∀ h : ℕ, 1 ≤ h →
          let input := Algorithms.encodeSamplingInput r c h
          let time := C * (Algorithms.samplingSize n r h) ^ explicitPublicDegree
          (∀ bits : Fin time → Bool, ∃ X : Table r c,
            Algorithms.OutputsTable Math115.PublicLatticeSampler.machine input bits X.val) ∧
          (∑ X : Table r c,
            |Algorithms.tableMass Math115.PublicLatticeSampler.machine input time X.val -
              (Fintype.card (Table r c) : ℝ)⁻¹|) / 2 ≤ ((2 : ℝ) ^ h)⁻¹ :=
  fixedMachineBoundedSampling_of_reference typed_actual_referencePackedTrial

end
end Math115.CompleteDrawNext
