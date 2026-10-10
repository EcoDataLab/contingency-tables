/-
SPDX-License-Identifier: Apache-2.0
Generic and ideal empty-block final output semantics.
Only the balance test converts the retained RowColumnPair into Table r c.
No unit walk/retry implementation or outer machine-cost theorem is added.
-/
import Math115.LatticeSamplerPreparation

namespace Math115.LatticeEmptyOutput

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles CompletionCounts PaddedCompletions
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open SmallContextCoordinates SmallContextFibres ReducedSmallChain PhysicalStationarySuccess
open scoped BigOperators Classical
noncomputable section

section FreeOutput
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (V W : ℕ)
local notation "small" => firstPaperSmall r c V
local notation "B" => capacity r c V W
local notation "e₀" => PhysicalComputedProposal.computedCellEquiv r c V

def outputData (z : States r c V W) : OuterTableData :=
  ProfilePrograms.outputData ((PhysicalComputedProposal.stateCodeData r c V W e₀ z, W), [])

lemma outputEntry (hempty : IsEmpty (LargeRows r V) ∨ IsEmpty (LargeColumns c V))
    (z : States r c V W) (i : Fin m) (j : Fin n) :
    ProfilePrograms.outputEntry (outputData r c V W z, (i.val, j.val)) =
      (PhysicalEmptyCompletion.emptyCompletion r c V W hempty z).val.val.1 i j := by
  have hs := PhysicalEmptyCompletion.allSmall_of_empty r c V hempty
  have he := outputEntry_small small e₀ (physicalProfile small B r c W z)
    (largeIndices (V, List.ofFn r)) (largeIndices (V, List.ofFn c)) V W [] i j (hs i j)
  exact he.trans (by
    simpa only [smallView, hs i j, dite_eq_left] using
      ((PhysicalEmptyCompletion.emptyCompletion r c V W hempty z).property.2.2.1 i j (hs i j)).1.symm)

lemma outputSuccess (hempty : IsEmpty (LargeRows r V) ∨ IsEmpty (LargeColumns c V))
    (z : States r c V W) :
    outerSuccess (outputData r c V W z) = true ↔
      PhysicalStationarySuccess.StateJointSuccess r c V W
        ⟨z, PhysicalEmptyCompletion.emptyCompletion r c V W hempty z⟩ := by
  have hs := PhysicalEmptyCompletion.allSmall_of_empty r c V hempty
  change (balancedTest (PhysicalComputedProposal.computedStateCode r c V W z, V) &&
    paddingTest (W, [])) = true ↔ _
  simp only [paddingTest, List.all_nil, Bool.and_true]
  rw [LatticeSamplerPreparation.balancedTest_stateCode r c V W z]
  constructor
  · intro hb
    refine ⟨hb, ?_⟩
    intro i j hij
    rw [hs i j] at hij
    contradiction
  · exact And.left

lemma outputMatrix (hempty : IsEmpty (LargeRows r V) ∨ IsEmpty (LargeColumns c V))
    (z : States r c V W)
    (hx : PhysicalStationarySuccess.StateJointSuccess r c V W
      ⟨z, PhysicalEmptyCompletion.emptyCompletion r c V W hempty z⟩) :
    ProfilePrograms.outputMatrix
      (prepareOutput ((PhysicalComputedProposal.stateCodeData r c V W e₀ z, W), [])) =
        matrixCode ((PhysicalStationarySuccess.originalStateSuccessEquiv r c V W).symm
          ⟨⟨z, PhysicalEmptyCompletion.emptyCompletion r c V W hempty z⟩, hx⟩).val := by
  have hs := PhysicalEmptyCompletion.allSmall_of_empty r c V hempty
  change ProfilePrograms.outputMatrix ((List.ofFn r, List.ofFn c), outputData r c V W z) = _
  rw [outputMatrix_code]
  apply congrArg matrixCode
  funext i j
  rw [outputEntry r c V W hempty z, LatticeSamplerPreparation.successful_entry]
  simp only [PhysicalStationarySuccess.large, largePadding, Finset.mem_filter,
    Finset.mem_univ, true_and, hs i j, Bool.true_eq_false, ite_false, Nat.sub_zero]

/-- Exact unit-branch output trial at free physical scales. Padding is
vacuous, while the stored-view balance test remains mandatory. -/
theorem outerTrial_empty_free_code
    (hempty : IsEmpty (LargeRows r V) ∨ IsEmpty (LargeColumns c V)) (z : States r c V W) :
    outerTrial ((PhysicalComputedProposal.stateCodeData r c V W e₀ z, W), []) =
      (PhysicalStationaryLaw.stateTrial r c V W
        ⟨z, PhysicalEmptyCompletion.emptyCompletion r c V W hempty z⟩).map
          (fun T => matrixCode T.val) := by
  by_cases h : PhysicalStationarySuccess.StateJointSuccess r c V W
    ⟨z, PhysicalEmptyCompletion.emptyCompletion r c V W hempty z⟩
  · have hp := (outputSuccess r c V W hempty z).mpr h
    calc
      _ = some (ProfilePrograms.outputMatrix
          (prepareOutput ((PhysicalComputedProposal.stateCodeData r c V W e₀ z, W), []))) := ite_eq_left hp
      _ = some (matrixCode ((PhysicalStationarySuccess.originalStateSuccessEquiv r c V W).symm
          ⟨⟨z, PhysicalEmptyCompletion.emptyCompletion r c V W hempty z⟩, h⟩).val) :=
        congrArg some (outputMatrix r c V W hempty z h)
      _ = _ := by
        simp only [PhysicalStationaryLaw.stateTrial, FirstSuccess.partialEquivDraw,
          dite_eq_left h, Option.map_some]
  · have hp : outerSuccess (outputData r c V W z) ≠ true :=
      fun hp => h ((outputSuccess r c V W hempty z).mp hp)
    calc
      _ = none := ite_eq_right hp
      _ = _ := by
        simp only [PhysicalStationaryLaw.stateTrial, FirstSuccess.partialEquivDraw,
          dite_eq_right h, Option.map_none]

end FreeOutput

section IdealOutput
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "U" => IdealOracleScales.cutoff (I := Fin m) (J := Fin n)
local notation "L" => IdealOracleScales.padding (I := Fin m) (J := Fin n)
local notation "e₀" => PhysicalComputedProposal.computedCellEquiv r c U

/-- The actual ideal-scale unit selector's terminal output seam. -/
theorem outerTrial_empty_code (h : ¬ PhysicalBooleanSampler.bothLarge r c) (z : States r c U L) :
    outerTrial ((PhysicalComputedProposal.stateCodeData r c U L e₀ z, L), []) =
      (PhysicalStationaryLaw.stateTrial r c U L
        ⟨z, PhysicalEmptyCompletion.emptyCompletionOfNotBoth r c U L
          (PhysicalBooleanSampler.not_bothLarge_reference r c h) z⟩).map
            (fun T => matrixCode T.val) :=
  outerTrial_empty_free_code r c U L
    (PhysicalEmptyCompletion.empty_of_not_both r c U
      (PhysicalBooleanSampler.not_bothLarge_reference r c h)) z

end IdealOutput
end
end Math115.LatticeEmptyOutput
