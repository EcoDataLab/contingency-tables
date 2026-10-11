/-
SPDX-License-Identifier: Apache-2.0
Pointwise code identities for the separate-precision reference trial and
bounded restarted outer program. These connect encoded output to the actual
finite Boolean experiment, retaining all inner and outer fallback events.
-/
import Math115.LatticeOuterProgram
import Math115.LatticeSamplerPreparation

namespace Math115.LatticeOuterSemantics

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles CompletionCounts
open ReducedSmallChain PhysicalCompletionOracle FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => IdealOracleScales.cutoff (I := Fin m) (J := Fin n)
local notation "L" => IdealOracleScales.padding (I := Fin m) (J := Fin n)
local notation "e" => PhysicalComputedProposal.computedCellEquiv r c U
local notation "s" => Nat.clog 2 (32 * d^2)
local notation "f" => PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r
variable (hr : 0 < (largeIndices (IdealOracleScales.cutoff (I := Fin m) (J := Fin n), List.ofFn r)).length)
variable (hc : 0 < (largeIndices (IdealOracleScales.cutoff (I := Fin m) (J := Fin n), List.ofFn c)).length)

lemma completionWidth_positive (h : ℕ) : 0 < f h := by
  unfold PhysicalLatticeCompletion.reservedCompletionBits PhysicalLatticeCompletion.reservedFineBits
    CompletionRetryBudget.retries
  positivity

/-- Every completed terminal trial returns precisely the code of the ordinary
table accepted by the physical balance/padding test, or the same rejection. -/
theorem profileTrial_ofFn (htotal : ∑ i, r i = ∑ j, c j)
    (initial x : States r c U L) (T hStep hTerminal : ℕ)
    (bits : Fin T → Fin (PhysicalReferenceBoolean.stepBits (n := n) r hStep) → Bool)
    (terminal : Fin (f hTerminal) → Bool) :
    LatticeOuterProgram.profileTrial
      (((LatticeProfileWalk.encodedConfiguration r c hStep initial x,
        List.ofFn (fun i => (List.ofFn (splitWordEquiv s (f hStep) (bits i)).1,
          List.ofFn (splitWordEquiv s (f hStep) (bits i)).2))), hTerminal), List.ofFn terminal) =
      (PhysicalStationaryLaw.stateTrial r c U L
        ⟨wordWalk (PhysicalReferenceBoolean.bitStep r c hr hc hStep) x T bits,
          ListedLatticeCompletion.completionDraw r c hr hc _ hTerminal terminal⟩).map
        (fun X => matrixCode X.val) := by
  let z := wordWalk (PhysicalReferenceBoolean.bitStep r c hr hc hStep) x T bits
  unfold LatticeOuterProgram.profileTrial LatticeOuterProgram.trialOutputInput
    LatticeOuterProgram.trialCompletion LatticeOuterProgram.trialParameters LatticeOuterProgram.trialState
  rw [LatticeProfileWalk.profileWalk_ofFn r c hr hc htotal,
    LatticeProfileWalk.currentParameters_encoded]
  change outerTrial ((PhysicalComputedProposal.stateCodeData r c U L e z, L),
    CompletionSamplerProgram.draw
      (residualParameters ((PhysicalComputedProposal.stateCodeData r c U L e z, L), (d, hTerminal)),
        List.ofFn terminal)) = _
  rw [LatticeProfileStep.residualParameters_code r c hr hc hTerminal z,
    ListedLatticeCompletion.programTable_code r c hr hc z hTerminal terminal,
    ← LatticeProfileStep.listedDraw_output r c hr hc hTerminal z terminal]
  exact LatticeSamplerPreparation.outerTrial_reference_code r c hr hc z
    (ListedLatticeCompletion.completionDraw r c hr hc z hTerminal terminal)

/-- Literal encoded parameters for the actual computed reference pair. -/
def parameters (x : States r c U L) (T hStep hTerminal : ℕ) :
    LatticeOuterProgram.TrialParameters :=
  ((LatticeProfileWalk.encodedConfiguration r c hStep x x, ((T, s), f hStep)),
    (hTerminal, f hTerminal))

lemma attemptWidth_parameters (x : States r c U L) (T hStep hTerminal : ℕ) :
    LatticeOuterProgram.attemptWidth (parameters r c x T hStep hTerminal) =
      PhysicalReferenceBoolean.attemptBits (n := n) r T hStep hTerminal := rfl

theorem packedTrial_code (htotal : ∑ i, r i = ∑ j, c j)
    (x : States r c U L) (T hStep hTerminal : ℕ)
    (bits : Fin (PhysicalReferenceBoolean.attemptBits (n := n) r T hStep hTerminal) → Bool) :
    LatticeOuterProgram.packedTrial (parameters r c x T hStep hTerminal, List.ofFn bits) =
      (PhysicalStationaryLaw.stateTrial r c U L
        (PhysicalReferenceBoolean.jointDraw r c hr hc x T hStep hTerminal bits)).map
        (fun X => matrixCode X.val) := by
  have hf := completionWidth_positive (n := n) r hStep
  unfold LatticeOuterProgram.packedTrial LatticeOuterProgram.prepareTrial parameters
  dsimp only [LatticeOuterProgram.trialWordInput]
  rw [LatticeOuterProgram.walkWords_ofFn (by omega), LatticeOuterProgram.terminalWord_ofFn]
  exact profileTrial_ofFn r c hr hc htotal x x T hStep hTerminal _ _

/-- Each attempt restarts from x; unused supplied bits cannot add attempts.
The original feasible fallback is returned exactly on total outer rejection. -/
theorem retry_code (htotal : ∑ i, r i = ∑ j, c j)
    (x : States r c U L) (fallback : Table r c) (T R hStep hTerminal : ℕ)
    (bits : Fin (PhysicalReferenceBoolean.outerBits (n := n) r T R hStep hTerminal) → Bool) :
    LatticeOuterProgram.retry
      (((parameters r c x T hStep hTerminal, matrixCode fallback.val), R), List.ofFn bits) =
      matrixCode (PhysicalReferenceBoolean.outerDraw r c hr hc x fallback T R hStep hTerminal bits).val := by
  have hw : 0 < LatticeOuterProgram.attemptWidth (parameters r c x T hStep hTerminal) := by
    have hf := completionWidth_positive (n := n) r hTerminal
    change 0 < T * (s + f hStep) + f hTerminal
    omega
  rw [LatticeOuterProgram.retry_ofFn _ _ R hw bits]
  have he : (fun word : Fin (PhysicalReferenceBoolean.attemptBits (n := n) r T hStep hTerminal) → Bool =>
      LatticeOuterProgram.packedTrial (parameters r c x T hStep hTerminal, List.ofFn word)) =
      (fun word => (PhysicalStationaryLaw.stateTrial r c U L
        (PhysicalReferenceBoolean.jointDraw r c hr hc x T hStep hTerminal word)).map
          (fun X => matrixCode X.val)) := by
    funext word
    exact packedTrial_code r c hr hc htotal x T hStep hTerminal word
  rw [he, FirstSuccessProgram.wordRetry_map]
  rfl

/-- The supplied initial configuration and fallback are replaced by actual
dimension-recursive preparation from the original margin lists. -/
theorem initialized_retry_code (htotal : ∑ i, r i = ∑ j, c j)
    (T R hStep hTerminal : ℕ)
    (bits : Fin (PhysicalReferenceBoolean.outerBits (n := n) r T R hStep hTerminal) → Bool) :
    LatticeOuterProgram.retry
      (((((LatticeSamplerPreparation.initialConfiguration ((List.ofFn r, List.ofFn c), hStep),
          ((T, s), f hStep)), (hTerminal, f hTerminal)),
        LatticeSamplerPreparation.initialFallback (List.ofFn r, List.ofFn c)), R), List.ofFn bits) =
      matrixCode (PhysicalReferenceBoolean.initializedDraw r c hr hc htotal T R hStep hTerminal bits).val := by
  rw [LatticeSamplerPreparation.initialConfiguration_code r c htotal,
    LatticeSamplerPreparation.initialFallback_code r c htotal]
  exact retry_code r c hr hc htotal
    (PhysicalFiniteWalk.initialState r c U L (GreedyFeasibleTable.table r c htotal))
    (GreedyFeasibleTable.table r c htotal) T R hStep hTerminal bits

end
end Math115.LatticeOuterSemantics
