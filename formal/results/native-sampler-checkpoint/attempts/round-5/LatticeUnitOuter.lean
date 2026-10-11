/-
SPDX-License-Identifier: Apache-2.0
The missing-reference branch uses the same reserved bank and restarted outer
parser as the reference branch. Completion segments are ignored; actual unit
neighbor moves and the exact terminal two-view reconstruction are retained.
-/
import Math115.LatticeOuterSemantics
import Math115.LatticeUnitWalk
import Math115.LatticeEmptyOutput

namespace Math115.LatticeUnitOuter

open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped
open ProfilePrograms DensePrograms

def trialState (z : LatticeOuterProgram.PackedTrial) : ProfileConfiguration :=
  LatticeUnitWalk.unitWalk (z.1.1.1, profileWalkChunks (LatticeOuterProgram.trialWordInput z))

def trialStateRealizer : Realizer trialState :=
  composition (pair (composition (composition first first) first)
    (composition LatticeOuterProgram.trialWordInputRealizer profileWalkChunksRealizer))
    LatticeUnitWalk.unitWalkRealizer

theorem polynomial_trialState : PolynomialTime trialStateRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_first)
    (polynomial_composition LatticeOuterProgram.polynomial_trialWordInput polynomial_profileWalkChunks))
    LatticeUnitWalk.polynomial_unitWalk

def packedTrial (z : LatticeOuterProgram.PackedTrial) : Option MatrixCode :=
  outerTrial ((currentParameters (trialState z)).1, [])

def packedTrialRealizer : Realizer packedTrial :=
  composition (pair (composition (composition trialStateRealizer currentParametersRealizer) first)
    (constant ([] : MatrixCode))) outerTrialRealizer

theorem polynomial_packedTrial : PolynomialTime packedTrialRealizer :=
  polynomial_composition (polynomial_pair (polynomial_composition
    (polynomial_composition polynomial_trialState polynomial_currentParameters) polynomial_first)
    (polynomial_constant ([] : MatrixCode))) polynomial_outerTrial

def retry (z : LatticeOuterProgram.RetryData) : MatrixCode :=
  FirstSuccessProgram.retry packedTrial (z.1.1, LatticeOuterProgram.retryWords z)

def retryRealizer : Realizer retry :=
  composition (pair (composition first first) LatticeOuterProgram.retryWordsRealizer)
    (FirstSuccessProgram.retryRealizer packedTrialRealizer)

theorem polynomial_retry : PolynomialTime retryRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_first) LatticeOuterProgram.polynomial_retryWords)
    (FirstSuccessProgram.polynomial_retry polynomial_packedTrial)

open OAI.CommonBasesFPRAS SmallGraphProfiles CompletionCounts ReducedSmallChain
open PhysicalCompletionOracle FirstSuccess FairBits GridBoundary
open scoped BigOperators Classical
noncomputable section

lemma walkChunks_ofFn {T s f g : ℕ} (hw : 0 < s + f)
    (bits : Fin (T * (s + f) + g) → Bool) :
    profileWalkChunks (((T, s), f), List.ofFn bits) =
      List.ofFn (fun i : Fin T => List.ofFn
        (gridWordEquiv T (s + f) (splitWordEquiv (T * (s + f)) g bits).1 i)) := by
  unfold profileWalkChunks
  dsimp only [profileWordWidth, profileWalkWidth]
  rw [ofFn_split_take]
  exact wordChunks_ofFn hw _

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => IdealOracleScales.cutoff (I := Fin m) (J := Fin n)
local notation "L" => IdealOracleScales.padding (I := Fin m) (J := Fin n)
local notation "s" => Nat.clog 2 (32 * d^2)
local notation "f" => PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r

theorem packedTrial_code (htotal : ∑ i, r i = ∑ j, c j)
    (h : ¬ PhysicalBooleanSampler.bothLarge r c) (x : States r c U L)
    (T hStep hTerminal : ℕ)
    (bits : Fin (PhysicalReferenceBoolean.attemptBits (n := n) r T hStep hTerminal) → Bool) :
    packedTrial (LatticeOuterSemantics.parameters r c x T hStep hTerminal, List.ofFn bits) =
      (PhysicalStationaryLaw.stateTrial r c U L
        (PhysicalBooleanSampler.unitJointDraw r c h x T hStep hTerminal bits)).map
        (fun X => matrixCode X.val) := by
  have hf := LatticeOuterSemantics.completionWidth_positive (n := n) r hStep
  unfold packedTrial trialState LatticeOuterSemantics.parameters
  dsimp only [LatticeOuterProgram.trialWordInput]
  rw [walkChunks_ofFn (by omega), LatticeUnitWalk.unitWalk_ofFn r c htotal,
    LatticeProfileWalk.currentParameters_encoded]
  exact LatticeEmptyOutput.outerTrial_empty_code r c h _

theorem retry_code (htotal : ∑ i, r i = ∑ j, c j)
    (h : ¬ PhysicalBooleanSampler.bothLarge r c) (x : States r c U L)
    (fallback : Table r c) (T R hStep hTerminal : ℕ)
    (bits : Fin (PhysicalReferenceBoolean.outerBits (n := n) r T R hStep hTerminal) → Bool) :
    retry (((LatticeOuterSemantics.parameters r c x T hStep hTerminal,
      matrixCode fallback.val), R), List.ofFn bits) =
      matrixCode (PhysicalBooleanSampler.unitOuterDraw r c h x fallback T R hStep hTerminal bits).val := by
  have hw : 0 < LatticeOuterProgram.attemptWidth
      (LatticeOuterSemantics.parameters r c x T hStep hTerminal) := by
    have hf := LatticeOuterSemantics.completionWidth_positive (n := n) r hTerminal
    change 0 < T * (s + f hStep) + f hTerminal
    omega
  unfold retry
  rw [LatticeOuterProgram.retryWords_ofFn _ _ R hw bits, FirstSuccessProgram.retry_ofFn]
  have he : (fun word : Fin (PhysicalReferenceBoolean.attemptBits (n := n) r T hStep hTerminal) → Bool =>
      packedTrial (LatticeOuterSemantics.parameters r c x T hStep hTerminal, List.ofFn word)) =
      (fun word => (PhysicalStationaryLaw.stateTrial r c U L
        (PhysicalBooleanSampler.unitJointDraw r c h x T hStep hTerminal word)).map
          (fun X => matrixCode X.val)) := by
    funext word
    exact packedTrial_code r c htotal h x T hStep hTerminal word
  rw [he, FirstSuccessProgram.wordRetry_map]
  rfl

theorem initialized_retry_code (htotal : ∑ i, r i = ∑ j, c j)
    (h : ¬ PhysicalBooleanSampler.bothLarge r c) (T R hStep hTerminal : ℕ)
    (bits : Fin (PhysicalReferenceBoolean.outerBits (n := n) r T R hStep hTerminal) → Bool) :
    retry (((((LatticeSamplerPreparation.initialConfiguration ((List.ofFn r, List.ofFn c), hStep),
      ((T, s), f hStep)), (hTerminal, f hTerminal)),
      LatticeSamplerPreparation.initialFallback (List.ofFn r, List.ofFn c)), R), List.ofFn bits) =
      matrixCode (PhysicalBooleanSampler.unitOuterDraw r c h
        (PhysicalFiniteWalk.initialState r c U L (GreedyFeasibleTable.table r c htotal))
        (GreedyFeasibleTable.table r c htotal) T R hStep hTerminal bits).val := by
  rw [LatticeSamplerPreparation.initialConfiguration_code r c htotal,
    LatticeSamplerPreparation.initialFallback_code r c htotal]
  exact retry_code r c htotal h
    (PhysicalFiniteWalk.initialState r c U L (GreedyFeasibleTable.table r c htotal))
    (GreedyFeasibleTable.table r c htotal) T R hStep hTerminal bits

end
end Math115.LatticeUnitOuter
