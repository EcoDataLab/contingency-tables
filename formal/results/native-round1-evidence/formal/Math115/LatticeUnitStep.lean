/-
SPDX-License-Identifier: Apache-2.0
The missing-reference branch uses the actual computed neighbor proposal and
keeps the current stored views only for an unused proposal code. The common
completion suffix remains reserved but is ignored. These are total list
programs with polynomial realizers; no outer machine-time exponent is claimed.
-/
import Math115.LatticeProfileStep
import Math115.PhysicalBooleanSampler

namespace Math115.LatticeUnitStep

open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped
open ProfilePrograms DensePrograms

/-- The proposal candidate, including the exact current-view default. No
completion or translation test is needed when a reference pair is missing. -/
def unitStep (z : ProfileStepInput) : List ℕ × List ℕ := stepCandidateViews z

def unitStepRealizer : Realizer unitStep := stepCandidateViewsRealizer

theorem polynomial_unitStep : PolynomialTime unitStepRealizer :=
  polynomial_stepCandidateViews

/-- The prefix width is computed from the supplied dimension allowance. -/
def proposalWidth (d : ℕ) : ℕ := Nat.clog 2 (32 * d^2)

def proposalWidthRealizer : Realizer proposalWidth :=
  (composition (composition (pair (constant 32) squareNat) multiply)
    ceilLogTwoRealizer).congr (by
      intro d
      simp only [Function.comp_apply]
      congr 1 <;> ring)

theorem polynomial_proposalWidth : PolynomialTime proposalWidthRealizer :=
  polynomial_congr _ (polynomial_composition
    (polynomial_composition (polynomial_pair (polynomial_constant 32) polynomial_squareNat)
      polynomial_multiply) polynomial_ceilLogTwo)

abbrev UnitWordInput := ResidualParameters × List Bool

def wordDimension : Realizer (fun z : UnitWordInput => z.1.2.1) :=
  composition (composition first second) first

theorem polynomial_wordDimension : PolynomialTime wordDimension :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_second)
    polynomial_first

/-- Surplus bits belong to the ignored completion reservation. Short malformed
words are still total inputs; correctness uses an actual reserved word below. -/
def proposalPrefix (z : UnitWordInput) : List Bool :=
  z.2.take (proposalWidth z.1.2.1)

def proposalPrefixRealizer : Realizer proposalPrefix :=
  composition (pair second (composition wordDimension proposalWidthRealizer)) takeFast

theorem polynomial_proposalPrefix : PolynomialTime proposalPrefixRealizer :=
  polynomial_composition (polynomial_pair polynomial_second
    (polynomial_composition polynomial_wordDimension polynomial_proposalWidth)) polynomial_takeFast

def unitWordInput (z : UnitWordInput) : ProfileStepInput :=
  (z.1, (proposalPrefix z, []))

def unitWordInputRealizer : Realizer unitWordInput :=
  pair first (pair proposalPrefixRealizer (constant ([] : List Bool)))

theorem polynomial_unitWordInput : PolynomialTime unitWordInputRealizer :=
  polynomial_pair polynomial_first
    (polynomial_pair polynomial_proposalPrefix (polynomial_constant ([] : List Bool)))

/-- An executable step on the same flat reserved word as the reference branch. -/
def unitWordStep (z : UnitWordInput) : List ℕ × List ℕ := unitStep (unitWordInput z)

def unitWordStepRealizer : Realizer unitWordStep :=
  composition unitWordInputRealizer unitStepRealizer

theorem polynomial_unitWordStep : PolynomialTime unitWordStepRealizer :=
  polynomial_composition polynomial_unitWordInput polynomial_unitStep

/-- Completion words cannot influence this branch's output. -/
theorem unitStep_completion_irrelevant (p : ResidualParameters)
    (proposal completion₁ completion₂ : List Bool) :
    unitStep (p, (proposal, completion₁)) = unitStep (p, (proposal, completion₂)) := rfl

open SmallGraphProfiles SmallContextCoordinates CompletionCounts ReducedSmallChain
open PhysicalComputedProposal PhysicalCompletionOracle FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
-- Keep the computed catalogue and physical decoder opaque during conversions.
-- Explicit unfolding below exposes only the unit-step wrapper when needed.
attribute [local irreducible] PhysicalComputedProposal.stateCode
  PhysicalComputedProposal.computedProposal codeNeighborProposal
  PhysicalBooleanSampler.unitBitStep
variable {m n : ℕ}
variable (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => IdealOracleScales.cutoff (I := Fin m) (J := Fin n)
local notation "L" => IdealOracleScales.padding (I := Fin m) (J := Fin n)
local notation "e" => computedCellEquiv r c U
local notation "s" => Nat.clog 2 (32 * d^2)

/-- The same parameters and literal computed catalogue as the reference step. -/
def encodedParameters (h : ℕ) (x : States r c U L) : ResidualParameters :=
  ((PhysicalComputedProposal.stateCodeData r c U L e x, L), (d, h))

theorem encodedParameters_profileStepInput (h : ℕ) (x : States r c U L)
    (proposal : Fin s → Bool)
    (completion : Fin (PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r h) → Bool) :
    (encodedParameters r c h x, (List.ofFn proposal, List.ofFn completion)) =
      LatticeProfileStep.encodedStepInput r c h x proposal completion := rfl

/-- Every proposal code is interpreted by the actual free-scale physical
decoder. Successful neighbor codes move the state; unused codes keep x. -/
theorem unitStep_encoded (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (x : States r c U L) (proposal : Fin s → Bool) (completion : List Bool) :
    unitStep (encodedParameters r c h x, (List.ofFn proposal, completion)) =
      PhysicalComputedProposal.computedStateCode r c U L
        ((PhysicalComputedProposal.computedProposal r c U L x proposal).getD x) := by
  unfold unitStep stepCandidateViews stepProposal
  change (codeNeighborProposal (PhysicalComputedProposal.stateCodeData r c U L e x,
    List.ofFn proposal)).getD (PhysicalComputedProposal.computedStateCode r c U L x) = _
  rw [LatticeProfileStep.codeProposal_encoded r c htotal x proposal]
  cases PhysicalComputedProposal.computedProposal r c U L x proposal <;> rfl

theorem unitStep_unused_code (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (x : States r c U L) (proposal : Fin s → Bool) (completion : List Bool)
    (hp : PhysicalComputedProposal.computedProposal r c U L x proposal = none) :
    unitStep (encodedParameters r c h x, (List.ofFn proposal, completion)) =
      PhysicalComputedProposal.computedStateCode r c U L x := by
  rw [unitStep_encoded r c htotal h x, hp]
  rfl

theorem unitStep_neighbor_code (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (x y : States r c U L) (proposal : Fin s → Bool) (completion : List Bool)
    (hp : PhysicalComputedProposal.computedProposal r c U L x proposal = some y) :
    unitStep (encodedParameters r c h x, (List.ofFn proposal, completion)) =
      PhysicalComputedProposal.computedStateCode r c U L y := by
  rw [unitStep_encoded r c htotal h x, hp]
  rfl

private lemma ofFn_take_prefix {k N : ℕ} (hk : k ≤ N) (bits : Fin N → Bool) :
    (List.ofFn bits).take k = List.ofFn (prefixWord hk bits) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_ofFn, min_eq_left hk]
  · intro i hi hj
    simp only [List.getElem_take, List.getElem_ofFn, prefixWord, Fin.castLE]

/-- Prefix extraction agrees exactly with the physical Boolean step, for
every reserved word and every state, without an assumption about reference
existence. The outer dispatcher chooses this branch when references are absent. -/
theorem unitWordStep_unitBitStep (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (x : States r c U L)
    (bits : Fin (PhysicalReferenceBoolean.stepBits (n := n) r h) → Bool) :
    unitWordStep (encodedParameters r c h x, List.ofFn bits) =
      PhysicalComputedProposal.computedStateCode r c U L
        (PhysicalBooleanSampler.unitBitStep r c h x bits) := by
  have hs : s ≤ PhysicalReferenceBoolean.stepBits (n := n) r h := Nat.le_add_right _ _
  unfold unitWordStep unitWordInput proposalPrefix
  change unitStep (encodedParameters r c h x, ((List.ofFn bits).take s, [])) = _
  rw [ofFn_take_prefix hs, unitStep_encoded r c htotal h x]
  simp only [PhysicalBooleanSampler.unitBitStep]

end
end Math115.LatticeUnitStep
