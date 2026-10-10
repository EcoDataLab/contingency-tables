/-
SPDX-License-Identifier: Apache-2.0
Bounded encoded unit-branch walk on the same reserved flat step words as the
reference walk. The actual neighbor proposal changes valid physical states;
completion suffixes are ignored. Terminal and outer retry programs are separate.
-/
import Math115.LatticeUnitStep
import Math115.LatticeProfileWalk

namespace Math115.LatticeUnitWalk

open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped
open ProfilePrograms Polynomial

def boundedNext (z : ProfileConfiguration × (List Bool)) : List ℕ × List ℕ :=
  capViews (z.1.1.1.1, LatticeUnitStep.unitWordStep (currentParameters z.1, z.2))

def boundedNextRealizer : Realizer boundedNext := by
  let check : Realizer (fun z : ProfileConfiguration × (List Bool) => z.1.1.1.1) :=
    composition (composition (composition first first) first) first
  let input : Realizer (fun z : ProfileConfiguration × (List Bool) => (currentParameters z.1, z.2)) :=
    pair (composition first currentParametersRealizer) second
  exact composition (pair check (composition input LatticeUnitStep.unitWordStepRealizer)) capViewsRealizer

theorem polynomial_boundedNext : PolynomialTime boundedNextRealizer := by
  unfold boundedNextRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_currentParameters) polynomial_second)
      LatticeUnitStep.polynomial_unitWordStep)) polynomial_capViews

def advanceUnit (z : (List Bool) × ProfileConfiguration) : ProfileConfiguration :=
  (z.2.1, boundedNext (z.2, z.1))

def advanceUnitRealizer : Realizer advanceUnit :=
  pair (composition second first) (composition
    (f := fun z : (List Bool) × ProfileConfiguration => (z.2, z.1)) (g := boundedNext)
    (pair second first) boundedNextRealizer)

theorem polynomial_advanceUnit : PolynomialTime advanceUnitRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_boundedNext)

/-- The cap guard bounds either returned view regardless of the supplied
words or the uncapped step's output. Immutable metadata determines q and U. -/
lemma advanceUnit_weight (word : (List Bool)) (z : ProfileConfiguration) (S : ℕ)
    (hz : weight z.1 ≤ S) : weight (advanceUnit (word, z)) ≤ 20 * (S + 1)^3 := by
  let q := z.1.1.1.1.1.1.length
  let U := z.1.1.1.2
  have hq : q ≤ S := (list_length_le_weight _).trans ((weight_fst z.1.1.1.1.1).trans
    ((weight_fst z.1.1.1.1).trans ((weight_fst z.1.1.1).trans
      ((weight_fst z.1.1).trans ((weight_fst z.1).trans hz)))))
  have hU : U.size ≤ S := (size_le_weight U).trans
    ((weight_snd z.1.1.1).trans ((weight_fst z.1.1).trans ((weight_fst z.1).trans hz)))
  have hx := capView_weight q U (LatticeUnitStep.unitWordStep (currentParameters z, word)).1
  have hy := capView_weight q U (LatticeUnitStep.unitWordStep (currentParameters z, word)).2
  change weight (z.1, (capView ((q, U), (LatticeUnitStep.unitWordStep (currentParameters z, word)).1),
    capView ((q, U), (LatticeUnitStep.unitWordStep (currentParameters z, word)).2))) ≤ 20 * (S + 1)^3
  rw [weight_prod z.1 _, weight_prod
    (capView ((q, U), (LatticeUnitStep.unitWordStep (currentParameters z, word)).1))
    (capView ((q, U), (LatticeUnitStep.unitWordStep (currentParameters z, word)).2))]
  have hm : q * (4 * U.size + 2) ≤ S * (4 * S + 2) := by gcongr
  nlinarith

def unitWalk (z : ProfileConfiguration × List (List Bool)) : ProfileConfiguration :=
  z.2.foldl (fun state word => advanceUnit (word, state)) z.1

def unitWalkRealizer : Realizer unitWalk :=
  composition (pair second first) (fold advanceUnitRealizer)

lemma unitWalk_nil (z : ProfileConfiguration) : unitWalk (z, []) = z := rfl

lemma unitFold_fixed (words : List (List Bool)) (z : ProfileConfiguration) :
    (words.foldl (fun state word => advanceUnit (word, state)) z).1 = z.1 := by
  induction words generalizing z with
  | nil => rfl
  | cons w ws ih => exact ih _

lemma unitFold_weight (words : List (List Bool)) (z : ProfileConfiguration) (S : ℕ)
    (hz : weight z ≤ S) :
    weight (words.foldl (fun state word => advanceUnit (word, state)) z) ≤ 20 * (S + 1)^3 := by
  induction words using List.reverseRecOn with
  | nil =>
    have hpow : S + 1 ≤ (S + 1)^3 := Nat.le_self_pow (by decide) _
    simpa using hz.trans (by omega : S ≤ 20 * (S + 1)^3)
  | append_singleton words w _ih =>
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    apply advanceUnit_weight
    rw [unitFold_fixed]
    exact (weight_fst z).trans hz

theorem polynomial_unitWalk : PolynomialTime unitWalkRealizer := by
  apply polynomial_composition (polynomial_pair polynomial_second polynomial_first)
  apply polynomial_fold polynomial_advanceUnit (20 * (X + 1)^3)
  intro words z pre post _
  simp only [eval_mul, eval_ofNat, eval_pow, eval_add, eval_X, eval_one]
  exact unitFold_weight pre z (weight (words, z)) (weight_snd (words, z))

open SmallGraphProfiles SmallContextCoordinates CompletionCounts
open PhysicalComputedProposal FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}
variable (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => IdealOracleScales.cutoff (I := Fin m) (J := Fin n)
local notation "L" => IdealOracleScales.padding (I := Fin m) (J := Fin n)
local notation "e" => computedCellEquiv r c U

/-- The cap guard is inactive for the valid neighbor state produced by the
unit step. Immutable metadata retains the literal computed catalogue order. -/
theorem advanceUnit_encoded (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (initial x : States r c U L)
    (bits : Fin (PhysicalReferenceBoolean.stepBits (n := n) r h) → Bool) :
    advanceUnit (List.ofFn bits, LatticeProfileWalk.encodedConfiguration r c h initial x) =
      LatticeProfileWalk.encodedConfiguration r c h initial
        (PhysicalBooleanSampler.unitBitStep r c h x bits) := by
  apply Prod.ext
  · rfl
  · change capViews (PhysicalComputedProposal.stateCodeData r c U L e initial,
      LatticeUnitStep.unitWordStep
        (currentParameters (LatticeProfileWalk.encodedConfiguration r c h initial x),
          List.ofFn bits)) = _
    rw [LatticeProfileWalk.currentParameters_encoded]
    change capViews (PhysicalComputedProposal.stateCodeData r c U L e initial,
      LatticeUnitStep.unitWordStep (LatticeUnitStep.encodedParameters r c h x, List.ofFn bits)) = _
    rw [LatticeUnitStep.unitWordStep_unitBitStep r c htotal h]
    exact LatticeProfileWalk.capViews_stateCode r c initial _

/-- Each array word is a full common step reservation. The completion suffix
is ignored separately at each evolving state; T=0 returns the original code. -/
theorem unitWalk_ofFn (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (initial x : States r c U L) (T : ℕ)
    (bits : Fin T → Fin (PhysicalReferenceBoolean.stepBits (n := n) r h) → Bool) :
    unitWalk (LatticeProfileWalk.encodedConfiguration r c h initial x,
      List.ofFn (fun i => List.ofFn (bits i))) =
      LatticeProfileWalk.encodedConfiguration r c h initial
        (wordWalk (PhysicalBooleanSampler.unitBitStep r c h) x T bits) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    unfold unitWalk at ih ⊢
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
    change advanceUnit (List.ofFn (bits (Fin.last T)),
      (List.ofFn (fun i => List.ofFn ((Fin.init bits) i))).foldl
        (fun state word => advanceUnit (word, state))
        (LatticeProfileWalk.encodedConfiguration r c h initial x)) = _
    rw [ih (Fin.init bits)]
    exact advanceUnit_encoded r c htotal h initial _ _

/-- Exact flat-word correspondence at the same T*(s+fStep) width as the
reference branch. No missing-reference hypothesis is needed for movement. -/
theorem unitWalk_flat (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (initial x : States r c U L) (T : ℕ)
    (bits : Fin (T * PhysicalReferenceBoolean.stepBits (n := n) r h) → Bool) :
    unitWalk (LatticeProfileWalk.encodedConfiguration r c h initial x,
      List.ofFn (fun i => List.ofFn
        (GridBoundary.gridWordEquiv T (PhysicalReferenceBoolean.stepBits (n := n) r h) bits i))) =
      LatticeProfileWalk.encodedConfiguration r c h initial
        (PhysicalBooleanSampler.flatUnitWalk r c x T h bits) :=
  unitWalk_ofFn r c htotal h initial x T
    (GridBoundary.gridWordEquiv T (PhysicalReferenceBoolean.stepBits (n := n) r h) bits)

/-- Exposes final state parameters for the separate terminal program. -/
theorem unitWalk_currentParameters (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (initial x : States r c U L) (T : ℕ)
    (bits : Fin (T * PhysicalReferenceBoolean.stepBits (n := n) r h) → Bool) :
    currentParameters (unitWalk (LatticeProfileWalk.encodedConfiguration r c h initial x,
      List.ofFn (fun i => List.ofFn
        (GridBoundary.gridWordEquiv T (PhysicalReferenceBoolean.stepBits (n := n) r h) bits i)))) =
      LatticeUnitStep.encodedParameters r c h
        (PhysicalBooleanSampler.flatUnitWalk r c x T h bits) := by
  rw [unitWalk_flat r c htotal h initial x T bits, LatticeProfileWalk.currentParameters_encoded]
  rfl

end
end Math115.LatticeUnitWalk
