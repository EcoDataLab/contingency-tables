/-
SPDX-License-Identifier: Apache-2.0
Bounded encoded profile fold using the lattice-completion step. Generic cap
guards control intermediate encoded size; exact word semantics preserve valid
computed profile codes at the actual ideal cutoff/padding scales.
Terminal reconstruction, outer retry, and final machine exponent are separate.
-/
import Math115.LatticeProfileStep
import OAI.Combinatorics.ContingencyTables.Transport.BoundedProfileWalk

namespace Math115.LatticeProfileWalk

open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped
open ProfilePrograms Polynomial

def boundedNext (z : ProfileConfiguration × ProfileWord) : List ℕ × List ℕ :=
  capViews (z.1.1.1.1, LatticeProfileStep.profileStep (currentParameters z.1, z.2))

def boundedNextRealizer : Realizer boundedNext := by
  let check : Realizer (fun z : ProfileConfiguration × ProfileWord => z.1.1.1.1) :=
    composition (composition (composition first first) first) first
  let input : Realizer (fun z : ProfileConfiguration × ProfileWord => (currentParameters z.1, z.2)) :=
    pair (composition first currentParametersRealizer) second
  exact composition (pair check (composition input LatticeProfileStep.profileStepRealizer)) capViewsRealizer

theorem polynomial_boundedNext : PolynomialTime boundedNextRealizer := by
  unfold boundedNextRealizer
  exact polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_first polynomial_first) polynomial_first) polynomial_first)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_currentParameters) polynomial_second)
      LatticeProfileStep.polynomial_profileStep)) polynomial_capViews

def advanceProfile (z : ProfileWord × ProfileConfiguration) : ProfileConfiguration :=
  (z.2.1, boundedNext (z.2, z.1))

def advanceProfileRealizer : Realizer advanceProfile :=
  pair (composition second first) (composition
    (f := fun z : ProfileWord × ProfileConfiguration => (z.2, z.1)) (g := boundedNext)
    (pair second first) boundedNextRealizer)

theorem polynomial_advanceProfile : PolynomialTime advanceProfileRealizer :=
  polynomial_pair (polynomial_composition polynomial_second polynomial_first)
    (polynomial_composition (polynomial_pair polynomial_second polynomial_first) polynomial_boundedNext)

/-- The cap guard bounds either returned view regardless of the supplied
words or the uncapped step's output. Immutable metadata determines q and U. -/
lemma advanceProfile_weight (word : ProfileWord) (z : ProfileConfiguration) (S : ℕ)
    (hz : weight z.1 ≤ S) : weight (advanceProfile (word, z)) ≤ 20 * (S + 1)^3 := by
  let q := z.1.1.1.1.1.1.length
  let U := z.1.1.1.2
  have hq : q ≤ S := (list_length_le_weight _).trans ((weight_fst z.1.1.1.1.1).trans
    ((weight_fst z.1.1.1.1).trans ((weight_fst z.1.1.1).trans
      ((weight_fst z.1.1).trans ((weight_fst z.1).trans hz)))))
  have hU : U.size ≤ S := (size_le_weight U).trans
    ((weight_snd z.1.1.1).trans ((weight_fst z.1.1).trans ((weight_fst z.1).trans hz)))
  have hx := capView_weight q U (LatticeProfileStep.profileStep (currentParameters z, word)).1
  have hy := capView_weight q U (LatticeProfileStep.profileStep (currentParameters z, word)).2
  change weight (z.1, (capView ((q, U), (LatticeProfileStep.profileStep (currentParameters z, word)).1),
    capView ((q, U), (LatticeProfileStep.profileStep (currentParameters z, word)).2))) ≤ 20 * (S + 1)^3
  rw [weight_prod z.1 _, weight_prod
    (capView ((q, U), (LatticeProfileStep.profileStep (currentParameters z, word)).1))
    (capView ((q, U), (LatticeProfileStep.profileStep (currentParameters z, word)).2))]
  have hm : q * (4 * U.size + 2) ≤ S * (4 * S + 2) := by gcongr
  nlinarith

def profileWalk (z : ProfileConfiguration × List ProfileWord) : ProfileConfiguration :=
  z.2.foldl (fun state word => advanceProfile (word, state)) z.1

def profileWalkRealizer : Realizer profileWalk :=
  composition (pair second first) (fold advanceProfileRealizer)

lemma profileFold_fixed (words : List ProfileWord) (z : ProfileConfiguration) :
    (words.foldl (fun state word => advanceProfile (word, state)) z).1 = z.1 := by
  induction words generalizing z with
  | nil => rfl
  | cons w ws ih => exact ih _

lemma profileFold_weight (words : List ProfileWord) (z : ProfileConfiguration) (S : ℕ)
    (hz : weight z ≤ S) :
    weight (words.foldl (fun state word => advanceProfile (word, state)) z) ≤ 20 * (S + 1)^3 := by
  induction words using List.reverseRecOn with
  | nil =>
    have hpow : S + 1 ≤ (S + 1)^3 := Nat.le_self_pow (by decide) _
    simpa using hz.trans (by omega : S ≤ 20 * (S + 1)^3)
  | append_singleton words w _ih =>
    rw [List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    apply advanceProfile_weight
    rw [profileFold_fixed]
    exact (weight_fst z).trans hz

theorem polynomial_profileWalk : PolynomialTime profileWalkRealizer := by
  apply polynomial_composition (polynomial_pair polynomial_second polynomial_first)
  apply polynomial_fold polynomial_advanceProfile (20 * (X + 1)^3)
  intro words z pre post _
  simp only [eval_mul, eval_ofNat, eval_pow, eval_add, eval_X, eval_one]
  exact profileFold_weight pre z (weight (words, z)) (weight_snd (words, z))

open SmallGraphProfiles SmallContextCoordinates SmallContextFibres
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts
open ReducedSmallChain PhysicalComputedProposal FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}
variable (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => IdealOracleScales.cutoff (I := Fin m) (J := Fin n)
local notation "L" => IdealOracleScales.padding (I := Fin m) (J := Fin n)
local notation "small" => firstPaperSmall r c U
local notation "B" => capacity r c U L
local notation "e" => computedCellEquiv r c U
local notation "q" => List.length (computedCatalog r c U)
local notation "s" => Nat.clog 2 (32 * d^2)
local notation "f" => PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r

lemma stateCode_bounded (x : States r c U L) (a : Cells small) (side : Bool) :
    physicalProfile small B r c L x (a, side) ≤ U := by
  have he := (PhysicalComputedProposal.physicalProfile_feasible r c U L x).bounded (a, side)
  exact he.trans_eq (capacity_small r c U L _ _ a.property)

lemma capViews_stateCode (initial x : States r c U L) :
    capViews (PhysicalComputedProposal.stateCodeData r c U L e initial,
      PhysicalComputedProposal.computedStateCode r c U L x) =
      PhysicalComputedProposal.computedStateCode r c U L x := by
  have hb (side : Bool) : capView ((q, U), viewList small e (physicalProfile small B r c L x) side) =
      viewList small e (physicalProfile small B r c L x) side := by
    apply capView_eq
    · simp only [viewList, List.length_ofFn]
    · intro a ha
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
      exact stateCode_bounded r c x (e i) side
  simpa only [capViews, PhysicalComputedProposal.stateCodeData, codeCheckData, cellCatalog,
    List.length_ofFn, PhysicalComputedProposal.computedStateCode, PhysicalComputedProposal.stateCode,
    profileCode] using Prod.ext (hb false) (hb true)

def encodedConfiguration (h : ℕ) (initial current : States r c U L) : ProfileConfiguration :=
  (((PhysicalComputedProposal.stateCodeData r c U L e initial, L), (d, h)),
    PhysicalComputedProposal.computedStateCode r c U L current)

lemma currentParameters_encoded (h : ℕ) (initial current : States r c U L) :
    currentParameters (encodedConfiguration r c h initial current) =
      ((PhysicalComputedProposal.stateCodeData r c U L e current, L), (d, h)) := rfl

variable (hr : 0 < (largeIndices
  (IdealOracleScales.cutoff (I := Fin m) (J := Fin n), List.ofFn r)).length)
variable (hc : 0 < (largeIndices
  (IdealOracleScales.cutoff (I := Fin m) (J := Fin n), List.ofFn c)).length)

theorem advanceProfile_encoded (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (initial x : States r c U L)
    (bits : Fin (PhysicalReferenceBoolean.stepBits (n := n) r h) → Bool) :
    advanceProfile ((List.ofFn (splitWordEquiv s (f h) bits).1,
      List.ofFn (splitWordEquiv s (f h) bits).2), encodedConfiguration r c h initial x) =
      encodedConfiguration r c h initial (PhysicalReferenceBoolean.bitStep r c hr hc h x bits) := by
  apply Prod.ext
  · rfl
  · change capViews (PhysicalComputedProposal.stateCodeData r c U L e initial,
      LatticeProfileStep.profileStep (LatticeProfileStep.encodedStepInput r c h x
        (splitWordEquiv s (f h) bits).1 (splitWordEquiv s (f h) bits).2)) = _
    rw [LatticeProfileStep.profileStep_bitStep r c hr hc htotal h]
    exact capViews_stateCode r c initial _

theorem profileWalk_ofFn (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (initial x : States r c U L) (T : ℕ)
    (bits : Fin T → Fin (PhysicalReferenceBoolean.stepBits (n := n) r h) → Bool) :
    profileWalk (encodedConfiguration r c h initial x,
      List.ofFn (fun i => (List.ofFn (splitWordEquiv s (f h) (bits i)).1,
        List.ofFn (splitWordEquiv s (f h) (bits i)).2))) =
      encodedConfiguration r c h initial
        (wordWalk (PhysicalReferenceBoolean.bitStep r c hr hc h) x T bits) := by
  -- Prove the recursion equation with an abstract step, so reflexivity does not
  -- unfold the concrete completion/proposal machinery during elaboration.
  have wordWalk_succ {α : Type*} {k : ℕ} (step : α → (Fin k → Bool) → α)
      (a : α) (t : ℕ) (words : Fin (t + 1) → Fin k → Bool) :
      wordWalk step a (t + 1) words =
        step (wordWalk step a t (Fin.init words)) (words (Fin.last t)) := rfl
  induction T with
  | zero => rfl
  | succ T ih =>
    unfold profileWalk at ih ⊢
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
    change advanceProfile ((List.ofFn (splitWordEquiv s (f h) (bits (Fin.last T))).1,
      List.ofFn (splitWordEquiv s (f h) (bits (Fin.last T))).2),
      (List.ofFn (fun i => (List.ofFn (splitWordEquiv s (f h) ((Fin.init bits) i)).1,
        List.ofFn (splitWordEquiv s (f h) ((Fin.init bits) i)).2))).foldl
          (fun state word => advanceProfile (word, state))
          (encodedConfiguration r c h initial x)) = _
    rw [ih (Fin.init bits)]
    have hwalk : wordWalk (PhysicalReferenceBoolean.bitStep r c hr hc h) x (T + 1) bits =
        PhysicalReferenceBoolean.bitStep r c hr hc h
          (wordWalk (PhysicalReferenceBoolean.bitStep r c hr hc h) x T (Fin.init bits))
          (bits (Fin.last T)) :=
      wordWalk_succ (PhysicalReferenceBoolean.bitStep r c hr hc h) x T bits
    rw [hwalk]
    exact advanceProfile_encoded r c hr hc htotal h initial
      (wordWalk (PhysicalReferenceBoolean.bitStep r c hr hc h) x T (Fin.init bits))
      (bits (Fin.last T))

theorem profileWalk_flat (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (initial x : States r c U L) (T : ℕ)
    (bits : Fin (T * PhysicalReferenceBoolean.stepBits (n := n) r h) → Bool) :
    profileWalk (encodedConfiguration r c h initial x,
      List.ofFn (fun i =>
        let word := GridBoundary.gridWordEquiv T (PhysicalReferenceBoolean.stepBits (n := n) r h) bits i
        (List.ofFn (splitWordEquiv s (f h) word).1,
          List.ofFn (splitWordEquiv s (f h) word).2))) =
      encodedConfiguration r c h initial (PhysicalReferenceBoolean.flatWalk r c hr hc x T h bits) :=
  profileWalk_ofFn r c hr hc htotal h initial x T
    (GridBoundary.gridWordEquiv T (PhysicalReferenceBoolean.stepBits (n := n) r h) bits)

/-- Terminal preparation may replace just the precision field after obtaining
these exact final-state parameters; no caller-provided final state is needed. -/
theorem profileWalk_currentParameters (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (initial x : States r c U L) (T : ℕ)
    (bits : Fin (T * PhysicalReferenceBoolean.stepBits (n := n) r h) → Bool) :
    currentParameters (profileWalk (encodedConfiguration r c h initial x,
      List.ofFn (fun i =>
        let word := GridBoundary.gridWordEquiv T (PhysicalReferenceBoolean.stepBits (n := n) r h) bits i
        (List.ofFn (splitWordEquiv s (f h) word).1,
          List.ofFn (splitWordEquiv s (f h) word).2)))) =
      ((PhysicalComputedProposal.stateCodeData r c U L e
        (PhysicalReferenceBoolean.flatWalk r c hr hc x T h bits), L), (d, h)) := by
  rw [profileWalk_flat r c hr hc htotal h initial x T bits, currentParameters_encoded]

end
end Math115.LatticeProfileWalk
