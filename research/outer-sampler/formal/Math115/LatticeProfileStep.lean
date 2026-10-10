/-
SPDX-License-Identifier: Apache-2.0
The generic encoded profile transition with only its completion call replaced
by the dilated lattice completion program. Exact ideal-scale word semantics
are proved independently of the old paper-scale transition specialization.
No full outer-loop realizer or composed machine-time exponent is asserted.
-/
import Math115.CompletionSamplerSemantics
import Math115.PhysicalReferenceBoolean
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileTransitionProgram
import OAI.Combinatorics.ContingencyTables.Transport.ListedReferenceDecision

namespace Math115.LatticeProfileStep

open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped
open ProfilePrograms DensePrograms

def stepCompletion (z : ProfileStepInput) : MatrixCode :=
  CompletionSamplerProgram.draw (residualParameters z.1, z.2.2)

def stepCompletionRealizer : Realizer stepCompletion :=
  composition (pair (composition first residualParametersRealizer) (composition second second))
    CompletionSamplerProgram.drawRealizer

theorem polynomial_stepCompletion : PolynomialTime stepCompletionRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_residualParameters)
    (polynomial_composition polynomial_second polynomial_second)) CompletionSamplerProgram.polynomial_draw

def stepTranslation (z : ProfileStepInput) : TranslationData :=
  ((stepOldMargins z, stepNewMargins z), stepCompletion z)

def stepTranslationRealizer : Realizer stepTranslation :=
  pair (pair stepOldMarginsRealizer stepNewMarginsRealizer) stepCompletionRealizer

theorem polynomial_stepTranslation : PolynomialTime stepTranslationRealizer :=
  polynomial_pair (polynomial_pair polynomial_stepOldMargins polynomial_stepNewMargins)
    polynomial_stepCompletion

def profileStep (z : ProfileStepInput) : List ℕ × List ℕ :=
  if translationValid (stepTranslation z) then stepCandidateViews z else z.1.1.1.1.1.2

def profileStepRealizer : Realizer profileStep :=
  (choose (composition stepTranslationRealizer translationValidRealizer)
    stepCandidateViewsRealizer stepViews).congr
      (by intro z; simp only [profileStep, Function.comp_apply])

theorem polynomial_profileStep : PolynomialTime profileStepRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition polynomial_stepTranslation polynomial_translationValid)
    polynomial_stepCandidateViews polynomial_stepViews)

open SmallGraphProfiles SmallContextCoordinates SmallContextFibres
open PhysicalCompletionFibres FirstPaperPhysicalMarginal CompletionCounts PaddedCompletions
open ReducedSmallChain PhysicalComputedProposal PhysicalCompletionOracle CompletionTranslation
open FirstSuccess FairBits
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
local notation "s" => Nat.clog 2 (32 * d^2)
variable (hr : 0 < (largeIndices
  (IdealOracleScales.cutoff (I := Fin m) (J := Fin n), List.ofFn r)).length)
variable (hc : 0 < (largeIndices
  (IdealOracleScales.cutoff (I := Fin m) (J := Fin n), List.ofFn c)).length)
local notation "i₀" => largeOptionEquiv r U hr none
local notation "j₀" => largeOptionEquiv c U hc none
local notation "Rₗ" => listedRows r c U L B hr
local notation "Pₗ" => listedColumns r c U L B hc
local notation "R₀" => referenceRows r c U L B i₀
local notation "P₀" => referenceColumns r c U L B j₀
local notation "f" => PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r
local notation "nr" => ListedLatticeCompletion.tailCount r U
local notation "nc" => ListedLatticeCompletion.tailCount c U

private lemma apply_decision {X Y : Type*} (encode : X → Y) (x y : X)
    (test : Bool) (accept : Prop) [Decidable accept] (h : test = true ↔ accept) :
    (if test then encode y else encode x) = encode (if accept then y else x) := by
  by_cases hp : accept
  · rw [ite_eq_left hp, ite_eq_left (h.mpr hp)]
  · rw [ite_eq_right hp, ite_eq_right (fun ht => hp (h.mp ht))]

private lemma completionDecision_some_formula {X I J : Type*} [Fintype I] [Fintype J]
    (R : X → Option I → ℕ) (P : X → Option J → ℕ) (x y : X) (A : Table (R x) (P x)) :
    completionDecision R P x (some y) A =
      if ∀ i j, 0 ≤ (A.val i j : ℤ) + between (R x) (R y) (P x) (P y) i j then y else x := rfl

def encodedStepInput (h : ℕ) (x : States r c U L)
    (proposal : Fin s → Bool) (completion : Fin (f h) → Bool) : ProfileStepInput :=
  (((PhysicalComputedProposal.stateCodeData r c U L e x, L), (d, h)),
    (List.ofFn proposal, List.ofFn completion))

/-- Proposal-code totality is established at the actual free physical scales;
the old paper-scale encoded-proposal specialization is not used. -/
theorem codeProposal_encoded (htotal : ∑ i, r i = ∑ j, c j) (x : States r c U L)
    (bits : Fin s → Bool) :
    codeNeighborProposal (PhysicalComputedProposal.stateCodeData r c U L e x, List.ofFn bits) =
      (PhysicalComputedProposal.computedProposal r c U L x bits).map
        (PhysicalComputedProposal.computedStateCode r c U L) := by
  cases hp : codeNeighborProposal (PhysicalComputedProposal.stateCodeData r c U L e x,
      List.ofFn bits) with
  | none =>
    simp only [PhysicalComputedProposal.computedProposal, PhysicalComputedProposal.decodedCodeProposal,
      hp, Option.bind_none, Option.map_none]
  | some v =>
    have hv : v ∈ codeNeighbors (PhysicalComputedProposal.stateCodeData r c U L e x) :=
      List.mem_of_getElem? hp
    obtain ⟨y, hy⟩ := PhysicalComputedProposal.codeNeighbors_decode_total r c U L e htotal x v hv
    have he := (PhysicalComputedProposal.decodeStateCode_eq_some_iff r c U L e v y).mp hy
    simp only [PhysicalComputedProposal.computedProposal, PhysicalComputedProposal.decodedCodeProposal,
      hp, Option.bind_some, hy, Option.map_some, PhysicalComputedProposal.computedStateCode, he]

lemma stepCandidate_encoded (h : ℕ) (x y : States r c U L)
    (proposal : Fin s → Bool) (completion : Fin (f h) → Bool)
    (hp : codeNeighborProposal (PhysicalComputedProposal.stateCodeData r c U L e x,
      List.ofFn proposal) = some (PhysicalComputedProposal.computedStateCode r c U L y)) :
    stepCandidateParameters (encodedStepInput r c h x proposal completion) =
      ((PhysicalComputedProposal.stateCodeData r c U L e y, L), (d, h)) := by
  simp only [stepCandidateParameters, stepCandidate, stepCandidateViews, stepProposal,
    encodedStepInput, hp, Option.getD_some, PhysicalComputedProposal.computedStateCode]
  rfl

include hr hc

/-- The generic residual program computes exactly the actual coarse margin
lists used by the completion program, including complemented column views. -/
theorem residualParameters_code (h : ℕ) (x : States r c U L) :
    residualParameters ((PhysicalComputedProposal.stateCodeData r c U L e x, L), (d, h)) =
      CompletionSamplerSemantics.parameters (m := nr) (n := nc) d
        (ListedLatticeCompletion.coarseRows r c hr x)
        (ListedLatticeCompletion.coarseColumns r c hc x) h := by
  apply Prod.ext
  · apply Prod.ext
    · exact (ListedLatticeCompletion.coarseRows_code r c hr e x).symm
    · exact (ListedLatticeCompletion.coarseColumns_code r c hc e x).symm
  · rfl

def listedDraw (h : ℕ) (x : States r c U L) (completion : Fin (f h) → Bool) :
    Table (I := Option (Fin nr)) (J := Option (Fin nc)) (Rₗ x) (Pₗ x) :=
  listedFibreEquiv r c U L B hr hc x
    (physical_paper_capacity _ r c _ L U dimension_le_allowance x)
    (ListedLatticeCompletion.completionDraw r c hr hc x h completion)

lemma listedDraw_output (h : ℕ) (x : States r c U L) (completion : Fin (f h) → Bool) :
    tableOutput (m := nr) (n := nc) (listedDraw r c hr hc h x completion) =
      matrixCode (ListedLatticeCompletion.programTable r c hr hc x h completion).val := by
  have he :
      tableReindex (finSuccEquiv nr) (finSuccEquiv nc) (Rₗ x) (Pₗ x)
        (listedDraw r c hr hc h x completion) =
      ListedLatticeCompletion.programTable r c hr hc x h completion := by
    unfold listedDraw
    exact (ListedLatticeCompletion.finiteFibreEquiv r c hr hc x).apply_symm_apply
      (ListedLatticeCompletion.programTable r c hr hc x h completion)
  exact congrArg
    (fun X : Table (ListedLatticeCompletion.coarseRows r c hr x)
        (ListedLatticeCompletion.coarseColumns r c hc x) => matrixCode X.val) he

attribute [local irreducible] listedDraw CompletionSamplerProgram.draw
  ProfilePrograms.residualParameters

set_option maxHeartbeats 2000000 in
lemma stepCompletion_encoded (h : ℕ) (x : States r c U L)
    (proposal : Fin s → Bool) (completion : Fin (f h) → Bool) :
    stepCompletion (encodedStepInput r c h x proposal completion) =
      tableOutput (m := nr) (n := nc) (listedDraw r c hr hc h x completion) := by
  calc
    stepCompletion (encodedStepInput r c h x proposal completion) =
        CompletionSamplerProgram.draw
          (CompletionSamplerSemantics.parameters (m := nr) (n := nc) d
            (ListedLatticeCompletion.coarseRows r c hr x)
            (ListedLatticeCompletion.coarseColumns r c hc x) h, List.ofFn completion) := by
      simpa only [stepCompletion, encodedStepInput] using
        congrArg (fun parameters : CompletionSamplerProgram.Parameters =>
          CompletionSamplerProgram.draw (parameters, List.ofFn completion))
          (residualParameters_code r c hr hc h x)
    _ = matrixCode (ListedLatticeCompletion.programTable r c hr hc x h completion).val :=
      ListedLatticeCompletion.programTable_code r c hr hc x h completion
    _ = tableOutput (m := nr) (n := nc) (listedDraw r c hr hc h x completion) :=
      (listedDraw_output r c hr hc h x completion).symm

lemma stepTranslation_encoded (h : ℕ) (x y : States r c U L)
    (proposal : Fin s → Bool) (completion : Fin (f h) → Bool)
    (hp : codeNeighborProposal (PhysicalComputedProposal.stateCodeData r c U L e x,
      List.ofFn proposal) = some (PhysicalComputedProposal.computedStateCode r c U L y)) :
    stepTranslation (encodedStepInput r c h x proposal completion) =
      (((marginCode (Rₗ x), marginCode (Pₗ x)), (marginCode (Rₗ y), marginCode (Pₗ y))),
        tableOutput (m := nr) (n := nc) (listedDraw r c hr hc h x completion)) := by
  have hmargins (z : States r c U L) :
      (residualParameters ((PhysicalComputedProposal.stateCodeData r c U L e z, L), (d, h))).1 =
        (marginCode (Rₗ z), marginCode (Pₗ z)) :=
    (congrArg (fun parameters : CompletionSamplerProgram.Parameters => parameters.1)
      (residualParameters_code r c hr hc h z)).trans
    (congrArg (fun parameters : CompletionSamplerProgram.Parameters => parameters.1)
      (ListedLatticeCompletion.parameters_listed r c hr hc z h))
  unfold stepTranslation stepOldMargins stepNewMargins
  rw [stepCandidate_encoded r c h x y proposal completion hp,
    stepCompletion_encoded r c hr hc h x proposal completion]
  dsimp only [encodedStepInput]
  rw [hmargins x, hmargins y]

lemma listed_between (x y : States r c U L) (i) (j) :
    between (Rₗ x) (Rₗ y) (Pₗ x) (Pₗ y) i j =
      between (R₀ x) (R₀ y) (P₀ x) (P₀ y)
        (listedReferenceIndex r U hr i) (listedReferenceIndex c U hc j) := by
  have he := between_reindex (listedReferenceIndex r U hr) (listedReferenceIndex c U hc)
    (listedReferenceIndex_none r U hr) (listedReferenceIndex_none c U hc)
    (R₀ x) (R₀ y) (P₀ x) (P₀ y) i j
  simpa only [listedReference_row, listedReference_column] using he

/-- Reindex the signed translation test while preserving the computed none
reference. This proof is generic in the coordinates beneath the new scales. -/
lemma translated_nonnegative (h : ℕ) (x y : States r c U L)
    (completion : Fin (f h) → Bool) :
    (∀ i j, 0 ≤ ((listedDraw r c hr hc h x completion).val i j : ℤ) +
      between (Rₗ x) (Rₗ y) (Pₗ x) (Pₗ y) i j) ↔
    ∀ i j, 0 ≤ ((ListedLatticeCompletion.referenceDraw r c hr hc x h completion).val i j : ℤ) +
      between (R₀ x) (R₀ y) (P₀ x) (P₀ y) i j := by
  have he (i : Option (Fin nr)) (j : Option (Fin nc)) :
      (listedDraw r c hr hc h x completion).val i j =
      (ListedLatticeCompletion.referenceDraw r c hr hc x h completion).val
        (listedReferenceIndex r U hr i) (listedReferenceIndex c U hc j) := by
    unfold listedDraw
    exact listedFibreEquiv_entry r c U L B hr hc x
      (physical_paper_capacity _ r c _ L U dimension_le_allowance x)
      (ListedLatticeCompletion.completionDraw r c hr hc x h completion) i j
  constructor
  · intro hh i j
    obtain ⟨i, rfl⟩ := (listedReferenceIndex r U hr).surjective i
    obtain ⟨j, rfl⟩ := (listedReferenceIndex c U hc).surjective j
    have hij := hh i j
    rw [he i j, Math115.LatticeProfileStep.listed_between r c hr hc x y i j] at hij
    exact hij
  · intro hh i j
    rw [he i j, Math115.LatticeProfileStep.listed_between r c hr hc x y i j]
    exact hh _ _

lemma listed_completionDecision (h : ℕ) (x : States r c U L)
    (proposal : Option (States r c U L)) (completion : Fin (f h) → Bool) :
    completionDecision Rₗ Pₗ x proposal (listedDraw r c hr hc h x completion) =
      completionDecision R₀ P₀ x proposal
        (ListedLatticeCompletion.referenceDraw r c hr hc x h completion) := by
  cases proposal with
  | none => rfl
  | some y =>
    unfold completionDecision
    dsimp only
    have he := translated_nonnegative r c hr hc h x y completion
    split_ifs with h₁ h₂ h₂
    · rfl
    · exact False.elim (h₂ (he.mp h₁))
    · exact False.elim (h₁ (he.mpr h₂))
    · rfl

/-- Exact pointwise correctness for the new completion program on every
proposal and reserved completion word, including the unused-proposal hold. -/
theorem profileStep_encoded (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (x : States r c U L) (proposal : Fin s → Bool) (completion : Fin (f h) → Bool) :
    profileStep (encodedStepInput r c h x proposal completion) =
      PhysicalComputedProposal.computedStateCode r c U L
        (completionDecision Rₗ Pₗ x (PhysicalComputedProposal.computedProposal r c U L x proposal)
          (listedDraw r c hr hc h x completion)) := by
  have hp := codeProposal_encoded r c htotal x proposal
  cases hd : PhysicalComputedProposal.computedProposal r c U L x proposal with
  | none =>
    rw [hd, Option.map_none] at hp
    unfold profileStep
    have hcand : stepCandidateViews (encodedStepInput r c h x proposal completion) =
        PhysicalComputedProposal.computedStateCode r c U L x := by
      simp only [stepCandidateViews, stepProposal, encodedStepInput, hp, Option.getD_none]
      rfl
    rw [hcand]
    split_ifs <;> rfl
  | some y =>
    rw [hd, Option.map_some] at hp
    have ht := stepTranslation_encoded r c hr hc h x y proposal completion hp
    have hv := translationValid_code (m := nr) (n := nc)
      (Rₗ x) (Rₗ y) (Pₗ x) (Pₗ y) (listedDraw r c hr hc h x completion)
    have hcand : stepCandidateViews (encodedStepInput r c h x proposal completion) =
        PhysicalComputedProposal.computedStateCode r c U L y := by
      simp only [stepCandidateViews, stepProposal, encodedStepInput, hp, Option.getD_some]
    have hviews : (encodedStepInput r c h x proposal completion).1.1.1.1.1.2 =
        PhysicalComputedProposal.computedStateCode r c U L x := rfl
    have hdecision := completionDecision_some_formula (I := Fin nr) (J := Fin nc)
      Rₗ Pₗ x y (listedDraw r c hr hc h x completion)
    have hbranch := (apply_decision
      (PhysicalComputedProposal.computedStateCode r c U L) x y _ _ hv).trans
      (congrArg (PhysicalComputedProposal.computedStateCode r c U L) hdecision.symm)
    have hprogram : profileStep (encodedStepInput r c h x proposal completion) =
        if translationValid
          (((marginCode (Rₗ x), marginCode (Pₗ x)), (marginCode (Rₗ y), marginCode (Pₗ y))),
            tableOutput (m := nr) (n := nc) (listedDraw r c hr hc h x completion)) then
          PhysicalComputedProposal.computedStateCode r c U L y
        else PhysicalComputedProposal.computedStateCode r c U L x := by
      simp only [profileStep, ht, hcand, hviews]
    exact hprogram.trans hbranch

theorem profileStep_bitStep (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (x : States r c U L)
    (bits : Fin (PhysicalReferenceBoolean.stepBits (n := n) r h) → Bool) :
    profileStep (encodedStepInput r c h x
      (splitWordEquiv s (f h) bits).1 (splitWordEquiv s (f h) bits).2) =
      PhysicalComputedProposal.computedStateCode r c U L
        (PhysicalReferenceBoolean.bitStep r c hr hc h x bits) := by
  let proposal := (splitWordEquiv s (f h) bits).1
  let completion := (splitWordEquiv s (f h) bits).2
  calc
    profileStep (encodedStepInput r c h x proposal completion) =
        PhysicalComputedProposal.computedStateCode r c U L
          (completionDecision Rₗ Pₗ x
            (PhysicalComputedProposal.computedProposal r c U L x proposal)
            (listedDraw r c hr hc h x completion)) :=
      profileStep_encoded r c hr hc htotal h x proposal completion
    _ = PhysicalComputedProposal.computedStateCode r c U L
          (completionDecision R₀ P₀ x
            (PhysicalComputedProposal.computedProposal r c U L x proposal)
            (ListedLatticeCompletion.referenceDraw r c hr hc x h completion)) :=
      congrArg (PhysicalComputedProposal.computedStateCode r c U L)
        (listed_completionDecision r c hr hc h x
          (PhysicalComputedProposal.computedProposal r c U L x proposal) completion)
    _ = PhysicalComputedProposal.computedStateCode r c U L
          (PhysicalReferenceBoolean.bitStep r c hr hc h x bits) := rfl


end
end Math115.LatticeProfileStep
