/-
SPDX-License-Identifier: Apache-2.0
Both branches of the ideal-scale sampler on a fixed finite Boolean word.
The reference branch uses the actual listed completion program. The empty
branch retains the neighbor walk and reconstructs its unique two-view fibre.
This is finite-word semantics; encoded outer-loop cost remains separate.
-/
import Math115.PhysicalReferenceBoolean
import Math115.PhysicalEmptyCompletion
import OAI.Combinatorics.ContingencyTables.Transport.FiniteProposalStay

namespace Math115.PhysicalBooleanSampler

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open SmallGraphProfiles CompletionCounts ProfilePrograms ReducedSmallChain
open PhysicalCompletionOracle PhysicalStationarySuccess PhysicalFiniteWalk
open PhysicalRationalKernel PhysicalStateNonempty CompletionRetryBudget
open CompletionTranslation ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => IdealOracleScales.cutoff (I := Fin m) (J := Fin n)
local notation "L" => IdealOracleScales.padding (I := Fin m) (J := Fin n)
local notation "s" => Nat.clog 2 (32 * d^2)
local notation "f" => PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r
local notation "stepBits" => PhysicalReferenceBoolean.stepBits (n := n) r
local notation "attemptBits" => PhysicalReferenceBoolean.attemptBits (n := n) r
local notation "outerBits" => PhysicalReferenceBoolean.outerBits (n := n) r

/-- The branch test is on the lengths of the actual computed index lists. -/
def bothLarge : Prop :=
  0 < (largeIndices (U, List.ofFn r)).length ∧
    0 < (largeIndices (U, List.ofFn c)).length

lemma not_bothLarge_reference (h : ¬ bothLarge r c) :
    ¬ (Nonempty (LargeRows r U) ∧ Nonempty (LargeColumns c U)) := by
  rintro ⟨⟨i⟩, ⟨j⟩⟩
  exact h ⟨largeIndices_pos r U i, largeIndices_pos c U j⟩

/-- The completion suffix is reserved but ignored in the unit branch.
Non-hold neighbor proposals still move the physical state. -/
def unitBitStep (hStep : ℕ) (x : States r c U L)
    (bits : Fin (stepBits hStep) → Bool) : States r c U L :=
  (PhysicalComputedProposal.computedProposal r c U L x
    (prefixWord (show s ≤ stepBits hStep from Nat.le_add_right _ _) bits)).getD x

section UnitStepMapProof
attribute [local irreducible] FirstSuccess.mapLaw

theorem unitBitStep_law (htotal : ∑ i, r i = ∑ j, c j)
    (hStep : ℕ) (x : States r c U L) :
    letI := states_nonempty r c U L htotal
    mapLaw (uniformLaw (α := Fin (stepBits hStep) → Bool)) (unitBitStep r c hStep x) =
      unitTransitionLaw r c U L x := by
  letI := states_nonempty r c U L htotal
  calc
    _ = mapLaw (uniformLaw (α := Fin s → Bool))
        (fun bits => (PhysicalComputedProposal.computedProposal r c U L x bits).getD x) :=
      padded_draw_law (show s ≤ stepBits hStep from Nat.le_add_right _ _)
        (fun bits => (PhysicalComputedProposal.computedProposal r c U L x bits).getD x)
    _ = mapLaw
        (mapLaw (uniformLaw (α := Fin s → Bool))
          (PhysicalComputedProposal.computedProposal r c U L x))
        (fun proposal => proposal.getD x) :=
      (mapLaw_comp (A := Fin s → Bool) (B := Option (States r c U L))
        (C := States r c U L) (uniformLaw (α := Fin s → Bool))
        (PhysicalComputedProposal.computedProposal r c U L x)
        (fun proposal : Option (States r c U L) => proposal.getD x)).symm
    _ = mapLaw (physicalProposalLaw r c U L x) (fun proposal => proposal.getD x) :=
      congrArg (fun p : RationalLaw (Option (States r c U L)) =>
        mapLaw p (fun proposal => proposal.getD x))
        (PhysicalComputedProposal.computedProposal_law r c U L htotal x)
    _ = _ := by
      apply RationalLaw.ext
      funext y
      exact proposalStayLaw_mass (unitMoveRat r c U L x)
        (proposalWeight_nonnegative r c U L x) (proposalWeight_total_le_one r c U L x) x y

end UnitStepMapProof

def flatUnitWalk (x : States r c U L) (T hStep : ℕ)
    (bits : Fin (T * stepBits hStep) → Bool) : States r c U L :=
  wordWalk (unitBitStep r c hStep) x T
    (GridBoundary.gridWordEquiv T (stepBits hStep) bits)

theorem flatUnitWalk_law (htotal : ∑ i, r i = ∑ j, c j)
    (h : ¬ bothLarge r c) (x : States r c U L) (T hStep : ℕ) :
    letI := states_nonempty r c U L htotal
    mapLaw (uniformLaw (α := Fin (T * stepBits hStep) → Bool))
      (flatUnitWalk r c x T hStep) = selectedWalkLaw r c U L x T := by
  letI := states_nonempty r c U L htotal
  unfold flatUnitWalk
  rw [← map_equiv (GridBoundary.gridWordEquiv T (stepBits hStep)), uniform_equiv]
  change wordWalkLaw _ _ _ = _
  rw [wordWalkLaw_eq]
  unfold selectedWalkLaw selectedTransitionLaw
  rw [dif_neg (not_bothLarge_reference r c h)]
  exact congrArg (fun K => walkLaw K x T) (funext (unitBitStep_law r c htotal hStep))

def unitJointDraw (h : ¬ bothLarge r c) (x : States r c U L) (T hStep hTerminal : ℕ)
    (bits : Fin (attemptBits T hStep hTerminal) → Bool) : StateJoint r c U L :=
  let parts := splitWordEquiv (T * stepBits hStep) (f hTerminal) bits
  let z := flatUnitWalk r c x T hStep parts.1
  ⟨z, PhysicalEmptyCompletion.emptyCompletionOfNotBoth r c U L
    (not_bothLarge_reference r c h) z⟩

theorem unitJointDraw_law (htotal : ∑ i, r i = ∑ j, c j)
    (h : ¬ bothLarge r c) (x : States r c U L) (T hStep hTerminal : ℕ) :
    letI := states_nonempty r c U L htotal
    mapLaw (uniformLaw (α := Fin (attemptBits T hStep hTerminal) → Bool))
      (unitJointDraw r c h x T hStep hTerminal) = walkJointLaw r c U L x T := by
  letI := states_nonempty r c U L htotal
  let finish := fun z : States r c U L => PhysicalEmptyCompletion.emptyCompletionOfNotBoth
    r c U L (not_bothLarge_reference r c h) z
  let E := splitWordEquiv (T * stepBits hStep) (f hTerminal)
  let F := fun ab : (Fin (T * stepBits hStep) → Bool) × (Fin (f hTerminal) → Bool) =>
    let z := flatUnitWalk r c x T hStep ab.1
    (⟨z, finish z⟩ : StateJoint r c U L)
  have hu : equivLaw E (uniformLaw (α := Fin (attemptBits T hStep hTerminal) → Bool)) =
      productLaw (uniformLaw (α := Fin (T * stepBits hStep) → Bool))
        (uniformLaw (α := Fin (f hTerminal) → Bool)) :=
    (uniform_equiv E).trans
      (uniform_product (α := Fin (T * stepBits hStep) → Bool)
        (β := Fin (f hTerminal) → Bool)).symm
  have he : mapLaw (productLaw
      (uniformLaw (α := Fin (T * stepBits hStep) → Bool))
      (uniformLaw (α := Fin (f hTerminal) → Bool))) F =
      mapLaw (uniformLaw (α := Fin (attemptBits T hStep hTerminal) → Bool))
        (fun bits => F (E bits)) :=
    (congrArg (fun p => mapLaw p F) hu.symm).trans
      (map_equiv E (uniformLaw (α := Fin (attemptBits T hStep hTerminal) → Bool)) F)
  calc
    _ = mapLaw (productLaw (uniformLaw (α := Fin (T * stepBits hStep) → Bool))
        (uniformLaw (α := Fin (f hTerminal) → Bool))) F := he.symm
    _ = dependentJointLaw
        (mapLaw (uniformLaw (α := Fin (T * stepBits hStep) → Bool))
          (flatUnitWalk r c x T hStep))
        (fun z => mapLaw (uniformLaw (α := Fin (f hTerminal) → Bool)) (fun _ => finish z)) :=
      mapLaw_dependent_product
        (A := Fin (T * stepBits hStep) → Bool) (B := Fin (f hTerminal) → Bool)
        (X := States r c U L) (Y := Fibre r c U L)
        (uniformLaw (α := Fin (T * stepBits hStep) → Bool))
        (uniformLaw (α := Fin (f hTerminal) → Bool))
        (flatUnitWalk r c x T hStep) (fun z _ => finish z)
    _ = _ := by
      rw [flatUnitWalk_law r c htotal h]
      unfold walkJointLaw
      have hterminal :
          (fun z : States r c U L =>
            mapLaw (uniformLaw (α := Fin (f hTerminal) → Bool)) (fun _ => finish z)) =
          (fun z : States r c U L => uniformLaw (α := Fibre r c U L z)) := by
        funext z
        rw [mapLaw_constant]
        exact PhysicalEmptyCompletion.emptyCompletionOfNotBoth_pointLaw_uniform
          r c U L (not_bothLarge_reference r c h) z
      exact congrArg
        (fun q : (z : States r c U L) → RationalLaw (Fibre r c U L z) =>
          dependentJointLaw (selectedWalkLaw r c U L x T) q) hterminal

def unitOuterDraw (h : ¬ bothLarge r c) (x : States r c U L) (fallback : Table r c)
    (T R hStep hTerminal : ℕ)
    (bits : Fin (outerBits T R hStep hTerminal) → Bool) : Table r c :=
  wordRetry (fun word => PhysicalStationaryLaw.stateTrial r c U L
    (unitJointDraw r c h x T hStep hTerminal word)) fallback R
    (GridBoundary.gridWordEquiv R (attemptBits T hStep hTerminal) bits)

theorem unitOuterDraw_law (htotal : ∑ i, r i = ∑ j, c j)
    (h : ¬ bothLarge r c) (x : States r c U L) (fallback : Table r c)
    (T R hStep hTerminal : ℕ) :
    letI := states_nonempty r c U L htotal
    mapLaw (uniformLaw (α := Fin (outerBits T R hStep hTerminal) → Bool))
      (unitOuterDraw r c h x fallback T R hStep hTerminal) =
      PhysicalFiniteWalk.outerLaw r c U L x T R fallback := by
  letI := states_nonempty r c U L htotal
  unfold unitOuterDraw PhysicalReferenceBoolean.outerBits
  rw [← map_equiv (GridBoundary.gridWordEquiv R (attemptBits T hStep hTerminal)), uniform_equiv]
  change wordRetryLaw _ _ _ = _
  rw [wordRetryLaw_eq, ← retryLaw_map, unitJointDraw_law r c htotal h]
  rfl

/-- Both branches return an ordinary feasible table for every fixed word.
The branch, fallback and initial state depend only on the original margins. -/
def draw (htotal : ∑ i, r i = ∑ j, c j) (T R hStep hTerminal : ℕ)
    (bits : Fin (outerBits T R hStep hTerminal) → Bool) : Table r c :=
  if h : bothLarge r c then
    PhysicalReferenceBoolean.initializedDraw r c h.1 h.2 htotal T R hStep hTerminal bits
  else
    let fallback := GreedyFeasibleTable.table r c htotal
    unitOuterDraw r c h (initialState r c U L fallback) fallback T R hStep hTerminal bits

/-- Uniform finite-word error at the actual smaller scales. The empty branch
has zero completion error; the displayed bound is valid in either branch. -/
theorem draw_variation (htotal : ∑ i, r i = ∑ j, c j) (T R hStep hTerminal : ℕ) :
    letI := table_nonempty r c htotal
    (variation (mapLaw (uniformLaw (α := Fin (outerBits T R hStep hTerminal) → Bool))
        (draw r c htotal T R hStep hTerminal)) (uniformLaw (α := Table r c)) : ℝ) ≤
      Real.exp (-(R : ℝ) / successAllowance r c U) +
      (R : ℝ) * (massAllowance (J := Fin n) r U L * Real.exp (-(T : ℝ) / idealGapAllowance d)) +
      (R : ℝ) * ((T : ℝ) * (proposalAllowance d : ℝ) * (dyadic hStep : ℝ) +
        (dyadic hTerminal : ℝ)) := by
  letI := table_nonempty r c htotal
  by_cases h : bothLarge r c
  · have hdraw : draw r c htotal T R hStep hTerminal =
        PhysicalReferenceBoolean.initializedDraw r c h.1 h.2 htotal T R hStep hTerminal := by
      funext bits
      unfold draw
      rw [dite_eq_left h]
    rw [hdraw]
    exact PhysicalReferenceBoolean.initializedDraw_variation r c h.1 h.2 htotal T R hStep hTerminal
  · have hdraw : draw r c htotal T R hStep hTerminal =
        unitOuterDraw r c h (initialState r c U L (GreedyFeasibleTable.table r c htotal))
          (GreedyFeasibleTable.table r c htotal) T R hStep hTerminal := by
      funext bits
      unfold draw
      rw [dite_eq_right h]
    rw [hdraw, unitOuterDraw_law r c htotal h]
    have hb := idealOuterLaw_variation r c htotal (GreedyFeasibleTable.table r c htotal) T R
    change (variation (idealOuterLaw r c htotal (GreedyFeasibleTable.table r c htotal) T R)
      (uniformLaw (α := Table r c)) : ℝ) ≤ _
    refine hb.trans (le_add_of_nonneg_right ?_)
    have hγ : (0 : ℝ) ≤ (proposalAllowance d : ℝ) := by
      exact_mod_cast proposalAllowance_nonnegative d
    have hs : (0 : ℝ) ≤ (dyadic hStep : ℝ) := by exact_mod_cast (dyadic_positive hStep).le
    have ht : (0 : ℝ) ≤ (dyadic hTerminal : ℝ) := by exact_mod_cast (dyadic_positive hTerminal).le
    positivity

/-- Every equal-total natural margin pair, including empty index types and
zero margins, admits this finite-word dyadic-accurate sampler. -/
theorem draw_explicit_accuracy (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ) :
    let p := CompletionOuterSchedule.physicalSmallCount r c
    let base := CompletionOuterSchedule.physicalMassBase (J := Fin n) r
    let T := CompletionOuterSchedule.walkCount p d base h
    let R := CompletionOuterSchedule.restartCount p h
    let hStep := CompletionOuterSchedule.stepPrecision p d base h
    let hTerminal := CompletionOuterSchedule.terminalPrecision p h
    letI := table_nonempty r c htotal
    (variation (mapLaw (uniformLaw (α := Fin (outerBits T R hStep hTerminal) → Bool))
        (draw r c htotal T R hStep hTerminal)) (uniformLaw (α := Table r c)) : ℝ) ≤
      (dyadic h : ℝ) := by
  let p := CompletionOuterSchedule.physicalSmallCount r c
  let base := CompletionOuterSchedule.physicalMassBase (J := Fin n) r
  letI := table_nonempty r c htotal
  have hd : 1 ≤ d := by unfold dimensionAllowance; omega
  have hγ : (proposalAllowance d : ℝ) ≤ 1 := by
    have hh : (proposalAllowance d : ℝ) ≤ 1 / 2 := by
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        ((Rat.cast_le (K := ℝ)).mpr (proposalAllowance_le_half d hd))
    exact hh.trans (by norm_num)
  have hbound := draw_variation r c htotal
    (CompletionOuterSchedule.walkCount p d base h)
    (CompletionOuterSchedule.restartCount p h)
    (CompletionOuterSchedule.stepPrecision p d base h)
    (CompletionOuterSchedule.terminalPrecision p h)
  have heS : successAllowance r c U = (CompletionOuterSchedule.successFactor p : ℝ) := by
    simp only [successAllowance, CompletionOuterSchedule.successFactor, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow, p,
      CompletionOuterSchedule.physicalSmallCount]
  have heK : idealGapAllowance d = (CompletionOuterSchedule.gapFactor d : ℝ) := by
    simp only [idealGapAllowance, CompletionOuterSchedule.gapFactor, Nat.cast_mul,
      Nat.cast_ofNat, Nat.cast_pow]
  have heB : massAllowance (J := Fin n) r U L = (base : ℝ) ^ (2 * d) := by
    unfold massAllowance capacityBound
    congr 2
  rw [heS, heK, heB] at hbound
  exact hbound.trans (CompletionOuterSchedule.arithmetic_schedule p d base h hd
    (proposalAllowance d) hγ)

end
end Math115.PhysicalBooleanSampler
