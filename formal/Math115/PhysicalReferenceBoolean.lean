/-
SPDX-License-Identifier: Apache-2.0
Fresh finite Boolean words for the computed-reference ideal-scale sampler.
This identifies the complete reference-branch word law. The encoded outer
loop, initialization and output realizers are separate machine-cost work.
-/
import Math115.PhysicalComputedProposal
import Math115.ListedLatticeCompletion
import Math115.CompletionOuterSchedule
import OAI.Combinatorics.ContingencyTables.Transport.WordCompletionStep
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordWalk
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordRejection

namespace Math115.PhysicalReferenceBoolean

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open SmallGraphProfiles CompletionCounts ProfilePrograms ReducedSmallChain
open PhysicalCompletionOracle PhysicalStationarySuccess PhysicalFiniteWalk
open PhysicalApproximateOracle PhysicalStateNonempty CompletionRetryBudget
open CompletionTranslation ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ}
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => IdealOracleScales.cutoff (I := Fin m) (J := Fin n)
local notation "L" => IdealOracleScales.padding (I := Fin m) (J := Fin n)
variable (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "s" => Nat.clog 2 (32 * d^2)
local notation "f" => PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r

/-- Each transition owns its proposal prefix and a separate completion word,
including transitions whose proposal is a hold. -/
def stepBits (h : ℕ) : ℕ := s + f h

def attemptBits (T hStep hTerminal : ℕ) : ℕ :=
  T * stepBits (n := n) r hStep + f hTerminal

def outerBits (T R hStep hTerminal : ℕ) : ℕ :=
  R * attemptBits (n := n) r T hStep hTerminal

/-- The computed neighbor proposal and actual listed completion use disjoint
uniform word segments at the current physical state. -/
def bitStep
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (h : ℕ) (z : States r c U L)
    (bits : Fin (stepBits (n := n) r h) → Bool) : States r c U L :=
  wordCompletionStep
    (referenceRows r c U L (capacity r c U L) (largeOptionEquiv r U hr none))
    (referenceColumns r c U L (capacity r c U L) (largeOptionEquiv c U hc none))
    (PhysicalComputedProposal.computedProposal r c U L)
    (fun z => ListedLatticeCompletion.referenceDraw r c hr hc z h) z bits

section BitStepRewriteProbe
attribute [local irreducible] FirstSuccess.mapLaw completionStepLaw

set_option maxHeartbeats 1000000 in
theorem bitStep_law
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (z : States r c U L) :
    mapLaw (uniformLaw (α := Fin (stepBits (n := n) r h) → Bool))
      (bitStep r c hr hc h z) =
      referenceStepLaw r c U L (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)
        (ListedLatticeCompletion.oracleFamily r c hr hc h (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)) z := by
  unfold bitStep stepBits
  rw [wordCompletionStep_law]
  have hp :
      (fun x : States r c U L => mapLaw (uniformLaw (α := Fin s → Bool))
        (PhysicalComputedProposal.computedProposal r c U L x)) =
      physicalProposalLaw r c U L :=
    funext (PhysicalComputedProposal.computedProposal_law r c U L htotal)
  have hf :
      (fun x : States r c U L => mapLaw (uniformLaw (α := Fin (f h) → Bool))
        (ListedLatticeCompletion.referenceDraw r c hr hc x h)) =
      ListedLatticeCompletion.oracleFamily r c hr hc h
        (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none) :=
    funext (fun x => ListedLatticeCompletion.referenceDraw_law r c hr hc x h)
  have hq := funext (fun x : States r c U L =>
    mapLaw_decidableEq_irrel
      (@Option.instDecidableEq (States r c U L) inferInstance)
      (inferInstance : DecidableEq (Option (States r c U L)))
      (uniformLaw (α := Fin s → Bool))
      (PhysicalComputedProposal.computedProposal r c U L x))
  unfold referenceStepLaw
  rw [hq, hp, hf]

end BitStepRewriteProbe

def flatWalk
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (x : States r c U L) (T h : ℕ)
    (bits : Fin (T * stepBits (n := n) r h) → Bool) : States r c U L :=
  wordWalk (bitStep r c hr hc h) x T
    (GridBoundary.gridWordEquiv T (stepBits (n := n) r h) bits)

theorem flatWalk_law
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (htotal : ∑ i, r i = ∑ j, c j)
    (x : States r c U L) (T h : ℕ) :
    mapLaw (uniformLaw (α := Fin (T * stepBits (n := n) r h) → Bool))
      (flatWalk r c hr hc x T h) =
      walkLaw (referenceStepLaw r c U L (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)
        (ListedLatticeCompletion.oracleFamily r c hr hc h (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none))) x T := by
  unfold flatWalk
  rw [← map_equiv (GridBoundary.gridWordEquiv T (stepBits (n := n) r h)), uniform_equiv]
  change wordWalkLaw _ _ _ = _
  rw [wordWalkLaw_eq]
  exact congrArg (fun K => walkLaw K x T) (funext (bitStep_law r c hr hc htotal h))

/-- Transport to reference coordinates and back preserves the actual
computed-list fibre law, including failed inner trials and their fallback. -/
lemma terminalLaw_eq
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (h : ℕ) (z : States r c U L) :
    referenceCompletionLaw r c U L (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)
      (ListedLatticeCompletion.oracleFamily r c hr hc h (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)) z =
      ListedLatticeCompletion.completionLaw r c hr hc z h := by
  apply RationalLaw.ext
  funext A
  simp only [referenceCompletionLaw, ListedLatticeCompletion.oracleFamily,
    equivLaw, Equiv.symm_symm, Equiv.apply_symm_apply]

/-- The terminal draw receives a fresh suffix after the adaptively obtained
state. Its precision and reservation can differ from the transition's. -/
def jointDraw
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (x : States r c U L) (T hStep hTerminal : ℕ)
    (bits : Fin (attemptBits (n := n) r T hStep hTerminal) → Bool) : StateJoint r c U L :=
  let parts := splitWordEquiv (T * stepBits (n := n) r hStep) (f hTerminal) bits
  let z := flatWalk r c hr hc x T hStep parts.1
  ⟨z, ListedLatticeCompletion.completionDraw r c hr hc z hTerminal parts.2⟩

theorem jointDraw_law
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (htotal : ∑ i, r i = ∑ j, c j)
    (x : States r c U L) (T hStep hTerminal : ℕ) :
    mapLaw (uniformLaw (α := Fin (attemptBits (n := n) r T hStep hTerminal) → Bool))
      (jointDraw r c hr hc x T hStep hTerminal) =
      approximateJointLaw r c U L
        (referenceStepLaw r c U L (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)
          (ListedLatticeCompletion.oracleFamily r c hr hc hStep (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)))
        (referenceCompletionLaw r c U L (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)
          (ListedLatticeCompletion.oracleFamily r c hr hc hTerminal (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none))) x T := by
  let E := splitWordEquiv (T * stepBits (n := n) r hStep) (f hTerminal)
  let F := fun ab : (Fin (T * stepBits (n := n) r hStep) → Bool) ×
      (Fin (f hTerminal) → Bool) =>
    let z := flatWalk r c hr hc x T hStep ab.1
    (⟨z, ListedLatticeCompletion.completionDraw r c hr hc z hTerminal ab.2⟩ : StateJoint r c U L)
  have hu : equivLaw E
      (uniformLaw (α := Fin (attemptBits (n := n) r T hStep hTerminal) → Bool)) =
      productLaw (uniformLaw (α := Fin (T * stepBits (n := n) r hStep) → Bool))
        (uniformLaw (α := Fin (f hTerminal) → Bool)) :=
    (uniform_equiv E).trans
      (uniform_product (α := Fin (T * stepBits (n := n) r hStep) → Bool)
        (β := Fin (f hTerminal) → Bool)).symm
  have he : mapLaw (productLaw
      (uniformLaw (α := Fin (T * stepBits (n := n) r hStep) → Bool))
      (uniformLaw (α := Fin (f hTerminal) → Bool))) F =
      mapLaw (uniformLaw (α := Fin (attemptBits (n := n) r T hStep hTerminal) → Bool))
        (fun bits => F (E bits)) :=
    (congrArg (fun p => mapLaw p F) hu.symm).trans
      (map_equiv E
        (uniformLaw (α := Fin (attemptBits (n := n) r T hStep hTerminal) → Bool)) F)
  calc
    _ = mapLaw (productLaw
        (uniformLaw (α := Fin (T * stepBits (n := n) r hStep) → Bool))
        (uniformLaw (α := Fin (f hTerminal) → Bool))) F := he.symm
    _ = dependentJointLaw
        (mapLaw (uniformLaw (α := Fin (T * stepBits (n := n) r hStep) → Bool))
          (flatWalk r c hr hc x T hStep))
        (fun z => mapLaw (uniformLaw (α := Fin (f hTerminal) → Bool))
          (ListedLatticeCompletion.completionDraw r c hr hc z hTerminal)) :=
      mapLaw_dependent_product
        (A := Fin (T * stepBits (n := n) r hStep) → Bool) (B := Fin (f hTerminal) → Bool)
        (X := States r c U L) (Y := Fibre r c U L)
        (uniformLaw (α := Fin (T * stepBits (n := n) r hStep) → Bool))
        (uniformLaw (α := Fin (f hTerminal) → Bool))
        (flatWalk r c hr hc x T hStep)
        (fun z => ListedLatticeCompletion.completionDraw r c hr hc z hTerminal)
    _ = _ := by
      rw [flatWalk_law r c hr hc htotal]
      unfold approximateJointLaw
      have hterminal :
          (fun z : States r c U L =>
            mapLaw (uniformLaw (α := Fin (f hTerminal) → Bool))
              (ListedLatticeCompletion.completionDraw r c hr hc z hTerminal)) =
          referenceCompletionLaw r c U L (largeOptionEquiv r U hr none)
            (largeOptionEquiv c U hc none)
            (ListedLatticeCompletion.oracleFamily r c hr hc hTerminal
              (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)) := by
        funext z
        change ListedLatticeCompletion.completionLaw r c hr hc z hTerminal = _
        exact (terminalLaw_eq r c hr hc hTerminal z).symm
      exact congrArg
        (fun q : (z : States r c U L) → RationalLaw (Fibre r c U L z) =>
          dependentJointLaw
            (walkLaw (referenceStepLaw r c U L (largeOptionEquiv r U hr none)
              (largeOptionEquiv c U hc none)
              (ListedLatticeCompletion.oracleFamily r c hr hc hStep
                (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none))) x T) q)
        hterminal

/-- Each attempt restarts from the same initial state and owns its entire
word. Unused suffix words are never recycled into subsequent attempts. -/
def outerDraw
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (x : States r c U L) (fallback : Table r c)
    (T R hStep hTerminal : ℕ)
    (bits : Fin (outerBits (n := n) r T R hStep hTerminal) → Bool) : Table r c :=
  wordRetry (fun word => PhysicalStationaryLaw.stateTrial r c U L
    (jointDraw r c hr hc x T hStep hTerminal word)) fallback R
    (GridBoundary.gridWordEquiv R (attemptBits (n := n) r T hStep hTerminal) bits)

theorem outerDraw_law
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (htotal : ∑ i, r i = ∑ j, c j)
    (x : States r c U L) (fallback : Table r c) (T R hStep hTerminal : ℕ) :
    mapLaw (uniformLaw (α := Fin (outerBits (n := n) r T R hStep hTerminal) → Bool))
      (outerDraw r c hr hc x fallback T R hStep hTerminal) =
      approximateOuterLaw r c U L
        (referenceStepLaw r c U L (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)
          (ListedLatticeCompletion.oracleFamily r c hr hc hStep (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)))
        (referenceCompletionLaw r c U L (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)
          (ListedLatticeCompletion.oracleFamily r c hr hc hTerminal (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none))) x T R fallback := by
  unfold outerDraw outerBits
  rw [← map_equiv (GridBoundary.gridWordEquiv R
    (attemptBits (n := n) r T hStep hTerminal)), uniform_equiv]
  change wordRetryLaw _ _ _ = _
  rw [wordRetryLaw_eq, ← retryLaw_map, jointDraw_law r c hr hc htotal]
  rfl

/-- The fallback and initial state are fixed by the original margins. No
completion witness or accuracy hypothesis is supplied by the caller. -/
def initializedDraw
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (htotal : ∑ i, r i = ∑ j, c j) (T R hStep hTerminal : ℕ)
    (bits : Fin (outerBits (n := n) r T R hStep hTerminal) → Bool) : Table r c :=
  let fallback := GreedyFeasibleTable.table r c htotal
  outerDraw r c hr hc (initialState r c U L fallback) fallback T R hStep hTerminal bits

theorem initializedDraw_law
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (htotal : ∑ i, r i = ∑ j, c j) (T R hStep hTerminal : ℕ) :
    mapLaw (uniformLaw (α := Fin (outerBits (n := n) r T R hStep hTerminal) → Bool))
      (initializedDraw r c hr hc htotal T R hStep hTerminal) =
      ListedLatticeCompletion.outerLaw r c hr hc htotal
        (GreedyFeasibleTable.table r c htotal) T R hStep hTerminal := by
  exact outerDraw_law r c hr hc htotal
    (initialState r c U L (GreedyFeasibleTable.table r c htotal))
    (GreedyFeasibleTable.table r c htotal) T R hStep hTerminal

theorem initializedDraw_variation
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (htotal : ∑ i, r i = ∑ j, c j)
    (T R hStep hTerminal : ℕ) :
    letI := table_nonempty r c htotal
    (variation (mapLaw
        (uniformLaw (α := Fin (outerBits (n := n) r T R hStep hTerminal) → Bool))
        (initializedDraw r c hr hc htotal T R hStep hTerminal))
      (uniformLaw (α := Table r c)) : ℝ) ≤
      Real.exp (-(R : ℝ) / successAllowance r c U) +
      (R : ℝ) * (massAllowance (J := Fin n) r U L * Real.exp (-(T : ℝ) / idealGapAllowance d)) +
      (R : ℝ) * ((T : ℝ) * (proposalAllowance d : ℝ) * (dyadic hStep : ℝ) +
        (dyadic hTerminal : ℝ)) := by
  letI := table_nonempty r c htotal
  rw [initializedDraw_law]
  exact ListedLatticeCompletion.outerLaw_variation r c hr hc htotal
    (GreedyFeasibleTable.table r c htotal) T R hStep hTerminal

/-- Finite-word accuracy with all numerical schedule conditions discharged.
Both computed large-index lists must be nonempty; the unit branch is separate. -/
theorem initializedDraw_explicit_accuracy
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ) :
    let p := CompletionOuterSchedule.physicalSmallCount r c
    let base := CompletionOuterSchedule.physicalMassBase (J := Fin n) r
    let T := CompletionOuterSchedule.walkCount p d base h
    let R := CompletionOuterSchedule.restartCount p h
    let hStep := CompletionOuterSchedule.stepPrecision p d base h
    let hTerminal := CompletionOuterSchedule.terminalPrecision p h
    letI := table_nonempty r c htotal
    (variation (mapLaw
        (uniformLaw (α := Fin (outerBits (n := n) r T R hStep hTerminal) → Bool))
        (initializedDraw r c hr hc htotal T R hStep hTerminal))
      (uniformLaw (α := Table r c)) : ℝ) ≤ (dyadic h : ℝ) := by
  let p := CompletionOuterSchedule.physicalSmallCount r c
  let base := CompletionOuterSchedule.physicalMassBase (J := Fin n) r
  letI := table_nonempty r c htotal
  have hd : 1 ≤ d := by unfold dimensionAllowance; omega
  have hγ : (proposalAllowance d : ℝ) ≤ 1 := by
    have hh : (proposalAllowance d : ℝ) ≤ 1 / 2 := by
      simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using
        ((Rat.cast_le (K := ℝ)).mpr (proposalAllowance_le_half d hd))
    exact hh.trans (by norm_num)
  have hbound := initializedDraw_variation r c hr hc htotal
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
end Math115.PhysicalReferenceBoolean
