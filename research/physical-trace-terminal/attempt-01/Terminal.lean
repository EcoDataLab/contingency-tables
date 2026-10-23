/-
SPDX-License-Identifier: Apache-2.0
A fresh frozen completion draw after the literal defect walk. The target
is uniform on defect-labelled physical completion pairs, not original
tables. The displayed word length is a reserved input bank, not a claim
about inspected bits or encoded-machine running time.
-/
import ResearchPhysicalTraceJoin.Mixing
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordDependent

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open FirstSuccess ResidualMixture FairBits
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalStationarySuccess Math115.PhysicalStationaryLaw
open Math115.PhysicalCompletionWidth Math115.CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

local notation "dimension" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "p" => Fintype.card (Cells (firstPaperSmall r c U))

/-- The defect label is retained along with its actual physical completion. -/
abbrev DefectJoint := (d : DefectVertices r c U L) × Fibre r c U L d.val

def defectStationaryJointLaw [Nonempty (DefectVertices r c U L)] :
    RationalLaw (DefectJoint r c U L) :=
  dependentJointLaw (defectStationaryLaw r c U L)
    (fun d => uniformLaw (α := Fibre r c U L d.val))

/-- Count-weighted defects followed by a uniform same-defect fibre give a
uniform labelled joint. No table projection is part of this identity. -/
theorem defectStationaryJointLaw_uniform [Nonempty (DefectVertices r c U L)] :
    defectStationaryJointLaw r c U L = uniformLaw (α := DefectJoint r c U L) := by
  apply dependentJointLaw_uniform
  intro d
  rfl

/-- Only the fresh terminal bank is prefixed to the reached state's width. -/
def terminalCompletion (d : DefectVertices r c U L) (hTerm : ℕ)
    (word : Fin (uniformCompletionBits r c U L hTerm) → Bool) : Fibre r c U L d.val :=
  LegacyPhysicalCompletion.completionDraw r c U L hr hc d.val hTerm
    (prefixWord (completionBits_le_uniform r c U L hr hc d.val hTerm) word)

theorem terminalCompletion_law (d : DefectVertices r c U L) (hTerm : ℕ) :
    mapLaw (uniformLaw (α := Fin (uniformCompletionBits r c U L hTerm) → Bool))
      (terminalCompletion r c U L hr hc d hTerm) =
      LegacyPhysicalCompletion.completionLaw r c U L hr hc d.val hTerm :=
  padded_draw_law (completionBits_le_uniform r c U L hr hc d.val hTerm)
    (LegacyPhysicalCompletion.completionDraw r c U L hr hc d.val hTerm)

theorem terminalCompletion_accuracy (d : DefectVertices r c U L) (hTerm : ℕ) :
    variation
      (mapLaw (uniformLaw (α := Fin (uniformCompletionBits r c U L hTerm) → Bool))
        (terminalCompletion r c U L hr hc d hTerm))
      (uniformLaw (α := Fibre r c U L d.val)) ≤ dyadic hTerm := by
  rw [terminalCompletion_law]
  exact LegacyPhysicalCompletion.completionLaw_accuracy r c U L hr hc d.val hTerm

def terminalBankWidth (N hIn J hExit T hTerm : ℕ) : ℕ :=
  T * uniformStepWidth r c U L N hIn J hExit + uniformCompletionBits r c U L hTerm

def terminalJoinedWord (start : DefectVertices r c U L) (N hIn J hExit T hTerm : ℕ)
    (word : Fin (terminalBankWidth r c U L N hIn J hExit T hTerm) → Bool) :
    DefectJoint r c U L :=
  let parts := splitWordEquiv (T * uniformStepWidth r c U L N hIn J hExit)
    (uniformCompletionBits r c U L hTerm) word
  let d := joinedWalkWord r c U L hr hc start N hIn J hExit T parts.1
  ⟨d, terminalCompletion r c U L hr hc d hTerm parts.2⟩

def terminalJoinedLaw (start : DefectVertices r c U L) (N hIn J hExit T hTerm : ℕ) :
    RationalLaw (DefectJoint r c U L) :=
  dependentJointLaw
    (walkLaw (fun d => actualJoinedLaw r c U L hr hc d N hIn J hExit) start T)
    (fun d => LegacyPhysicalCompletion.completionLaw r c U L hr hc d.val hTerm)

/-- Existing dependent-product and word-padding laws identify both literal
programs. The terminal draw uses an independent, disjoint suffix. -/
theorem terminalJoinedWord_law (start : DefectVertices r c U L)
    (N hIn J hExit T hTerm : ℕ) :
    mapLaw (uniformLaw (α := Fin
      (terminalBankWidth r c U L N hIn J hExit T hTerm) → Bool))
      (terminalJoinedWord r c U L hr hc start N hIn J hExit T hTerm) =
      terminalJoinedLaw r c U L hr hc start N hIn J hExit T hTerm := by
  let A := T * uniformStepWidth r c U L N hIn J hExit
  let W := uniformCompletionBits r c U L hTerm
  let E := splitWordEquiv A W
  let F := fun ab : (Fin A → Bool) × (Fin W → Bool) =>
    let d := joinedWalkWord r c U L hr hc start N hIn J hExit T ab.1
    (⟨d, terminalCompletion r c U L hr hc d hTerm ab.2⟩ : DefectJoint r c U L)
  have hu : equivLaw E (uniformLaw (α := Fin (A + W) → Bool)) =
      productLaw (uniformLaw (α := Fin A → Bool))
        (uniformLaw (α := Fin W → Bool)) :=
    (uniform_equiv E).trans
      (uniform_product (α := Fin A → Bool) (β := Fin W → Bool)).symm
  have he : mapLaw (productLaw (uniformLaw (α := Fin A → Bool))
      (uniformLaw (α := Fin W → Bool))) F =
      mapLaw (uniformLaw (α := Fin (A + W) → Bool)) (fun word => F (E word)) :=
    (congrArg (fun q => mapLaw q F) hu.symm).trans
      (map_equiv E (uniformLaw (α := Fin (A + W) → Bool)) F)
  calc
    _ = mapLaw (productLaw (uniformLaw (α := Fin A → Bool))
        (uniformLaw (α := Fin W → Bool))) F := he.symm
    _ = dependentJointLaw
        (mapLaw (uniformLaw (α := Fin A → Bool))
          (joinedWalkWord r c U L hr hc start N hIn J hExit T))
        (fun d => mapLaw (uniformLaw (α := Fin W → Bool))
          (terminalCompletion r c U L hr hc d hTerm)) :=
      mapLaw_dependent_product
        (A := Fin A → Bool) (B := Fin W → Bool)
        (X := DefectVertices r c U L) (Y := fun d => Fibre r c U L d.val)
        (uniformLaw (α := Fin A → Bool)) (uniformLaw (α := Fin W → Bool))
        (joinedWalkWord r c U L hr hc start N hIn J hExit T)
        (fun d => terminalCompletion r c U L hr hc d hTerm)
    _ = _ := by
      dsimp only [A, W]
      rw [joinedWalkWord_law]
      have hterminal :
          (fun d : DefectVertices r c U L =>
            mapLaw (uniformLaw (α := Fin (uniformCompletionBits r c U L hTerm) → Bool))
              (terminalCompletion r c U L hr hc d hTerm)) =
          (fun d => LegacyPhysicalCompletion.completionLaw r c U L hr hc d.val hTerm) := by
        funext d
        exact terminalCompletion_law r c U L hr hc d hTerm
      rw [hterminal]
      rfl

/-- Uniform conditional completion adds its error without dividing by a
stationary mass or conditioning on a successful outer event. -/
theorem terminalJoinedLaw_variation [Nonempty (DefectVertices r c U L)]
    (start : DefectVertices r c U L) (N hIn J hExit T hTerm : ℕ) :
    variation (terminalJoinedLaw r c U L hr hc start N hIn J hExit T hTerm)
      (uniformLaw (α := DefectJoint r c U L)) ≤
      variation
        (walkLaw (fun d => actualJoinedLaw r c U L hr hc d N hIn J hExit) start T)
        (defectStationaryLaw r c U L) + dyadic hTerm := by
  rw [← defectStationaryJointLaw_uniform r c U L]
  exact variation_dependentJoint_uniform
    (walkLaw (fun d => actualJoinedLaw r c U L hr hc d N hIn J hExit) start T)
    (defectStationaryLaw r c U L)
    (fun d => LegacyPhysicalCompletion.completionLaw r c U L hr hc d.val hTerm)
    (fun d => uniformLaw (α := Fibre r c U L d.val)) (dyadic hTerm)
    (fun d => LegacyPhysicalCompletion.completionLaw_accuracy r c U L hr hc d.val hTerm)

/-- A literal bounded walk and one fresh frozen completion yield an
approximately uniform defect-labelled joint, with no output correction. -/
theorem scheduledTerminalJoinedWord_accuracy [Nonempty (DefectVertices r c U L)]
    (htotal : (∑ i, r i) = ∑ j, c j) (hU : 2 ≤ U) (hL : 7 ≤ L) (hp : 2 ≤ p)
    (start : DefectVertices r c U L) (t T hTerm : ℕ) :
    (variation
      (mapLaw (uniformLaw (α := Fin
        (terminalBankWidth r c U L (t + 2) (t + 2)
          (Math115.PhysicalStarBudget.attempts dimension t)
          (Math115.PhysicalStarBudget.precision dimension t) T hTerm) → Bool))
        (terminalJoinedWord r c U L hr hc start (t + 2) (t + 2)
          (Math115.PhysicalStarBudget.attempts dimension t)
          (Math115.PhysicalStarBudget.precision dimension t) T hTerm))
      (uniformLaw (α := DefectJoint r c U L)) : ℝ) ≤
      (T : ℝ) * (dyadic t : ℝ) +
      Math115.PhysicalFiniteWalk.massAllowance (J := Fin n) r U L *
        Real.exp (-(T : ℝ) / aggregateMixingAllowance r c U) + (dyadic hTerm : ℝ) := by
  rw [terminalJoinedWord_law]
  have hj := (Rat.cast_le (K := ℝ)).mpr
    (terminalJoinedLaw_variation r c U L hr hc start (t + 2) (t + 2)
      (Math115.PhysicalStarBudget.attempts dimension t)
      (Math115.PhysicalStarBudget.precision dimension t) T hTerm)
  simp only [Rat.cast_add] at hj
  have hw := scheduledJoinedWalkWord_mixing r c U L hr hc htotal hU hL hp start t T
  rw [joinedWalkWord_law] at hw
  exact hj.trans (add_le_add hw (le_refl _))

end
end Math115.PhysicalTraceJoin
