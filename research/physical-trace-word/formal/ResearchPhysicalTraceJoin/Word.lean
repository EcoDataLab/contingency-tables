/-
SPDX-License-Identifier: Apache-2.0
A common fresh word realization of one actual incoming/exit law.
The supplied second-block width is fixed before the incoming experiment
and bounds every balanced exit bank. No efficient bound or width-selection
algorithm, repeated-walk reservation or encoded-cost result is supplied.
-/
import ResearchPhysicalTraceJoin.Actual
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordPadding

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open FirstSuccess ResidualMixture FairBits
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalCompletionOracle Math115.PhysicalStarTrial
open Math115.PhysicalStarRetry Math115.LegacyPhysicalCompletion
open Math115.RationalClockStep Math115.CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section

/-- Existing fixed-word independence, with an unchanged second word. -/
lemma fresh_split_law
    {X D : Type*} [Fintype X] [Fintype D] [DecidableEq X] [DecidableEq D]
    {A W : ℕ} (f : (Fin A → Bool) → X) (finish : X → (Fin W → Bool) → D) :
    mapLaw (uniformLaw (α := Fin (A + W) → Bool))
      (fun word => let parts := splitWordEquiv A W word
        finish (f parts.1) parts.2) =
      bindLaw (mapLaw (uniformLaw (α := Fin A → Bool)) f)
        (fun x => mapLaw (uniformLaw (α := Fin W → Bool)) (finish x)) := by
  have he := fixedWord_finish_law f (id : (Fin W → Bool) → (Fin W → Bool)) finish
  rw [mapLaw_id] at he
  exact he

def freshPrefixDraw {X D : Type*} {A W : ℕ}
    (k : X → ℕ) (hk : ∀ x, k x ≤ W) (f : (Fin A → Bool) → X)
    (g : (x : X) → (Fin (k x) → Bool) → D) (word : Fin (A + W) → Bool) : D :=
  let parts := splitWordEquiv A W word
  let x := f parts.1
  g x (prefixWord (hk x) parts.2)

/-- The state-dependent prefix is taken only from the fresh second block.
W and its bound are parameters fixed before the first draw. -/
theorem freshPrefixDraw_law
    {X D : Type*} [Fintype X] [Fintype D] [DecidableEq X] [DecidableEq D]
    {A W : ℕ} (k : X → ℕ) (hk : ∀ x, k x ≤ W)
    (f : (Fin A → Bool) → X) (g : (x : X) → (Fin (k x) → Bool) → D) :
    mapLaw (uniformLaw (α := Fin (A + W) → Bool)) (freshPrefixDraw k hk f g) =
      bindLaw (mapLaw (uniformLaw (α := Fin A → Bool)) f)
        (fun x => mapLaw (uniformLaw (α := Fin (k x) → Bool)) (g x)) := by
  calc
    _ = bindLaw (mapLaw (uniformLaw (α := Fin A → Bool)) f)
        (fun x => mapLaw (uniformLaw (α := Fin W → Bool))
          (fun bits => g x (prefixWord (hk x) bits))) :=
      fresh_split_law f (fun x bits => g x (prefixWord (hk x) bits))
    _ = _ := by
      congr 1
      funext x
      exact padded_draw_law (hk x) (g x)

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

local notation "dimension" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => Nat.clog 2 (32 * dimension^2)

def incomingWidth (d : DefectVertices r c U L) (N hIn : ℕ) : ℕ :=
  N * Math115.RationalClockProposal.precision (Math115.RationalClockProposal.denominator r c U) +
    bits r c U L hr hc d.val hIn

def balancedExitWidth (b : BalancedVertices r c U L) (J hExit : ℕ) : ℕ :=
  J * (s + bits r c U L hr hc b.val hExit)

/-- All balanced states, including actual-only arrivals, are covered by hW.
Defect outputs ignore this independent second block. -/
def commonExitDraw (d : DefectVertices r c U L) (J hExit W : ℕ)
    (hW : ∀ b : BalancedVertices r c U L, balancedExitWidth r c U L hr hc b J hExit ≤ W)
    (x : States r c U L) (word : Fin W → Bool) : DefectVertices r c U L :=
  if hb : IsBalanced r c U L x then
    flatExit r c U L hr hc ⟨x, hb⟩ hExit d J (prefixWord (hW ⟨x, hb⟩) word)
  else ⟨x, hb⟩

theorem commonExitDraw_law (d : DefectVertices r c U L) (J hExit W : ℕ)
    (hW : ∀ b : BalancedVertices r c U L, balancedExitWidth r c U L hr hc b J hExit ≤ W)
    (x : States r c U L) :
    mapLaw (uniformLaw (α := Fin W → Bool)) (commonExitDraw r c U L hr hc d J hExit W hW x) =
      actualExitKernel r c U L hr hc d J hExit x := by
  by_cases hb : IsBalanced r c U L x
  · let b : BalancedVertices r c U L := ⟨x, hb⟩
    change mapLaw (uniformLaw (α := Fin W → Bool))
      (commonExitDraw r c U L hr hc d J hExit W hW b.val) =
      actualExitKernel r c U L hr hc d J hExit b.val
    have he : commonExitDraw r c U L hr hc d J hExit W hW b.val =
        fun word => flatExit r c U L hr hc b hExit d J (prefixWord (hW b) word) := by
      funext word
      simp only [commonExitDraw, dite_eq_left b.property]
    rw [he, actualExitKernel_balanced r c U L hr hc d b J hExit]
    exact padded_draw_law (hW b) (flatExit r c U L hr hc b hExit d J)
  · let e : DefectVertices r c U L := ⟨x, hb⟩
    have he : commonExitDraw r c U L hr hc d J hExit W hW e.val = fun _ => e := by
      funext word
      simp only [commonExitDraw, dite_eq_right e.property]
    change mapLaw (uniformLaw (α := Fin W → Bool))
      (commonExitDraw r c U L hr hc d J hExit W hW e.val) =
      actualExitKernel r c U L hr hc d J hExit e.val
    rw [he, actualExitKernel_defect r c U L hr hc d e J hExit]
    exact mapLaw_constant _ e

/-- One word with a fixed incoming block and a disjoint common exit block.
The first segment runs the literal proposal/draw/list incoming step. -/
def joinedWord (d : DefectVertices r c U L) (N hIn J hExit W : ℕ)
    (hW : ∀ b : BalancedVertices r c U L, balancedExitWidth r c U L hr hc b J hExit ≤ W)
    (word : Fin (incomingWidth r c U L hr hc d N hIn + W) → Bool) : DefectVertices r c U L :=
  let parts := splitWordEquiv (incomingWidth r c U L hr hc d N hIn) W word
  commonExitDraw r c U L hr hc d J hExit W hW
    (incomingStep r c U L hr hc d N hIn parts.1) parts.2

/-- Padding introduces no approximation. No ideal draw is substituted for
either literal finite-word experiment. -/
theorem joinedWord_law (d : DefectVertices r c U L) (N hIn J hExit W : ℕ)
    (hW : ∀ b : BalancedVertices r c U L, balancedExitWidth r c U L hr hc b J hExit ≤ W) :
    mapLaw (uniformLaw (α := Fin (incomingWidth r c U L hr hc d N hIn + W) → Bool))
      (joinedWord r c U L hr hc d N hIn J hExit W hW) =
      actualJoinedLaw r c U L hr hc d N hIn J hExit := by
  calc
    _ = bindLaw (incomingLaw r c U L hr hc d N hIn)
        (fun x => mapLaw (uniformLaw (α := Fin W → Bool))
          (commonExitDraw r c U L hr hc d J hExit W hW x)) :=
      fresh_split_law (incomingStep r c U L hr hc d N hIn)
        (commonExitDraw r c U L hr hc d J hExit W hW)
    _ = _ := by
      unfold actualJoinedLaw
      congr 1
      funext x
      exact commonExitDraw_law r c U L hr hc d J hExit W hW x

theorem joinedWord_accuracy (htotal : (∑ i, r i) = ∑ j, c j)
    (hL : 7 ≤ L) (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d : DefectVertices r c U L) (N hIn J hExit W : ℕ)
    (hW : ∀ b : BalancedVertices r c U L, balancedExitWidth r c U L hr hc b J hExit ≤ W) :
    variation
      (mapLaw (uniformLaw (α := Fin (incomingWidth r c U L hr hc d N hIn + W) → Bool))
        (joinedWord r c U L hr hc d N hIn J hExit W hW))
      (idealJoinedLaw r c U L hr hc hp d) ≤
      (1 / 2 : ℚ)^N + dyadic hIn + exitAllowance dimension J hExit := by
  rw [joinedWord_law]
  exact actualJoinedLaw_accuracy r c U L hr hc htotal hL hp d N hIn J hExit

/-- A supplied common width turns the checked local one-step schedule into
one finite word. The width bound itself remains an explicit obligation. -/
theorem scheduledJoinedWord_accuracy (htotal : (∑ i, r i) = ∑ j, c j)
    (hL : 7 ≤ L) (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (d : DefectVertices r c U L) (t W : ℕ)
    (hW : ∀ b : BalancedVertices r c U L,
      balancedExitWidth r c U L hr hc b (Math115.PhysicalStarBudget.attempts dimension t)
        (Math115.PhysicalStarBudget.precision dimension t) ≤ W) :
    variation
      (mapLaw (uniformLaw (α := Fin (incomingWidth r c U L hr hc d (t + 2) (t + 2) + W) → Bool))
        (joinedWord r c U L hr hc d (t + 2) (t + 2)
          (Math115.PhysicalStarBudget.attempts dimension t)
          (Math115.PhysicalStarBudget.precision dimension t) W hW))
      (idealJoinedLaw r c U L hr hc hp d) ≤ dyadic t := by
  rw [joinedWord_law]
  exact scheduledJoinedLaw_accuracy r c U L hr hc htotal hL hp d t

end
end Math115.PhysicalTraceJoin
