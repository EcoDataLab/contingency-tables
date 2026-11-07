/-
SPDX-License-Identifier: Apache-2.0
An alternative reservation adapter bounded by the old width for the same actual joined law.
No existing schedules, raw sampler, completion draw, or probability target
are changed. The incoming actual-width split and final unused slack remain
in the same order. The optional terminal bank has the old terminal joint law.
No additional approximation or encoded-machine cost statement is made.
-/
import ResearchPhysicalTraceJoin.GeneralCompletionTightBudget
import ResearchPhysicalTraceJoin.Terminal

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open FirstSuccess ResidualMixture FairBits
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalCompletionWidth Math115.LegacyPhysicalCompletion
open Math115.RationalClockStep Math115.PhysicalStationarySuccess
open scoped BigOperators

/-- List arithmetic for an alternative exit reservation. -/
def rawTightCommonExitWidth (rs cs : List ℕ) (U L J hExit : ℕ) : ℕ :=
  J * (Nat.clog 2 (32 * (rawScheduleDimension rs cs)^2) +
    rawTightCompletionBits rs cs U L hExit)

/-- No maximum over physical states is computed. -/
def rawTightStepWidth (rs cs : List ℕ) (U L N hIn J hExit : ℕ) : ℕ :=
  N * Nat.clog 2 (rawScheduleClockDenominator rs cs U) +
    rawTightCompletionBits rs cs U L hIn + rawTightCommonExitWidth rs cs U L J hExit

/-- A walk bank and a fresh terminal bank using the alternative reservation. -/
def rawTightTerminalBankWidth (rs cs : List ℕ) (U L N hIn J hExit T hTerm : ℕ) : ℕ :=
  T * rawTightStepWidth rs cs U L N hIn J hExit + rawTightCompletionBits rs cs U L hTerm

theorem rawTightStepWidth_le_old (rs cs : List ℕ) (U L N hIn J hExit : ℕ) :
    rawTightStepWidth rs cs U L N hIn J hExit ≤ rawUniformStepWidth rs cs U L N hIn J hExit := by
  unfold rawTightStepWidth rawTightCommonExitWidth rawUniformStepWidth
  exact Nat.add_le_add
    (Nat.add_le_add_left (rawTightCompletionBits_le_old rs cs U L hIn) _)
    (Nat.mul_le_mul_left J (Nat.add_le_add_left
      (rawTightCompletionBits_le_old rs cs U L hExit) _))

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)

/-- Typed aliases remain ordinary natural arithmetic on supplied margins. -/
def tightCompletionBits (h : ℕ) : ℕ := rawTightCompletionBits (List.ofFn r) (List.ofFn c) U L h

def tightCommonExitWidth (J hExit : ℕ) : ℕ :=
  rawTightCommonExitWidth (List.ofFn r) (List.ofFn c) U L J hExit

def tightStepWidth (N hIn J hExit : ℕ) : ℕ :=
  rawTightStepWidth (List.ofFn r) (List.ofFn c) U L N hIn J hExit

def tightTerminalBankWidth (N hIn J hExit T hTerm : ℕ) : ℕ :=
  rawTightTerminalBankWidth (List.ofFn r) (List.ofFn c) U L N hIn J hExit T hTerm

open scoped Classical
noncomputable section
variable (hr : 0 < (largeIndices (U,List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U,List.ofFn c)).length)
local notation "dim" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => Nat.clog 2 (32*dim^2)

lemma tightCompletionBits_le_uniform (h : ℕ) :
    tightCompletionBits r c U L h ≤ uniformCompletionBits r c U L h := by
  exact (rawTightCompletionBits_le_old (List.ofFn r) (List.ofFn c) U L h).trans_eq
    (rawUniformCompletionBits_eq r c U L h)

lemma completionBits_le_tight (z : States r c U L) (h : ℕ) :
    bits r c U L hr hc z h ≤ tightCompletionBits r c U L h :=
  completionBits_le_rawTight r c U L hr hc z h

lemma tightCommonExitWidth_eq (J hExit : ℕ) :
    tightCommonExitWidth r c U L J hExit = J * (s + tightCompletionBits r c U L hExit) := by
  simp only [tightCommonExitWidth,rawTightCommonExitWidth,rawScheduleDimension_eq,tightCompletionBits]

lemma tightStepWidth_eq (N hIn J hExit : ℕ) :
    tightStepWidth r c U L N hIn J hExit =
      N * Math115.RationalClockProposal.precision (Math115.RationalClockProposal.denominator r c U) +
        tightCompletionBits r c U L hIn + tightCommonExitWidth r c U L J hExit := by
  simp only [tightStepWidth,rawTightStepWidth,rawScheduleClockDenominator_eq,
    Math115.RationalClockProposal.precision,tightCompletionBits,tightCommonExitWidth]

theorem tightCommonExitWidth_le_common (J hExit : ℕ) :
    tightCommonExitWidth r c U L J hExit ≤ commonExitWidth r c U L J hExit := by
  rw [tightCommonExitWidth_eq]
  unfold commonExitWidth
  exact Nat.mul_le_mul_left J (Nat.add_le_add_left (tightCompletionBits_le_uniform r c U L hExit) s)

theorem tightStepWidth_le_uniform (N hIn J hExit : ℕ) :
    tightStepWidth r c U L N hIn J hExit ≤ uniformStepWidth r c U L N hIn J hExit := by
  exact (rawTightStepWidth_le_old (List.ofFn r) (List.ofFn c) U L N hIn J hExit).trans_eq
    (rawUniformStepWidth_eq r c U L N hIn J hExit)

theorem balancedExitWidth_le_tight (b : BalancedVertices r c U L) (J hExit : ℕ) :
    balancedExitWidth r c U L hr hc b J hExit ≤ tightCommonExitWidth r c U L J hExit := by
  rw [tightCommonExitWidth_eq]
  unfold balancedExitWidth
  exact Nat.mul_le_mul_left J (Nat.add_le_add_left (completionBits_le_tight r c U L hr hc b.val hExit) s)

theorem joinedWidth_le_tight (d : DefectVertices r c U L) (N hIn J hExit : ℕ) :
    incomingWidth r c U L hr hc d N hIn + tightCommonExitWidth r c U L J hExit ≤
      tightStepWidth r c U L N hIn J hExit := by
  rw [tightStepWidth_eq]
  unfold incomingWidth
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (completionBits_le_tight r c U L hr hc d.val hIn) _) _

/-- The actual incoming block is followed immediately by the tight common
exit block. No source-dependent completion block is enlarged or moved. -/
def tightBoundedJoinedWord (d : DefectVertices r c U L) (N hIn J hExit : ℕ)
    (word : Fin (incomingWidth r c U L hr hc d N hIn + tightCommonExitWidth r c U L J hExit) → Bool) :
    DefectVertices r c U L :=
  joinedWord r c U L hr hc d N hIn J hExit (tightCommonExitWidth r c U L J hExit)
    (fun b => balancedExitWidth_le_tight r c U L hr hc b J hExit) word

theorem tightBoundedJoinedWord_law (d : DefectVertices r c U L) (N hIn J hExit : ℕ) :
    mapLaw (uniformLaw (α := Fin
      (incomingWidth r c U L hr hc d N hIn + tightCommonExitWidth r c U L J hExit) → Bool))
      (tightBoundedJoinedWord r c U L hr hc d N hIn J hExit) =
        actualJoinedLaw r c U L hr hc d N hIn J hExit :=
  joinedWord_law r c U L hr hc d N hIn J hExit (tightCommonExitWidth r c U L J hExit)
    (fun b => balancedExitWidth_le_tight r c U L hr hc b J hExit)

/-- Uniform width across sources; the sole unused padding is a final suffix
after the actual incoming block and tight common exit bank. -/
def tightUniformJoinedWord (d : DefectVertices r c U L) (N hIn J hExit : ℕ)
    (word : Fin (tightStepWidth r c U L N hIn J hExit) → Bool) : DefectVertices r c U L :=
  tightBoundedJoinedWord r c U L hr hc d N hIn J hExit
    (prefixWord (joinedWidth_le_tight r c U L hr hc d N hIn J hExit) word)

/-- Explicit source-dependent split with unused slack only at the end. -/
theorem tightUniformJoinedWord_split (d : DefectVertices r c U L) (N hIn J hExit : ℕ)
    (word : Fin (tightStepWidth r c U L N hIn J hExit) → Bool) :
    tightUniformJoinedWord r c U L hr hc d N hIn J hExit word =
      let activeWord := prefixWord (joinedWidth_le_tight r c U L hr hc d N hIn J hExit) word
      let parts := splitWordEquiv (incomingWidth r c U L hr hc d N hIn)
        (tightCommonExitWidth r c U L J hExit) activeWord
      commonExitDraw r c U L hr hc d J hExit (tightCommonExitWidth r c U L J hExit)
        (fun b => balancedExitWidth_le_tight r c U L hr hc b J hExit)
        (incomingStep r c U L hr hc d N hIn parts.1) parts.2 := rfl

/-- The new width changes only padding, exactly preserving the old actual law. -/
theorem tightUniformJoinedWord_law (d : DefectVertices r c U L) (N hIn J hExit : ℕ) :
    mapLaw (uniformLaw (α := Fin (tightStepWidth r c U L N hIn J hExit) → Bool))
      (tightUniformJoinedWord r c U L hr hc d N hIn J hExit) =
        actualJoinedLaw r c U L hr hc d N hIn J hExit :=
  (padded_draw_law (joinedWidth_le_tight r c U L hr hc d N hIn J hExit)
    (tightBoundedJoinedWord r c U L hr hc d N hIn J hExit)).trans
      (tightBoundedJoinedWord_law r c U L hr hc d N hIn J hExit)

theorem tightUniformJoinedWord_same_law (d : DefectVertices r c U L) (N hIn J hExit : ℕ) :
    mapLaw (uniformLaw (α := Fin (tightStepWidth r c U L N hIn J hExit) → Bool))
      (tightUniformJoinedWord r c U L hr hc d N hIn J hExit) =
    mapLaw (uniformLaw (α := Fin (uniformStepWidth r c U L N hIn J hExit) → Bool))
      (uniformJoinedWord r c U L hr hc d N hIn J hExit) :=
  (tightUniformJoinedWord_law r c U L hr hc d N hIn J hExit).trans
    (uniformJoinedWord_law r c U L hr hc d N hIn J hExit).symm

/-- Every reached source receives a fresh block of the smaller uniform width. -/
def tightJoinedWalkWord (start : DefectVertices r c U L) (N hIn J hExit T : ℕ)
    (word : Fin (T * tightStepWidth r c U L N hIn J hExit) → Bool) : DefectVertices r c U L :=
  flatWordWalk (fun d => tightUniformJoinedWord r c U L hr hc d N hIn J hExit) start T word

theorem tightJoinedWalkWord_law (start : DefectVertices r c U L) (N hIn J hExit T : ℕ) :
    mapLaw (uniformLaw (α := Fin (T * tightStepWidth r c U L N hIn J hExit) → Bool))
      (tightJoinedWalkWord r c U L hr hc start N hIn J hExit T) =
        walkLaw (fun d => actualJoinedLaw r c U L hr hc d N hIn J hExit) start T := by
  unfold tightJoinedWalkWord
  rw [flatWordWalk_law]
  have he : (fun d : DefectVertices r c U L =>
      mapLaw (uniformLaw (α := Fin (tightStepWidth r c U L N hIn J hExit) → Bool))
        (tightUniformJoinedWord r c U L hr hc d N hIn J hExit)) =
      (fun d => actualJoinedLaw r c U L hr hc d N hIn J hExit) := by
    funext d
    exact tightUniformJoinedWord_law r c U L hr hc d N hIn J hExit
  rw [he]

/-- The terminal sampler is the unchanged frozen completion on its actual
prefix of a smaller fresh terminal bank. -/
def tightTerminalCompletion (d : DefectVertices r c U L) (hTerm : ℕ)
    (word : Fin (tightCompletionBits r c U L hTerm) → Bool) : Fibre r c U L d.val :=
  completionDraw r c U L hr hc d.val hTerm
    (prefixWord (completionBits_le_tight r c U L hr hc d.val hTerm) word)

theorem tightTerminalCompletion_law (d : DefectVertices r c U L) (hTerm : ℕ) :
    mapLaw (uniformLaw (α := Fin (tightCompletionBits r c U L hTerm) → Bool))
      (tightTerminalCompletion r c U L hr hc d hTerm) = completionLaw r c U L hr hc d.val hTerm :=
  padded_draw_law (completionBits_le_tight r c U L hr hc d.val hTerm)
    (completionDraw r c U L hr hc d.val hTerm)

theorem tightTerminalCompletion_same_law (d : DefectVertices r c U L) (hTerm : ℕ) :
    mapLaw (uniformLaw (α := Fin (tightCompletionBits r c U L hTerm) → Bool))
      (tightTerminalCompletion r c U L hr hc d hTerm) =
    mapLaw (uniformLaw (α := Fin (uniformCompletionBits r c U L hTerm) → Bool))
      (terminalCompletion r c U L hr hc d hTerm) :=
  (tightTerminalCompletion_law r c U L hr hc d hTerm).trans
    (terminalCompletion_law r c U L hr hc d hTerm).symm

theorem tightTerminalBankWidth_le_old (N hIn J hExit T hTerm : ℕ) :
    tightTerminalBankWidth r c U L N hIn J hExit T hTerm ≤
      terminalBankWidth r c U L N hIn J hExit T hTerm := by
  unfold tightTerminalBankWidth rawTightTerminalBankWidth terminalBankWidth
  exact Nat.add_le_add (Nat.mul_le_mul_left T (tightStepWidth_le_uniform r c U L N hIn J hExit))
    (tightCompletionBits_le_uniform r c U L hTerm)

/-- A disjoint alternative walk bank followed by a fresh terminal completion;
this produces the same labelled joint law, before any outer correction. -/
def tightTerminalJoinedWord (start : DefectVertices r c U L) (N hIn J hExit T hTerm : ℕ)
    (word : Fin (tightTerminalBankWidth r c U L N hIn J hExit T hTerm) → Bool) : DefectJoint r c U L :=
  let parts := splitWordEquiv (T * tightStepWidth r c U L N hIn J hExit)
    (tightCompletionBits r c U L hTerm) word
  let d := tightJoinedWalkWord r c U L hr hc start N hIn J hExit T parts.1
  ⟨d,tightTerminalCompletion r c U L hr hc d hTerm parts.2⟩

theorem tightTerminalJoinedWord_law (start : DefectVertices r c U L) (N hIn J hExit T hTerm : ℕ) :
    mapLaw (uniformLaw (α := Fin (tightTerminalBankWidth r c U L N hIn J hExit T hTerm) → Bool))
      (tightTerminalJoinedWord r c U L hr hc start N hIn J hExit T hTerm) =
        terminalJoinedLaw r c U L hr hc start N hIn J hExit T hTerm := by
  let A := T * tightStepWidth r c U L N hIn J hExit
  let W := tightCompletionBits r c U L hTerm
  let E := splitWordEquiv A W
  let F := fun ab : (Fin A → Bool) × (Fin W → Bool) =>
    let d := tightJoinedWalkWord r c U L hr hc start N hIn J hExit T ab.1
    (⟨d,tightTerminalCompletion r c U L hr hc d hTerm ab.2⟩ : DefectJoint r c U L)
  have hu : equivLaw E (uniformLaw (α := Fin (A+W) → Bool)) =
      productLaw (uniformLaw (α := Fin A → Bool)) (uniformLaw (α := Fin W → Bool)) :=
    (uniform_equiv E).trans (uniform_product (α := Fin A → Bool) (β := Fin W → Bool)).symm
  have he : mapLaw (productLaw (uniformLaw (α := Fin A → Bool))
      (uniformLaw (α := Fin W → Bool))) F =
      mapLaw (uniformLaw (α := Fin (A+W) → Bool)) (fun word => F (E word)) :=
    (congrArg (fun q => mapLaw q F) hu.symm).trans
      (map_equiv E (uniformLaw (α := Fin (A+W) → Bool)) F)
  calc
    _ = mapLaw (productLaw (uniformLaw (α := Fin A → Bool))
        (uniformLaw (α := Fin W → Bool))) F := he.symm
    _ = dependentJointLaw
        (mapLaw (uniformLaw (α := Fin A → Bool))
          (tightJoinedWalkWord r c U L hr hc start N hIn J hExit T))
        (fun d => mapLaw (uniformLaw (α := Fin W → Bool))
          (tightTerminalCompletion r c U L hr hc d hTerm)) :=
      mapLaw_dependent_product (A := Fin A → Bool) (B := Fin W → Bool)
        (X := DefectVertices r c U L) (Y := fun d => Fibre r c U L d.val)
        (uniformLaw (α := Fin A → Bool)) (uniformLaw (α := Fin W → Bool))
        (tightJoinedWalkWord r c U L hr hc start N hIn J hExit T)
        (fun d => tightTerminalCompletion r c U L hr hc d hTerm)
    _ = _ := by
      dsimp only [A,W]
      rw [tightJoinedWalkWord_law]
      have ht : (fun d : DefectVertices r c U L =>
          mapLaw (uniformLaw (α := Fin (tightCompletionBits r c U L hTerm) → Bool))
            (tightTerminalCompletion r c U L hr hc d hTerm)) =
          (fun d => completionLaw r c U L hr hc d.val hTerm) := by
        funext d
        exact tightTerminalCompletion_law r c U L hr hc d hTerm
      rw [ht]
      rfl

theorem tightTerminalJoinedWord_same_law (start : DefectVertices r c U L) (N hIn J hExit T hTerm : ℕ) :
    mapLaw (uniformLaw (α := Fin (tightTerminalBankWidth r c U L N hIn J hExit T hTerm) → Bool))
      (tightTerminalJoinedWord r c U L hr hc start N hIn J hExit T hTerm) =
    mapLaw (uniformLaw (α := Fin (terminalBankWidth r c U L N hIn J hExit T hTerm) → Bool))
      (terminalJoinedWord r c U L hr hc start N hIn J hExit T hTerm) :=
  (tightTerminalJoinedWord_law r c U L hr hc start N hIn J hExit T hTerm).trans
    (terminalJoinedWord_law r c U L hr hc start N hIn J hExit T hTerm).symm

end
end Math115.PhysicalTraceJoin
