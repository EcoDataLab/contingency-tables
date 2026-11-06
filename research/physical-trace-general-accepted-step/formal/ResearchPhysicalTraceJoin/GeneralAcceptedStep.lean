/-
SPDX-License-Identifier: Apache-2.0
Raw accepted rational-clock incoming step, using the original frozen
source completion and translation test. This is not the balanced-star
exit or the complete joined defect trace; no probability proof is repeated.
-/
import ResearchPhysicalTraceJoin.GeneralRawNeighbors
import ResearchPhysicalTraceJoin.GeneralCompletionCode
import ResearchRationalClockStep.Step
import OAI.Combinatorics.ContingencyTables.Machines.FiniteWordWalk

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms FairBits FirstSuccess
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalComputedProposal Math115.LegacyPhysicalCompletion
open Math115.RationalClockProposal Math115.RationalClockStep
open scoped BigOperators

/-- Total raw word reader. Missing input bits are zero; the correspondence
theorems below provide the complete reserved word, so no default is used. -/
def rawBoolWord (k : ℕ) (word : List Bool) : Fin k → Bool :=
  fun i => word[i.val]?.getD false

/-- The same translation test as the typed step. A missing proposal or a
failed source-to-candidate translation retains the original source code. -/
def rawAcceptedCandidate (rs cs : List ℕ) (U L : ℕ) (source : List ℕ × List ℕ)
    (candidate : Option (List ℕ × List ℕ)) (residual : MatrixCode) : List ℕ × List ℕ :=
  match candidate with
  | none => source
  | some target =>
    if translationValid ((rawCoarseMargins rs cs U L source,
        rawCoarseMargins rs cs U L target), residual)
    then target else source

/-- A missing candidate returns before asking for a completion. A present
candidate is checked against a frozen draw at the original source. -/
def rawAcceptedCompletion (rs cs : List ℕ) (U L : ℕ) (source : List ℕ × List ℕ)
    (candidate : Option (List ℕ × List ℕ)) (h : ℕ) (word : List Bool) : List ℕ × List ℕ :=
  match candidate with
  | none => source
  | some target => rawAcceptedCandidate rs cs U L source (some target)
      (rawCompletionResidual rs cs U L source h word)

/-- Proposal bits precede the actual source completion block. The frozen
draw uses the source margins, including when the candidate is balanced.
Any trailing reserved suffix is ignored by rawCompletionResidual. -/
def rawIncomingAcceptedStep (rs cs : List ℕ) (U L V N h : ℕ)
    (source : List ℕ × List ℕ) (word : List Bool) : List ℕ × List ℕ :=
  let proposalWidth := N * Nat.clog 2 V
  let candidate := rawClockNeighborDraw
    (SmallGraphProfiles.codeCheckData (smallCellCatalog ((rs, cs), U)) rs cs U source)
    V N (rawBoolWord proposalWidth (word.take proposalWidth))
  rawAcceptedCompletion rs cs U L source candidate h (word.drop proposalWidth)

/-- Raw iteration over supplied blocks, with the current raw state passed
to each next step. A full joined trace still needs its own step bridge. -/
def rawAcceptedWalk (step : (List ℕ × List ℕ) → List Bool → (List ℕ × List ℕ))
    (start : List ℕ × List ℕ) (words : List (List Bool)) : List ℕ × List ℕ :=
  words.foldl step start

noncomputable section
open scoped Classical

theorem rawBoolWord_ofFn (k : ℕ) (word : Fin k → Bool) :
    rawBoolWord k (List.ofFn word) = word := by
  funext i
  simp only [rawBoolWord, List.getElem?_ofFn, i.isLt, dite_true, Option.getD_some]

theorem rawAcceptedCompletion_eq (rs cs : List ℕ) (U L : ℕ) (source : List ℕ × List ℕ)
    (candidate : Option (List ℕ × List ℕ)) (h : ℕ) (word : List Bool) :
    rawAcceptedCompletion rs cs U L source candidate h word =
      rawAcceptedCandidate rs cs U L source candidate
        (rawCompletionResidual rs cs U L source h word) := by
  cases candidate <;> rfl

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

/-- Acceptance is pointwise arithmetic on raw source and target margins;
there is no runtime semantic decoding of either candidate or completion. -/
theorem rawAcceptedCandidate_eq (source : States r c U L)
    (candidate : Option (States r c U L)) (residual : MatrixCode) :
    rawAcceptedCandidate (List.ofFn r) (List.ofFn c) U L
      (computedStateCode r c U L source) (candidate.map (computedStateCode r c U L)) residual =
    computedStateCode r c U L
      (match candidate with
      | none => source
      | some target =>
        if translationValid
          (((List.ofFn (coarseRows r c U L hr source),
              List.ofFn (coarseColumns r c U L hc source)),
            (List.ofFn (coarseRows r c U L hr target),
              List.ofFn (coarseColumns r c U L hc target))), residual)
        then target else source) := by
  cases candidate with
  | none => rfl
  | some target =>
    simp only [rawAcceptedCandidate, Option.map_some,
      rawCoarseMargins_eq r c U L hr hc source,
      rawCoarseMargins_eq r c U L hr hc target]
    split_ifs <;> rfl

/-- Exact incoming-step correspondence on the same complete word. The
completion suffix starts after the capped clock reservation, and source
completion size is recomputed from the raw source code. -/
theorem rawIncomingAcceptedStep_eq
    (htotal : (∑ i, r i) = ∑ j, c j) (source : DefectVertices r c U L) (N h : ℕ)
    (word : Fin (N * precision (denominator r c U) + bits r c U L hr hc source.val h) → Bool) :
    rawIncomingAcceptedStep (List.ofFn r) (List.ofFn c) U L
      (denominator r c U) N h (computedStateCode r c U L source.val) (List.ofFn word) =
        computedStateCode r c U L (incomingStep r c U L hr hc source N h word) := by
  let parts := splitWordEquiv (N * precision (denominator r c U))
    (bits r c U L hr hc source.val h) word
  have hp := rawClockNeighborDraw_eq r c U L htotal source N parts.1
  have htake : (List.ofFn word).take (N * Nat.clog 2 (denominator r c U)) =
      List.ofFn parts.1 := ofFn_split_take word
  have hdrop : (List.ofFn word).drop (N * Nat.clog 2 (denominator r c U)) =
      List.ofFn parts.2 := ofFn_split_drop word
  have hread : rawBoolWord (N * Nat.clog 2 (denominator r c U))
      (List.ofFn parts.1) = parts.1 := rawBoolWord_ofFn _ parts.1
  unfold rawIncomingAcceptedStep
  dsimp only
  rw [htake, hread, rawAcceptedCompletion_eq]
  change rawAcceptedCandidate _ _ _ _ _
    (rawClockNeighborDraw
      (SmallGraphProfiles.codeCheckData (computedCatalog r c U) (List.ofFn r) (List.ofFn c)
        U (computedStateCode r c U L source.val)) (denominator r c U) N parts.1) _ = _
  rw [hp, hdrop]
  unfold rawCompletionResidual
  rw [rawCoarseMargins_eq r c U L hr hc source.val,
    rawCompletionBits_eq r c U L hr hc source.val h]
  rw [List.take_of_length_le (by simp only [List.length_ofFn, le_refl])]
  exact rawAcceptedCandidate_eq r c U L hr hc source.val
    (physicalProposal r c U L source N parts.1) _

/-- A step commuting equation lifts to arbitrary fixed-word iteration.
This generic theorem does not substitute incoming steps for joined steps. -/
theorem rawAcceptedWalk_eq_wordWalk {X : Type*} {B : ℕ}
    (encode : X → List ℕ × List ℕ)
    (step : X → (Fin B → Bool) → X)
    (rawStep : (List ℕ × List ℕ) → List Bool → (List ℕ × List ℕ))
    (hstep : ∀ x word, rawStep (encode x) (List.ofFn word) = encode (step x word))
    (start : X) (T : ℕ) (words : Fin T → Fin B → Bool) :
    rawAcceptedWalk rawStep (encode start) (List.ofFn (fun i => List.ofFn (words i))) =
      encode (wordWalk step start T words) := by
  induction T with
  | zero => rfl
  | succ T ih =>
    unfold rawAcceptedWalk at ih ⊢
    rw [List.ofFn_succ', List.concat_eq_append, List.foldl_append]
    change rawStep
      ((List.ofFn (fun i => List.ofFn ((Fin.init words) i))).foldl rawStep (encode start))
      (List.ofFn (words (Fin.last T))) = _
    rw [ih (Fin.init words), hstep]
    rfl

end
end Math115.PhysicalTraceJoin
