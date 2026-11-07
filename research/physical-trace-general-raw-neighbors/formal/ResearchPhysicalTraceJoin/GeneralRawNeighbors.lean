/-
SPDX-License-Identifier: Apache-2.0
Computational code-neighbor selection for the rational clock. Runtime
selection stays on the existing validated list, in its original order.
Semantic decoding occurs only in proofs, not in the raw draw definitions.
-/
import ResearchRationalClock.Proposal

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms SmallContextCoordinates FirstPaperProfiles
open CompletionCounts FairBits ExactIntegerChoice
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalComputedProposal Math115.RationalClockProposal
open scoped BigOperators

/-- An ordinary integer bit decoder, with rejection only outside [0,V). -/
def rawClockIntervalTrial (V : ℕ) (word : Fin (Nat.clog 2 V) → Bool) : Option (Fin V) :=
  let j := OAI.MatchingFPRAS.StackAddition.value (List.ofFn word)
  if hj : j < V then some ⟨j, hj⟩ else none

/-- The extra option distinguishes exhausted interval rejection from an
accepted index. All complete bit blocks are reserved before selection. -/
def rawClockIndex (V N : ℕ) (word : Fin (N * Nat.clog 2 V) → Bool) : Option (Fin V) :=
  Math115.CompletionBooleanRetry.flatRetry
    (fun block => (rawClockIntervalTrial V block).map some) none N word

/-- Validated, deduplicated code-neighbor list and one optional index.
Unused list slots return none; they never trigger another interval trial. -/
def rawNeighborLookup (data : ProfileCheckData) {V : ℕ} (index : Option (Fin V)) :
    Option (List ℕ × List ℕ) :=
  index.bind (fun j => (codeNeighbors data)[j.val]?)

/-- Raw input and output state views are lists. No semantic state decoder
or enumeration is an operation of this finite-word program. -/
def rawClockNeighborDraw (data : ProfileCheckData) (V N : ℕ)
    (word : Fin (N * Nat.clog 2 V) → Bool) : Option (List ℕ × List ℕ) :=
  rawNeighborLookup data (rawClockIndex V N word)

noncomputable section
open scoped Classical

theorem rawClockIntervalTrial_eq (V : ℕ) (word : Fin (precision V) → Bool) :
    rawClockIntervalTrial V word = intervalWordTrial V word := by
  let choose : ℕ → Option (Fin V) := fun j =>
    if hj : j < V then some ⟨j, hj⟩ else none
  exact congrArg choose (ProfilePrograms.bitValue_eq_word (precision V) word)

theorem rawClockIndex_eq (V N : ℕ) (word : Fin (N * precision V) → Bool) :
    rawClockIndex V N word = cappedIndex V N word := by
  have he : rawClockIntervalTrial V = intervalWordTrial V :=
    funext (rawClockIntervalTrial_eq V)
  unfold rawClockIndex cappedIndex
  rw [he]
  rfl

private theorem map_filterMap_inverse {A B : Type*} (f : A → Option B) (g : B → A)
    (xs : List A) (h : ∀ a ∈ xs, ∃ b, f a = some b ∧ g b = a) :
    (xs.filterMap f).map g = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    obtain ⟨b, hb, hg⟩ := h a (by simp)
    have ht : ∀ a ∈ xs, ∃ b, f a = some b ∧ g b = a :=
      fun a ha => h a (by simp [ha])
    simp only [List.filterMap_cons, hb, List.map_cons, hg, ih ht]

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)

/-- Total validity of the existing list implies exact list equality after
encoding its typed interpretation. This preserves order, not just membership. -/
theorem physicalNeighbors_map_computedStateCode
    (htotal : (∑ i, r i) = ∑ j, c j) (x : States r c U L) :
    (physicalNeighbors r c U L x).map (computedStateCode r c U L) =
      codeNeighbors (SmallGraphProfiles.codeCheckData (computedCatalog r c U) (List.ofFn r) (List.ofFn c)
        U (computedStateCode r c U L x)) := by
  have ht := codeNeighbors_decode_total r c U L (computedCellEquiv r c U) htotal x
  have he := map_filterMap_inverse
    (decodeStateCode r c U L (computedCellEquiv r c U)) (computedStateCode r c U L)
    (codeNeighbors (stateCodeData r c U L (computedCellEquiv r c U) x)) (by
      intro v hv
      obtain ⟨y, hy⟩ := ht v hv
      exact ⟨y, hy, (decodeStateCode_eq_some_iff r c U L
        (computedCellEquiv r c U) v y).mp hy⟩)
  simpa only [physicalNeighbors, codeNeighborStates, stateCodeData,
    computedCellEquiv_catalog, computedStateCode] using he

/-- Lookup commutes at every natural index, including beyond the list. -/
theorem physicalNeighbors_getElem?_computedStateCode
    (htotal : (∑ i, r i) = ∑ j, c j) (x : States r c U L) (j : ℕ) :
    (codeNeighbors (SmallGraphProfiles.codeCheckData (computedCatalog r c U) (List.ofFn r) (List.ofFn c)
      U (computedStateCode r c U L x)))[j]? =
        ((physicalNeighbors r c U L x)[j]?).map (computedStateCode r c U L) := by
  rw [← physicalNeighbors_map_computedStateCode r c U L htotal x, List.getElem?_map]

/-- Optional rational-clock lookup, without decoding raw output at runtime. -/
theorem rawNeighborLookup_eq (htotal : (∑ i, r i) = ∑ j, c j)
    (x : States r c U L) {V : ℕ} (index : Option (Fin V)) :
    rawNeighborLookup (SmallGraphProfiles.codeCheckData (computedCatalog r c U) (List.ofFn r) (List.ofFn c)
      U (computedStateCode r c U L x)) index =
        (lookupIndex (physicalNeighbors r c U L x) index).map (computedStateCode r c U L) := by
  cases index with
  | none => rfl
  | some j => exact physicalNeighbors_getElem?_computedStateCode r c U L htotal x j.val

/-- Pointwise commuting equation for the new rational-clock proposal.
Rejections, unused-list holding and exhaustion all preserve none exactly. -/
theorem rawClockNeighborDraw_eq (htotal : (∑ i, r i) = ∑ j, c j)
    (x : DefectVertices r c U L) (N : ℕ)
    (word : Fin (N * precision (denominator r c U)) → Bool) :
    rawClockNeighborDraw
      (SmallGraphProfiles.codeCheckData (computedCatalog r c U) (List.ofFn r) (List.ofFn c)
        U (computedStateCode r c U L x.val)) (denominator r c U) N word =
      (physicalProposal r c U L x N word).map (computedStateCode r c U L) := by
  unfold rawClockNeighborDraw
  rw [rawClockIndex_eq]
  exact rawNeighborLookup_eq r c U L htotal x.val _

end
end Math115.PhysicalTraceJoin
