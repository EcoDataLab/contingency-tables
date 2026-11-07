/-
SPDX-License-Identifier: Apache-2.0
Raw dyadic balanced-star trial and first-success fixed blocks. The frozen
completion belongs to the balanced source. The original entering defect is
the all-failure fallback. This is a pointwise code seam, not a cost theorem.
-/
import ResearchPhysicalTraceJoin.GeneralAcceptedStep
import Math115.LatticeSamplerPreparation
import ResearchPhysicalStarRetry.Exit

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open FirstSuccess ResidualMixture FairBits
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalComputedProposal Math115.LegacyPhysicalCompletion
open Math115.CompletionBooleanRetry Math115.PhysicalStarTrial Math115.PhysicalStarRetry
open scoped BigOperators

/-- The inherited dyadic list proposal, including its unused-slot none. -/
def rawDyadicNeighborDraw (rs cs : List ℕ) (U d : ℕ) (source : List ℕ × List ℕ)
    (word : List Bool) : Option (List ℕ × List ℕ) :=
  codeNeighborProposal (SmallGraphProfiles.codeCheckData
    (smallCellCatalog ((rs,cs),U)) rs cs U source, word.take (Nat.clog 2 (32*d^2)))

/-- The proposal prefix is dyadic, and the completion suffix is frozen at
source even when the candidate has different residual margins. -/
def rawStarStep (rs cs : List ℕ) (U L d h : ℕ) (source : List ℕ × List ℕ)
    (word : List Bool) : List ℕ × List ℕ :=
  rawAcceptedCompletion rs cs U L source (rawDyadicNeighborDraw rs cs U d source word)
    h (word.drop (Nat.clog 2 (32*d^2)))

/-- Balanced outputs, including the held balanced source, are failures. Returning the entering defect
is a success whenever the projected output is defective. -/
def rawDefectProjection (U : ℕ) (state : List ℕ × List ℕ) : Option (List ℕ × List ℕ) :=
  if balancedTest (state,U) then none else some state

def rawStarTrial (rs cs : List ℕ) (U L d h : ℕ) (source : List ℕ × List ℕ)
    (word : List Bool) : Option (List ℕ × List ℕ) :=
  rawDefectProjection U (rawStarStep rs cs U L d h source word)

/-- Structural first success over blocks, advancing only on none. -/
def rawFirstSuccess {A : Type*} (trial : List Bool → Option A) (fallback : A) :
    List (List Bool) → A
  | [] => fallback
  | block :: rest => match trial block with
    | some value => value
    | none => rawFirstSuccess trial fallback rest

/-- Blocks remain in their original flat-word order. -/
def rawFixedBlocks (J q : ℕ) (word : List Bool) : List (List Bool) :=
  (List.range J).map (fun j => (word.drop (q*j)).take q)

/-- Exactly J source-width blocks are reserved, retaining the original
entering defect on total failure and accepting fallback-valued successes. -/
def rawStarExit (rs cs : List ℕ) (U L d h : ℕ)
    (source entering : List ℕ × List ℕ) (J : ℕ) (word : List Bool) : List ℕ × List ℕ :=
  rawFirstSuccess (rawStarTrial rs cs U L d h source) entering
    (rawFixedBlocks J (Nat.clog 2 (32*d^2) + rawCompletionBits rs cs U L source h) word)

noncomputable section
open scoped Classical
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U,List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U,List.ofFn c)).length)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => Nat.clog 2 (32*d^2)

/-- The ordinary list test is exactly semantic balance on stored views. -/
theorem rawBalancedTest_eq (state : States r c U L) :
    balancedTest (computedStateCode r c U L state,U) = true ↔ IsBalanced r c U L state :=
  Math115.LatticeSamplerPreparation.balancedTest_stateCode r c U L state

theorem rawDefectProjection_eq (state : States r c U L) :
    rawDefectProjection U (computedStateCode r c U L state) =
      (defectProjection r c U L state).map (fun e => computedStateCode r c U L e.val) := by
  by_cases hb : IsBalanced r c U L state
  · have ht := (rawBalancedTest_eq r c U L state).mpr hb
    simp [rawDefectProjection, ht, defectProjection, hb]
  · have ht : balancedTest (computedStateCode r c U L state,U) = false :=
      Bool.eq_false_iff.mpr (fun ht => hb ((rawBalancedTest_eq r c U L state).mp ht))
    simp [rawDefectProjection, ht, defectProjection, hb]

/-- Code selection follows the exact inherited list order. Semantic
validation is used only to prove that re-encoding recovers the raw choice. -/
theorem rawDyadicNeighborDraw_eq (htotal : (∑ i,r i) = ∑ j,c j)
    (state : States r c U L) (word : Fin s → Bool) :
    rawDyadicNeighborDraw (List.ofFn r) (List.ofFn c) U d
      (computedStateCode r c U L state) (List.ofFn word) =
        (computedProposal r c U L state word).map (computedStateCode r c U L) := by
  unfold rawDyadicNeighborDraw
  rw [List.take_of_length_le (by simp only [List.length_ofFn,le_refl])]
  change codeNeighborProposal (SmallGraphProfiles.codeCheckData (computedCatalog r c U)
    (List.ofFn r) (List.ofFn c) U (computedStateCode r c U L state),List.ofFn word) = _
  rw [computedProposal_apply]
  have hd : Math115.PhysicalComputedProposal.stateCodeData r c U L (computedCellEquiv r c U) state =
      SmallGraphProfiles.codeCheckData (computedCatalog r c U) (List.ofFn r) (List.ofFn c)
        U (computedStateCode r c U L state) := by
    unfold Math115.PhysicalComputedProposal.stateCodeData
    rw [computedCellEquiv_catalog]
    rfl
  rw [←hd]
  let data := Math115.PhysicalComputedProposal.stateCodeData r c U L (computedCellEquiv r c U) state
  have ht := codeNeighbors_decode_total r c U L (computedCellEquiv r c U) htotal state
  change codeNeighborProposal (data,List.ofFn word) =
    ((codeNeighborProposal (data,List.ofFn word)).bind
      (decodeStateCode r c U L (computedCellEquiv r c U))).map (computedStateCode r c U L)
  cases hp : codeNeighborProposal (data,List.ofFn word) with
  | none => rfl
  | some code =>
    have hm : code ∈ codeNeighbors data := by
      unfold codeNeighborProposal at hp
      exact List.mem_of_getElem? hp
    obtain ⟨target,hy⟩ := ht code hm
    simp only [Option.bind_some,hy,Option.map_some,Option.some.injEq]
    exact (decodeStateCode_eq_some_iff r c U L (computedCellEquiv r c U) code target).mp hy |>.symm

/-- Fixed source width and literal translation Boolean match actualStep. -/
theorem rawStarStep_eq (htotal : (∑ i,r i) = ∑ j,c j)
    (b : BalancedVertices r c U L) (h : ℕ)
    (word : Fin (s + bits r c U L hr hc b.val h) → Bool) :
    rawStarStep (List.ofFn r) (List.ofFn c) U L d h
      (computedStateCode r c U L b.val) (List.ofFn word) =
        computedStateCode r c U L (actualStep r c U L hr hc b h word) := by
  let parts := splitWordEquiv s (bits r c U L hr hc b.val h) word
  have htake : (List.ofFn word).take s = List.ofFn parts.1 := ofFn_split_take word
  have hdrop : (List.ofFn word).drop s = List.ofFn parts.2 := ofFn_split_drop word
  have hp : rawDyadicNeighborDraw (List.ofFn r) (List.ofFn c) U d
      (computedStateCode r c U L b.val) (List.ofFn word) =
      rawDyadicNeighborDraw (List.ofFn r) (List.ofFn c) U d
        (computedStateCode r c U L b.val) (List.ofFn parts.1) := by
    unfold rawDyadicNeighborDraw
    rw [htake,List.take_of_length_le (by simp only [List.length_ofFn,le_refl])]
  unfold rawStarStep
  rw [hp,rawDyadicNeighborDraw_eq r c U L htotal b.val parts.1,hdrop,
    rawAcceptedCompletion_eq]
  unfold rawCompletionResidual
  rw [rawCoarseMargins_eq r c U L hr hc b.val,
    rawCompletionBits_eq r c U L hr hc b.val h,
    List.take_of_length_le (by simp only [List.length_ofFn,le_refl])]
  exact rawAcceptedCandidate_eq r c U L hr hc b.val (computedProposal r c U L b.val parts.1) _

theorem rawStarTrial_eq (htotal : (∑ i,r i) = ∑ j,c j)
    (b : BalancedVertices r c U L) (h : ℕ)
    (word : Fin (s + bits r c U L hr hc b.val h) → Bool) :
    rawStarTrial (List.ofFn r) (List.ofFn c) U L d h
      (computedStateCode r c U L b.val) (List.ofFn word) =
        (actualTrial r c U L hr hc b h word).map (fun e => computedStateCode r c U L e.val) := by
  unfold rawStarTrial
  rw [rawStarStep_eq r c U L hr hc htotal b h word,rawDefectProjection_eq]
  rfl

lemma rawFixedBlocks_ofFn (J q : ℕ) (word : Fin (J*q) → Bool) :
    rawFixedBlocks J q (List.ofFn word) =
      List.ofFn (fun i => List.ofFn (wordBankEquiv q J word i)) := by
  apply List.ext_getElem
  · simp [rawFixedBlocks]
  · intro i hi hj
    have hi' : i < J := by simpa only [List.length_ofFn] using hj
    simp only [rawFixedBlocks,List.getElem_map,List.getElem_range,List.getElem_ofFn]
    have hblock : q*i+q ≤ J*q := by
      calc
        q*i+q = q*(i+1) := by simp only [Nat.mul_add,Nat.mul_one]
        _ ≤ q*J := Nat.mul_le_mul_left q (Nat.succ_le_of_lt hi')
        _ = J*q := Nat.mul_comm _ _
    apply List.ext_getElem
    · simp only [List.length_take,List.length_drop,List.length_ofFn]
      omega
    · intro j hj hk
      have hj' : j < q := by simpa only [List.length_ofFn] using hk
      simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn,wordBankEquiv,
        Equiv.coe_fn_mk,finProdFinEquiv]
      congr 1
      apply Fin.ext
      simp only [Fin.val_mk]
      omega

/-- Taking exactly the reserved bank never changes an individual block,
including when the supplied word is shorter than the reservation. -/
lemma rawFixedBlocks_take (J q : ℕ) (word : List Bool) :
    rawFixedBlocks J q (word.take (J*q)) = rawFixedBlocks J q word := by
  unfold rawFixedBlocks
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  have hblock : q*i+q ≤ J*q := by
    calc
      q*i+q = q*(i+1) := by simp only [Nat.mul_add,Nat.mul_one]
      _ ≤ q*J := Nat.mul_le_mul_left q (Nat.succ_le_of_lt hi')
      _ = J*q := Nat.mul_comm _ _
  rw [List.drop_take,List.take_take]
  congr 1
  omega

lemma rawFirstSuccess_ofFn {A C : Type*} {q : ℕ} (encode : A → C)
    (trial : (Fin q → Bool) → Option A) (rawTrial : List Bool → Option C)
    (htrial : ∀ word, rawTrial (List.ofFn word) = (trial word).map encode)
    (fallback : A) (J : ℕ) (words : Fin J → Fin q → Bool) :
    rawFirstSuccess rawTrial (encode fallback) (List.ofFn (fun i => List.ofFn (words i))) =
      encode (retryWords trial fallback J words) := by
  induction J with
  | zero => rfl
  | succ J ih =>
    rw [List.ofFn_succ]
    simp only [rawFirstSuccess,htrial,retryWords]
    cases trial (words 0) with
    | none => exact ih (Fin.tail words)
    | some value => rfl

/-- Exact flatExit correspondence with unchanged width, order, source,
option failures, and original entering fallback. -/
theorem rawStarExit_eq (htotal : (∑ i,r i) = ∑ j,c j)
    (b : BalancedVertices r c U L) (h : ℕ) (entering : DefectVertices r c U L) (J : ℕ)
    (word : Fin (J*(s + bits r c U L hr hc b.val h)) → Bool) :
    rawStarExit (List.ofFn r) (List.ofFn c) U L d h
      (computedStateCode r c U L b.val) (computedStateCode r c U L entering.val) J
      (List.ofFn word) =
        computedStateCode r c U L (flatExit r c U L hr hc b h entering J word).val := by
  unfold rawStarExit
  rw [rawCompletionBits_eq r c U L hr hc b.val h,rawFixedBlocks_ofFn]
  exact rawFirstSuccess_ofFn (fun e : DefectVertices r c U L => computedStateCode r c U L e.val)
    (actualTrial r c U L hr hc b h) (rawStarTrial (List.ofFn r) (List.ofFn c) U L d h
      (computedStateCode r c U L b.val)) (rawStarTrial_eq r c U L hr hc htotal b h)
    entering J _

/-- A larger reserved word supplies exactly the same source-width blocks.
Trailing common-width slack is ignored after the actual balanced prefix. -/
theorem rawStarExit_eq_reserved (htotal : (∑ i,r i) = ∑ j,c j)
    (b : BalancedVertices r c U L) (h : ℕ) (entering : DefectVertices r c U L) (J N : ℕ)
    (hN : J*(s + bits r c U L hr hc b.val h) ≤ N) (word : Fin N → Bool) :
    rawStarExit (List.ofFn r) (List.ofFn c) U L d h
      (computedStateCode r c U L b.val) (computedStateCode r c U L entering.val) J
      (List.ofFn word) =
        computedStateCode r c U L
          (flatExit r c U L hr hc b h entering J (prefixWord hN word)).val := by
  have he := rawStarExit_eq r c U L hr hc htotal b h entering J (prefixWord hN word)
  rw [←DensePrograms.take_ofFn_prefix hN word] at he
  unfold rawStarExit at he ⊢
  rw [rawCompletionBits_eq r c U L hr hc b.val h,rawFixedBlocks_take] at he
  rw [rawCompletionBits_eq r c U L hr hc b.val h]
  exact he

end
end Math115.PhysicalTraceJoin
