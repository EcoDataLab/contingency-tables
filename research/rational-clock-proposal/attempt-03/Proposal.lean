/-
SPDX-License-Identifier: Apache-2.0
Capped binary rejection for a rational-clock index, followed by list lookup.
Only indices outside the integer interval are retried. An accepted index
outside the neighbor list is a hold, not a reason to retry. These finite-word
maps have no extracted-machine or encoded-cost claim in this module.
-/
import ResearchWeightedExit.FirstSuccess
import Math115.PhysicalComputedProposal
import Research.PhysicalDefectTraceFinal
import OAI.Combinatorics.ContingencyTables.Sampling.ExactIntegerChoice
import OAI.Combinatorics.ContingencyTables.Sampling.ExactIntegerRetry
import OAI.Combinatorics.ContingencyTables.Transport.ListBitProposal

set_option maxHeartbeats 800000

namespace Math115.RationalClockProposal

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open CompletionCounts
open FirstSuccess ResidualMixture FairBits ExactIntegerChoice
open Math115.CompletionBooleanRetry Math115.WeightedExit
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalComputedProposal
open SmallGraphProfiles SmallContextCoordinates FirstPaperProfiles
open scoped BigOperators Classical

noncomputable section

def precision (V : ℕ) : ℕ := Nat.clog 2 V

def intervalWordTrial (V : ℕ) (word : Fin (precision V) → Bool) : Option (Fin V) :=
  intervalTrial (Nat.le_pow_clog (by decide : 1 < 2) V) (binaryWordEquiv (precision V) word)

def intervalWordLaw (V : ℕ) : RationalLaw (Option (Fin V)) :=
  mapLaw (uniformLaw (α := Fin (precision V) → Bool)) (intervalWordTrial V)

def idealIndexLaw (V : ℕ) (hV : 0 < V) : RationalLaw (Fin V) :=
  letI : Nonempty (Fin V) := ⟨⟨0, hV⟩⟩
  uniformLaw

def liftedIndexLaw (V : ℕ) (hV : 0 < V) : RationalLaw (Option (Fin V)) :=
  mapLaw (idealIndexLaw V hV) some

def acceptance (V : ℕ) : ℚ := (V : ℚ) / (2 : ℚ)^(precision V)

lemma intervalWordLaw_some (V : ℕ) (i : Fin V) :
    (intervalWordLaw V).mass (some i) = 1 / (2 : ℚ)^(precision V) := by
  have he := map_equiv (binaryWordEquiv (precision V))
    (uniformLaw (α := Fin (precision V) → Bool))
    (intervalTrial (Nat.le_pow_clog (by decide : 1 < 2) V))
  rw [uniform_equiv] at he
  change (mapLaw (uniformLaw (α := Fin (precision V) → Bool))
    (fun word => intervalTrial (Nat.le_pow_clog (by decide : 1 < 2) V)
      (binaryWordEquiv (precision V) word))).mass (some i) = _
  dsimp only [precision] at he ⊢
  rw [← he, intervalTrial_mass]
  norm_cast

lemma liftedIndexLaw_some (V : ℕ) (hV : 0 < V) (i : Fin V) :
    (liftedIndexLaw V hV).mass (some i) = 1 / (V : ℚ) := by
  simp [liftedIndexLaw, idealIndexLaw, mapLaw, uniformLaw, uniformMass, Fintype.card_fin]

lemma liftedIndexLaw_none (V : ℕ) (hV : 0 < V) :
    (liftedIndexLaw V hV).mass none = 0 := by
  simp [liftedIndexLaw, mapLaw]

lemma lifted_successMass {D : Type*} [Fintype D] [DecidableEq D]
    (q : RationalLaw (Option D)) (i : D) :
    successMass q (fun x => x.map some) (some i) = q.mass (some i) := by
  simp [successMass]

lemma lifted_no_successMass {D : Type*} [Fintype D] [DecidableEq D]
    (q : RationalLaw (Option D)) :
    successMass q (fun x => x.map some) none = 0 := by
  simp [successMass]

lemma interval_weighted_success (V : ℕ) (hV : 0 < V) (i : Option (Fin V)) :
    successMass (intervalWordLaw V) (fun x => x.map some) i =
      acceptance V * (liftedIndexLaw V hV).mass i := by
  cases i with
  | none => rw [lifted_no_successMass, liftedIndexLaw_none, mul_zero]
  | some i =>
      rw [lifted_successMass, intervalWordLaw_some, liftedIndexLaw_some]
      unfold acceptance
      have hVQ : (V : ℚ) ≠ 0 := by exact_mod_cast hV.ne'
      field_simp [hVQ]

lemma interval_failure_nonnegative (V : ℕ) (hV : 0 < V) : 0 ≤ 1 - acceptance V := by
  rw [← failure_of_weighted_success (intervalWordLaw V) (fun x => x.map some)
    (liftedIndexLaw V hV) (acceptance V) (interval_weighted_success V hV)]
  exact Math115.CompletionRetryBudget.failure_nonnegative _ _

lemma interval_failure_le_half (V : ℕ) (hV : 0 < V) : 1 - acceptance V ≤ 1 / 2 := by
  have hshort := clog_power_lt_twice V hV
  have hshortQ : (2 : ℚ)^(precision V) < 2 * (V : ℚ) := by
    exact_mod_cast hshort
  have hhalf : (1 / 2 : ℚ) ≤ acceptance V := by
    unfold acceptance
    apply (le_div_iff₀ (by positivity : (0 : ℚ) < 2^(precision V))).2
    linarith
  linarith

/-- The extra Option lift makes none a terminal exhaustion marker; it is
never replaced by a selected fallback index. -/
def cappedIndex (V N : ℕ) (word : Fin (N * precision V) → Bool) : Option (Fin V) :=
  flatRetry (fun block => (intervalWordTrial V block).map some) none N word

theorem cappedIndex_law (V N : ℕ) :
    mapLaw (uniformLaw (α := Fin (N * precision V) → Bool)) (cappedIndex V N) =
      retryLaw (intervalWordLaw V) (fun x => x.map some) none N :=
  flatRetry_law (intervalWordTrial V) (fun x => x.map some) none N

theorem cappedIndex_none (V : ℕ) (hV : 0 < V) (N : ℕ) :
    (mapLaw (uniformLaw (α := Fin (N * precision V) → Bool)) (cappedIndex V N)).mass none =
      (1 - acceptance V)^N := by
  rw [cappedIndex_law,
    weighted_retry_mass (intervalWordLaw V) (fun x => x.map some) (liftedIndexLaw V hV)
      (acceptance V) (interval_weighted_success V hV), liftedIndexLaw_none]
  simp

theorem cappedIndex_variation (V : ℕ) (hV : 0 < V) (N : ℕ) :
    variation
      (mapLaw (uniformLaw (α := Fin (N * precision V) → Bool)) (cappedIndex V N))
      (liftedIndexLaw V hV) ≤ (1 / 2 : ℚ)^N := by
  rw [cappedIndex_law]
  exact (weighted_retry_variation (intervalWordLaw V) (fun x => x.map some)
    (liftedIndexLaw V hV) (acceptance V) (interval_weighted_success V hV) none N).trans
      (pow_le_pow_left₀ (interval_failure_nonnegative V hV) (interval_failure_le_half V hV) N)

section ListLookup
variable {X : Type*} [Fintype X] [DecidableEq X]

def lookupIndex {V : ℕ} (xs : List X) (i : Option (Fin V)) : Option X :=
  i.bind (fun j => xs[j.val]?)

def cappedList (V : ℕ) (xs : List X) (N : ℕ)
    (word : Fin (N * precision V) → Bool) : Option X :=
  lookupIndex xs (cappedIndex V N word)

def idealListLaw (V : ℕ) (hV : 0 < V) (xs : List X) : RationalLaw (Option X) :=
  mapLaw (idealIndexLaw V hV) (fun i => xs[i.val]?)

lemma lifted_lookup_eq (V : ℕ) (hV : 0 < V) (xs : List X) :
    mapLaw (liftedIndexLaw V hV) (lookupIndex xs) = idealListLaw V hV xs := by
  unfold liftedIndexLaw idealListLaw
  rw [mapLaw_comp]
  rfl

/-- Accepted unused list slots stay holds; lookup never restarts rejection. -/
theorem cappedList_variation (V : ℕ) (hV : 0 < V) (xs : List X) (N : ℕ) :
    variation
      (mapLaw (uniformLaw (α := Fin (N * precision V) → Bool)) (cappedList V xs N))
      (idealListLaw V hV xs) ≤ (1 / 2 : ℚ)^N := by
  have he := variation_map
    (mapLaw (uniformLaw (α := Fin (N * precision V) → Bool)) (cappedIndex V N))
    (liftedIndexLaw V hV) (lookupIndex xs)
  rw [mapLaw_comp, lifted_lookup_eq] at he
  exact he.trans (cappedIndex_variation V hV N)

omit [Fintype X] [DecidableEq X] in
lemma listIndex_eq_iff (xs : List X) (hn : xs.Nodup) (V : ℕ)
    (hlen : xs.length ≤ V) (i : ℕ) (hi : i < xs.length)
    (b : Fin V) : xs[b.val]? = some xs[i] ↔ b = ⟨i, hi.trans_le hlen⟩ := by
  constructor
  · intro hb
    obtain ⟨hb, hval⟩ := List.getElem?_eq_some_iff.mp hb
    apply Fin.ext
    exact hn.getElem_inj_iff.mp hval
  · intro hb
    subst b
    exact List.getElem?_eq_getElem hi

theorem idealListLaw_mass (V : ℕ) (hV : 0 < V) (xs : List X) (hn : xs.Nodup)
    (hlen : xs.length ≤ V) (x : X) :
    (idealListLaw V hV xs).mass (some x) = if x ∈ xs then 1 / (V : ℚ) else 0 := by
  by_cases hx : x ∈ xs
  · obtain ⟨i, hi, hix⟩ := List.mem_iff_getElem.mp hx
    have he (b : Fin V) : xs[b.val]? = some x ↔ b = ⟨i, hi.trans_le hlen⟩ := by
      rw [← hix]
      exact listIndex_eq_iff xs hn V hlen i hi b
    simp only [idealListLaw, idealIndexLaw, mapLaw, uniformLaw, uniformMass,
      Fintype.card_fin, he, ite_eq_left hx]
    simp
  · have he (b : Fin V) : xs[b.val]? ≠ some x := by
      intro hb
      obtain ⟨hb, hval⟩ := List.getElem?_eq_some_iff.mp hb
      exact hx (List.mem_iff_getElem.mpr ⟨b.val, hb, hval⟩)
    simp only [idealListLaw, mapLaw, he, ite_false, Finset.sum_const_zero, ite_eq_right hx]

end ListLookup

section Physical
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)

def physicalNeighbors (x : States r c U L) : List (States r c U L) :=
  codeNeighborStates r c U L (computedCellEquiv r c U) x

def denominator (r : Fin m → ℕ) (c : Fin n → ℕ) (U : ℕ) : ℕ :=
  2 * defectAllowance r c U

lemma denominator_pos
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U))) : 0 < denominator r c U := by
  have hQ := defectAllowance_positive r c U hp
  unfold denominator
  omega

lemma physicalNeighbors_nodup (x : States r c U L) : (physicalNeighbors r c U L x).Nodup :=
  codeNeighborStates_nodup r c U L (computedCellEquiv r c U) x

lemma physicalNeighbors_length (htotal : (∑ i, r i) = ∑ j, c j)
    (x : DefectVertices r c U L) :
    (physicalNeighbors r c U L x.val).length ≤ defectAllowance r c U := by
  have he : (physicalNeighbors r c U L x.val).toFinset =
      Finset.univ.filter (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x.val) := by
    ext y
    simp only [List.mem_toFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      physicalNeighbors, mem_codeNeighborStates r c U L (computedCellEquiv r c U) htotal]
  calc
    _ = (physicalNeighbors r c U L x.val).toFinset.card :=
      (List.toFinset_card_of_nodup (physicalNeighbors_nodup r c U L x.val)).symm
    _ = _ := congrArg Finset.card he
    _ ≤ _ := actual_defect_degree r c U L x

def physicalProposal (x : DefectVertices r c U L) (N : ℕ)
    (word : Fin (N * precision (denominator r c U)) → Bool) : Option (States r c U L) :=
  cappedList (denominator r c U) (physicalNeighbors r c U L x.val) N word

def idealPhysicalProposalLaw
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (x : DefectVertices r c U L) : RationalLaw (Option (States r c U L)) :=
  idealListLaw (denominator r c U) (denominator_pos r c U hp) (physicalNeighbors r c U L x.val)

theorem physicalProposal_variation
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (x : DefectVertices r c U L) (N : ℕ) :
    variation
      (mapLaw (uniformLaw (α := Fin (N * precision (denominator r c U)) → Bool))
        (physicalProposal r c U L x N))
      (idealPhysicalProposalLaw r c U L hp x) ≤ (1 / 2 : ℚ)^N :=
  cappedList_variation (denominator r c U) (denominator_pos r c U hp)
    (physicalNeighbors r c U L x.val) N

/-- Every actual neighbor has the canonical rational proposal rate. -/
theorem idealPhysicalProposalLaw_mass (htotal : (∑ i, r i) = ∑ j, c j)
    (hp : 2 ≤ Fintype.card (Cells (firstPaperSmall r c U)))
    (x : DefectVertices r c U L) (y : States r c U L) :
    (idealPhysicalProposalLaw r c U L hp x).mass (some y) =
      if physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x.val y
      then 1 / (denominator r c U : ℚ) else 0 := by
  have hlen := physicalNeighbors_length r c U L htotal x
  have hlen' : (physicalNeighbors r c U L x.val).length ≤ denominator r c U := by
    unfold denominator
    omega
  rw [idealPhysicalProposalLaw, idealListLaw_mass _ _ _ (physicalNeighbors_nodup r c U L x.val) hlen']
  rw [physicalNeighbors, mem_codeNeighborStates r c U L (computedCellEquiv r c U) htotal]

theorem rational_clock_cast :
    ((1 / (denominator r c U : ℚ) : ℚ) : ℝ) = 1 / (2 * (defectAllowance r c U : ℝ)) := by
  unfold denominator
  push_cast
  rfl

end Physical
end
end Math115.RationalClockProposal
