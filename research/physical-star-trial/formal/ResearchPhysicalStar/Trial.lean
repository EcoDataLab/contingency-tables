/-
SPDX-License-Identifier: Apache-2.0
One physical balanced-star trial with the existing dyadic proposal clock.
Only the current balanced state's completion width is reserved here.
No incoming rational trace clock, retry schedule or outer sampler is identified.
-/
import ResearchListedAcceptance.Decision
import ResearchComputedReference.Trace
import Math115.PhysicalComputedProposal
import OAI.Combinatorics.ContingencyTables.Transport.WordCompletionStep

set_option maxHeartbeats 800000

namespace Math115.PhysicalStarTrial

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms CompletionTranslation
open SmallGraphProfiles
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open CompletionCounts PaddedCompletions FirstSuccess ResidualMixture FairBits
open Math115.ReducedSmallChain Math115.PhysicalCompletionOracle
open Math115.PhysicalRationalKernel Math115.PhysicalStationarySuccess
open Math115.PhysicalDefectTrace Math115.ComputedReferenceTrace
open Math115.LegacyPhysicalCompletion Math115.ListedAcceptance
open Math115.CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section

/-- Fixed-width independence algebra, proved before any physical program is
substituted for the two word maps. -/
lemma fixedWord_finish_law
    {A T Z : Type*} [Fintype A] [Fintype T] [Fintype Z]
    [DecidableEq A] [DecidableEq T] [DecidableEq Z] {s f : ℕ}
    (proposal : (Fin s → Bool) → A) (draw : (Fin f → Bool) → T)
    (finish : A → T → Z) :
    mapLaw (uniformLaw (α := Fin (s + f) → Bool))
      (fun word => let parts := splitWordEquiv s f word
        finish (proposal parts.1) (draw parts.2)) =
      bindLaw (mapLaw (uniformLaw (α := Fin s → Bool)) proposal)
        (fun a => mapLaw (mapLaw (uniformLaw (α := Fin f → Bool)) draw) (finish a)) := by
  let F := fun parts : (Fin s → Bool) × (Fin f → Bool) =>
    finish (proposal parts.1) (draw parts.2)
  have he := map_equiv (splitWordEquiv s f)
    (uniformLaw (α := Fin (s + f) → Bool)) F
  rw [uniform_equiv, ←uniform_product] at he
  calc
    _ = mapLaw (productLaw (uniformLaw (α := Fin s → Bool))
        (uniformLaw (α := Fin f → Bool))) F := he.symm
    _ = bindLaw (mapLaw (uniformLaw (α := Fin s → Bool)) proposal)
        (fun a => mapLaw (uniformLaw (α := Fin f → Bool))
          (fun word => finish a (draw word))) :=
      mapLaw_product_finish _ _ proposal (fun a word => finish a (draw word))
    _ = _ := by
      congr 1
      funext a
      exact (mapLaw_comp _ draw (finish a)).symm

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U, List.ofFn c)).length)

local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => Nat.clog 2 (32 * d^2)
local notation "B" => capacity r c U L
local notation "i₀" => largeOptionEquiv r U hr none
local notation "j₀" => largeOptionEquiv c U hc none
local notation "R₀" => referenceRows r c U L B i₀
local notation "P₀" => referenceColumns r c U L B j₀

/-- Holding and balanced outputs are failures. -/
def defectProjection (x : States r c U L) : Option (DefectVertices r c U L) :=
  if hx : ¬IsBalanced r c U L x then some ⟨x, hx⟩ else none

lemma defectProjection_eq_some_iff (x : States r c U L) (e : DefectVertices r c U L) :
    defectProjection r c U L x = some e ↔ x = e.val := by
  by_cases hx : ¬IsBalanced r c U L x
  · simp only [defectProjection, dif_pos hx, Option.some.injEq]
    exact Subtype.ext_iff
  · simp only [defectProjection, dif_neg hx, reduceCtorEq, false_iff]
    intro hxe
    exact hx (hxe.symm ▸ e.property)

lemma defectProjection_balanced (b : BalancedVertices r c U L) :
    defectProjection r c U L b.val = none := by
  simp [defectProjection, b.property]

lemma projected_mass_some (p : RationalLaw (States r c U L))
    (e : DefectVertices r c U L) :
    (mapLaw p (defectProjection r c U L)).mass (some e) = p.mass e.val := by
  simp only [mapLaw, defectProjection_eq_some_iff]
  simp

/-- This is the literal checked list Boolean on the actual frozen draw output. -/
def actualStep (b : BalancedVertices r c U L) (h : ℕ)
    (word : Fin (s + bits r c U L hr hc b.val h) → Bool) : States r c U L :=
  let parts := splitWordEquiv s (bits r c U L hr hc b.val h) word
  match Math115.PhysicalComputedProposal.computedProposal r c U L b.val parts.1 with
  | none => b.val
  | some y =>
    if translationValid
      (((List.ofFn (coarseRows r c U L hr b.val), List.ofFn (coarseColumns r c U L hc b.val)),
        (List.ofFn (coarseRows r c U L hr y), List.ofFn (coarseColumns r c U L hc y))),
        LatticeSampler.draw
          (((List.ofFn (coarseRows r c U L hr b.val),
            List.ofFn (coarseColumns r c U L hc b.val)), h), List.ofFn parts.2))
    then y else b.val

def actualTrial (b : BalancedVertices r c U L) (h : ℕ)
    (word : Fin (s + bits r c U L hr hc b.val h) → Bool) :
    Option (DefectVertices r c U L) :=
  defectProjection r c U L (actualStep r c U L hr hc b h word)

def actualTrialLaw (b : BalancedVertices r c U L) (h : ℕ) :
    RationalLaw (Option (DefectVertices r c U L)) :=
  mapLaw (uniformLaw (α := Fin (s + bits r c U L hr hc b.val h) → Bool))
    (actualTrial r c U L hr hc b h)

/-- Ideal completions are used only to define the comparison law. -/
def idealTrialLaw (b : BalancedVertices r c U L) :
    RationalLaw (Option (DefectVertices r c U L)) :=
  mapLaw (referenceStepLaw r c U L i₀ j₀
    (fun z => uniformLaw (α := ReferenceTable r c U L i₀ j₀ z)) b.val)
    (defectProjection r c U L)

lemma referenceDraw_law (x : States r c U L) (h : ℕ) :
    mapLaw (uniformLaw (α := Fin (bits r c U L hr hc x h) → Bool))
      (fun word => referenceCompletion r c U L hr hc x
        (completionDraw r c U L hr hc x h word)) =
      oracleFamily r c U L hr hc h i₀ j₀ x := by
  unfold referenceCompletion oracleFamily referenceFibreMap completionLaw
  simp only [Equiv.symm_symm]
  exact mapLaw_equiv_output _
    (uniformLaw (α := Fin (bits r c U L hr hc x h) → Bool))
    (completionDraw r c U L hr hc x h)

/-- The actual Boolean branch, isolated before the word-law algebra. -/
lemma actualStep_eq (b : BalancedVertices r c U L) (h : ℕ)
    (word : Fin (s + bits r c U L hr hc b.val h) → Bool) :
    actualStep r c U L hr hc b h word =
      let parts := splitWordEquiv s (bits r c U L hr hc b.val h) word
      completionDecision R₀ P₀ b.val
        (Math115.PhysicalComputedProposal.computedProposal r c U L b.val parts.1)
        (referenceCompletion r c U L hr hc b.val
          (completionDraw r c U L hr hc b.val h parts.2)) := by
  dsimp only [actualStep]
  exact draw_completionDecision r c U L hr hc b.val
    (Math115.PhysicalComputedProposal.computedProposal r c U L b.val
      (splitWordEquiv s (bits r c U L hr hc b.val h) word).1) h
    (splitWordEquiv s (bits r c U L hr hc b.val h) word).2

/-- The word split is at this fixed b; completion widths at other states are
never equated with its width. -/
theorem actualStep_law (htotal : (∑ i, r i) = ∑ j, c j)
    (b : BalancedVertices r c U L) (h : ℕ) :
    mapLaw (uniformLaw (α := Fin (s + bits r c U L hr hc b.val h) → Bool))
      (actualStep r c U L hr hc b h) =
    referenceStepLaw r c U L i₀ j₀ (oracleFamily r c U L hr hc h i₀ j₀) b.val := by
  have hpoint := funext (actualStep_eq r c U L hr hc b h)
  rw [hpoint]
  calc
    _ = bindLaw
        (mapLaw (uniformLaw (α := Fin s → Bool))
          (Math115.PhysicalComputedProposal.computedProposal r c U L b.val))
        (fun proposal => mapLaw
          (mapLaw (uniformLaw (α := Fin (bits r c U L hr hc b.val h) → Bool))
            (fun word => referenceCompletion r c U L hr hc b.val
              (completionDraw r c U L hr hc b.val h word)))
          (completionDecision R₀ P₀ b.val proposal)) :=
      fixedWord_finish_law
        (Math115.PhysicalComputedProposal.computedProposal r c U L b.val)
        (fun word => referenceCompletion r c U L hr hc b.val
          (completionDraw r c U L hr hc b.val h word))
        (completionDecision R₀ P₀ b.val)
    _ = _ := by
      rw [Math115.PhysicalComputedProposal.computedProposal_law r c U L htotal b.val,
        referenceDraw_law r c U L hr hc b.val h]
      rfl

theorem actualTrialLaw_eq (htotal : (∑ i, r i) = ∑ j, c j)
    (b : BalancedVertices r c U L) (h : ℕ) :
    actualTrialLaw r c U L hr hc b h =
    mapLaw (referenceStepLaw r c U L i₀ j₀
      (oracleFamily r c U L hr hc h i₀ j₀) b.val) (defectProjection r c U L) := by
  unfold actualTrialLaw actualTrial
  rw [←mapLaw_comp, actualStep_law r c U L hr hc htotal b h]

/-- All conductances in this trial are rational natural-count expressions. -/
def crossRat (b : BalancedVertices r c U L) (e : DefectVertices r c U L) : ℚ :=
  if physicalAdjacent r c U L B (capacity_small r c U L) b.val e.val then
    (acceptedCount R₀ P₀ b.val e.val : ℚ) else 0

def weightRat (b : BalancedVertices r c U L) : ℚ := (blockCount R₀ P₀ b.val : ℚ)

lemma crossRat_cast (b : BalancedVertices r c U L) (e : DefectVertices r c U L) :
    (crossRat r c U L hr hc b e : ℝ) = referenceCross r c U L i₀ j₀ b e := by
  unfold crossRat referenceCross referenceConductance
  split_ifs <;> simp only [Rat.cast_natCast, Rat.cast_zero]

lemma weightRat_cast (b : BalancedVertices r c U L) :
    (weightRat r c U L hr hc b : ℝ) = balancedWeight r c U L b := by
  simpa only [weightRat, Rat.cast_natCast, balancedWeight] using
    (reference_weight r c U L i₀ j₀ b.val).symm

/-- The old dyadic proposal clock appears explicitly; this is not the incoming
clock 1 / (2 * (4*p-3)) of the canonical defect trace. -/
theorem idealTrialLaw_mass_some (b : BalancedVertices r c U L)
    (e : DefectVertices r c U L) :
    (idealTrialLaw r c U L hr hc b).mass (some e) =
      proposalRat d * crossRat r c U L hr hc b e / weightRat r c U L hr hc b := by
  letI : Nonempty (States r c U L) := ⟨b.val⟩
  unfold idealTrialLaw
  rw [projected_mass_some, referenceExactStep_eq]
  have hbe : b.val ≠ e.val := by
    intro he
    exact e.property (he ▸ b.property)
  change referenceTransitionRat r c U L i₀ j₀ b.val e.val = _
  simp only [referenceTransitionRat, hbe, ite_false, add_zero]
  unfold referenceMoveRat crossRat weightRat
  split_ifs <;> simp

theorem idealTrialLaw_mass_some_cast (b : BalancedVertices r c U L)
    (e : DefectVertices r c U L) :
    ((idealTrialLaw r c U L hr hc b).mass (some e) : ℝ) =
      (proposalRat d : ℝ) * referenceCross r c U L i₀ j₀ b e /
        balancedWeight r c U L b := by
  rw [idealTrialLaw_mass_some]
  simp only [Rat.cast_div, Rat.cast_mul, crossRat_cast, weightRat_cast]

/-- Fresh proposal and completion bits, followed by deterministic projection,
preserve the frozen draw's dyadic accuracy allowance. -/
theorem actualTrialLaw_accuracy (htotal : (∑ i, r i) = ∑ j, c j)
    (b : BalancedVertices r c U L) (h : ℕ) :
    variation (actualTrialLaw r c U L hr hc b h) (idealTrialLaw r c U L hr hc b) ≤
      dyadic h := by
  rw [actualTrialLaw_eq r c U L hr hc htotal b h]
  unfold idealTrialLaw
  apply (variation_map _ _ (defectProjection r c U L)).trans
  exact completionStep_variation R₀ P₀ (physicalProposalLaw r c U L)
    (oracleFamily r c U L hr hc h i₀ j₀)
    (fun z => uniformLaw (α := ReferenceTable r c U L i₀ j₀ z)) (dyadic h)
    (oracleFamily_accuracy r c U L hr hc h i₀ j₀) b.val

end
end Math115.PhysicalStarTrial
