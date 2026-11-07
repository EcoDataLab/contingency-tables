/-
SPDX-License-Identifier: Apache-2.0
Arbitrary outer cutoff/padding physical completions supplied by the frozen
complete LatticeSampler.draw. This is a semantic program/fibre adapter, not an
encoded new outer sampler or a new runtime bound. Both selected lists are
nonempty. The Classical.choose below is only a typed semantic witness; the
pointwise code theorem identifies the executable program being called.
-/
import Math115.LatticeSampler
import OAI.Combinatorics.ContingencyTables.Transport.ListedCompletion

namespace Math115.LegacyPhysicalCompletion

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open SmallGraphProfiles CompletionCounts PaddedCompletions ProfilePrograms DensePrograms
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open ReducedSmallChain PhysicalCompletionOracle PhysicalStationarySuccess
open FirstSuccess ResidualMixture FairBits CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
local notation "B" => capacity r c U L

def tailCount {q : ℕ} (R : Fin q → ℕ) (V : ℕ) : ℕ :=
  (largeIndices (V, List.ofFn R)).length - 1

local notation "nr" => tailCount r U
local notation "nc" => tailCount c U

def coarseRows (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (z : States r c U L) : Fin (nr + 1) → ℕ :=
  fun i => listedRows r c U L B hr z (finSuccEquiv nr i)

def coarseColumns (hc : 0 < (largeIndices (U, List.ofFn c)).length)
    (z : States r c U L) : Fin (nc + 1) → ℕ :=
  fun j => listedColumns r c U L B hc z (finSuccEquiv nc j)

theorem coarse_totals
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) :
    (∑ i, coarseRows r c U L hr z i) = ∑ j, coarseColumns r c U L hc z j := by
  unfold coarseRows coarseColumns tailCount
  exact ((finSuccEquiv _).sum_comp (listedRows r c U L B hr z)).trans
    ((listed_totals r c U L B hr hc z
      (physical_paper_capacity _ r c _ L U dimension_le_allowance z)).trans
      ((finSuccEquiv _).sum_comp (listedColumns r c U L B hc z)).symm)

/-- Actual row input in the physical program's computed large-line order. -/
theorem coarseRows_code
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    {q : ℕ} (e : Fin q ≃ SmallContextCoordinates.Cells (firstPaperSmall r c U))
    (z : States r c U L) :
    List.ofFn (coarseRows r c U L hr z) = largePaddedMargins true
      (((((cellCatalog (firstPaperSmall r c U) e,
        viewList (firstPaperSmall r c U) e (physicalProfile _ B r c L z) false),
        (List.ofFn r, List.ofFn c)), U), L)) := by
  rw [show List.ofFn (coarseRows r c U L hr z) = marginCode (listedRows r c U L B hr z)
    from (marginCode_ofFn _).symm]
  exact listedRows_code r c U L B hr e z

/-- Actual column input, including the physical complement-view rule. -/
theorem coarseColumns_code
    (hc : 0 < (largeIndices (U, List.ofFn c)).length)
    {q : ℕ} (e : Fin q ≃ SmallContextCoordinates.Cells (firstPaperSmall r c U))
    (z : States r c U L) :
    List.ofFn (coarseColumns r c U L hc z) = largePaddedMargins false
      (((((cellCatalog (firstPaperSmall r c U) e,
        complementValues (U, viewList (firstPaperSmall r c U) e
          (physicalProfile _ B r c L z) true)),
        (List.ofFn r, List.ofFn c)), U), L)) := by
  rw [show List.ofFn (coarseColumns r c U L hc z) = marginCode (listedColumns r c U L B hc z)
    from (marginCode_ofFn _).symm]
  exact listedColumns_code r c U L B hc e
    (fun a => capacity_small r c U L a.val.1 a.val.2 a.property) z

/-- The redundant physical capacity discharges the unrestricted-table bridge. -/
def finiteFibreEquiv
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) :
    Fibre r c U L z ≃ Table (coarseRows r c U L hr z) (coarseColumns r c U L hc z) :=
  (listedFibreEquiv r c U L B hr hc z
    (physical_paper_capacity _ r c _ L U dimension_le_allowance z)).trans
    (tableReindex (finSuccEquiv nr) (finSuccEquiv nc)
      (listedRows r c U L B hr z) (listedColumns r c U L B hc z))

theorem finiteFibreEquiv_entry
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L)
    (A : Fibre r c U L z) (i : Fin (nr + 1)) (j : Fin (nc + 1)) :
    (finiteFibreEquiv r c U L hr hc z A).val i j =
      (referenceFibreEquiv r c U L B (largeOptionEquiv r U hr none)
        (largeOptionEquiv c U hc none) z
        (physical_paper_capacity _ r c _ L U dimension_le_allowance z) A).val
          (listedReferenceIndex r U hr (finSuccEquiv nr i))
          (listedReferenceIndex c U hc (finSuccEquiv nc j)) := by
  exact listedFibreEquiv_entry r c U L B hr hc z
    (physical_paper_capacity _ r c _ L U dimension_le_allowance z) A
    (finSuccEquiv nr i) (finSuccEquiv nc j)

def bits
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ) : ℕ :=
  LatticeScheduleProgram.totalBits
    ((List.ofFn (coarseRows r c U L hr z), List.ofFn (coarseColumns r c U L hc z)), h)

def programTable
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ) :
    (Fin (bits r c U L hr hc z h) → Bool) →
      Table (coarseRows r c U L hr z) (coarseColumns r c U L hc z) :=
  Classical.choose (LatticeSampler.draw_spec (coarseRows r c U L hr z)
    (coarseColumns r c U L hc z) (coarse_totals r c U L hr hc z) h)

/-- Every supplied word returns the code of this feasible residual table. -/
theorem programTable_code
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ)
    (word : Fin (bits r c U L hr hc z h) → Bool) :
    LatticeSampler.draw
      (((List.ofFn (coarseRows r c U L hr z), List.ofFn (coarseColumns r c U L hc z)), h),
        List.ofFn word) = matrixCode (programTable r c U L hr hc z h word).val :=
  (Classical.choose_spec (LatticeSampler.draw_spec (coarseRows r c U L hr z)
    (coarseColumns r c U L hc z) (coarse_totals r c U L hr hc z) h)).1 word

theorem programTable_accuracy
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ) :
    letI := table_nonempty _ _ (coarse_totals r c U L hr hc z)
    variation (mapLaw (uniformLaw (α := Fin (bits r c U L hr hc z h) → Bool))
      (programTable r c U L hr hc z h))
      (uniformLaw (α := Table (coarseRows r c U L hr z) (coarseColumns r c U L hc z))) ≤
        dyadic h := by
  apply (Rat.cast_le (K := ℝ)).mp
  exact (Classical.choose_spec (LatticeSampler.draw_spec (coarseRows r c U L hr z)
    (coarseColumns r c U L hc z) (coarse_totals r c U L hr hc z) h)).2

def completionDraw
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ)
    (word : Fin (bits r c U L hr hc z h) → Bool) : Fibre r c U L z :=
  (finiteFibreEquiv r c U L hr hc z).symm (programTable r c U L hr hc z h word)

/-- Exact identity connecting the old executable output to the physical fibre. -/
theorem completionDraw_code
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ)
    (word : Fin (bits r c U L hr hc z h) → Bool) :
    LatticeSampler.draw
      (((List.ofFn (coarseRows r c U L hr z), List.ofFn (coarseColumns r c U L hc z)), h),
        List.ofFn word) = matrixCode
          ((finiteFibreEquiv r c U L hr hc z) (completionDraw r c U L hr hc z h word)).val := by
  simpa only [completionDraw, Equiv.apply_symm_apply] using
    programTable_code r c U L hr hc z h word

def completionLaw
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ) :
    RationalLaw (Fibre r c U L z) :=
  mapLaw (uniformLaw (α := Fin (bits r c U L hr hc z h) → Bool))
    (completionDraw r c U L hr hc z h)

/-- Accuracy is obtained from the actual old draw_spec, with no accuracy premise. -/
theorem completionLaw_accuracy
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ) :
    variation (completionLaw r c U L hr hc z h) (uniformLaw (α := Fibre r c U L z)) ≤
      dyadic h := by
  let E := finiteFibreEquiv r c U L hr hc z
  letI := table_nonempty _ _ (coarse_totals r c U L hr hc z)
  change variation (mapLaw (uniformLaw (α := Fin (bits r c U L hr hc z h) → Bool))
    (fun word => E.symm (programTable r c U L hr hc z h word)))
      (uniformLaw (α := Fibre r c U L z)) ≤ _
  rw [mapLaw_equiv_output, ← equivLaw_uniform E.symm, variation_equiv]
  exact programTable_accuracy r c U L hr hc z h

def oracleFamily
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (h : ℕ) : OracleFamily r c U L :=
  fun i j z => equivLaw (referenceFibreMap r c U L i j z).symm
    (completionLaw r c U L hr hc z h)

theorem oracleFamily_accuracy
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (h : ℕ) :
    ∀ (i : LargeRows r U) (j : LargeColumns c U) (z : States r c U L),
      variation (oracleFamily r c U L hr hc h i j z)
        (uniformLaw (α := ReferenceTable r c U L i j z)) ≤ dyadic h := by
  intro i j z
  unfold oracleFamily
  rw [← equivLaw_uniform (referenceFibreMap r c U L i j z).symm, variation_equiv]
  exact completionLaw_accuracy r c U L hr hc z h

end
end Math115.LegacyPhysicalCompletion
