/-
SPDX-License-Identifier: Apache-2.0
Actual completion program in computed large-index list order.
Uses generic arbitrary-scale listed completion coordinates, not the old
paper-scale dense wrapper. No outer neighbor/loop machine-cost claim is made.
-/
import Math115.CompletionSamplerSemantics
import Math115.PhysicalReferenceWalk
import OAI.Combinatorics.ContingencyTables.Transport.ListedCompletion

namespace Math115.ListedLatticeCompletion

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open SmallGraphProfiles CompletionCounts PaddedCompletions ProfilePrograms DensePrograms
open PhysicalCompletionFibres FirstPaperPhysicalMarginal
open SmallContextCoordinates SmallContextFibres FirstPaperProfiles
open ReducedSmallChain PhysicalCompletionOracle PhysicalStationarySuccess
open PhysicalFiniteWalk PhysicalStateNonempty FirstSuccess ResidualMixture
open CompletionRetryBudget
open scoped BigOperators Classical
noncomputable section

/-- Tail dimension of the actual computed large-index list. -/
def tailCount {q : ℕ} (R : Fin q → ℕ) (V : ℕ) : ℕ := (largeIndices (V, List.ofFn R)).length - 1

lemma tailCount_eq_referenceFree {q : ℕ} (R : Fin q → ℕ) (V : ℕ)
    (hR : 0 < (largeIndices (V, List.ofFn R)).length) :
    tailCount R V = PhysicalLatticeCompletion.rowFree R V (largeOptionEquiv R V hR none) := by
  have h := Fintype.card_congr (listedReferenceIndex R V hR)
  have h' : tailCount R V + 1 =
      PhysicalLatticeCompletion.rowFree R V (largeOptionEquiv R V hR none) + 1 := by
    simpa only [tailCount, PhysicalLatticeCompletion.rowFree, PhysicalLatticeCompletion.RowTail,
      Fintype.card_option, Fintype.card_fin] using h
  exact Nat.add_right_cancel h'

lemma fullCount_card {q : ℕ} (R : Fin q → ℕ) (V : ℕ)
    (hR : 0 < (largeIndices (V, List.ofFn R)).length) :
    tailCount R V + 1 = Fintype.card (LargeRows R V) := by
  simpa only [tailCount, Fintype.card_option, Fintype.card_fin] using
    Fintype.card_congr (largeOptionEquiv R V hR)

variable {m n : ℕ}
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => IdealOracleScales.cutoff (I := Fin m) (J := Fin n)
local notation "L" => IdealOracleScales.padding (I := Fin m) (J := Fin n)
variable (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "nr" => tailCount r U
local notation "nc" => tailCount c U
local notation "B" => capacity r c U L

def coarseRows
    (hr : 0 < (largeIndices (U, List.ofFn r)).length) (z : States r c U L) : Fin (nr + 1) → ℕ :=
  fun i => listedRows r c U L B hr z (finSuccEquiv nr i)

def coarseColumns
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) : Fin (nc + 1) → ℕ :=
  fun j => listedColumns r c U L B hc z (finSuccEquiv nc j)

lemma coarse_totals
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) :
    (∑ i, coarseRows r c hr z i) = ∑ j, coarseColumns r c hc z j := by
  unfold coarseRows coarseColumns tailCount
  exact ((finSuccEquiv ((largeIndices (U, List.ofFn r)).length - 1)).sum_comp
    (listedRows r c U L B hr z)).trans
    ((listed_totals r c U L B hr hc z
      (physical_paper_capacity _ r c _ L U dimension_le_allowance z)).trans
      ((finSuccEquiv ((largeIndices (U, List.ofFn c)).length - 1)).sum_comp
        (listedColumns r c U L B hc z)).symm)

lemma parameters_listed
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ) :
    CompletionSamplerSemantics.parameters (m := nr) (n := nc) d (coarseRows r c hr z) (coarseColumns r c hc z) h =
      ((marginCode (listedRows r c U L B hr z), marginCode (listedColumns r c U L B hc z)), (d, h)) := by
  unfold CompletionSamplerSemantics.parameters
  rw [show List.ofFn (coarseRows r c hr z) = marginCode (listedRows r c U L B hr z)
      from (marginCode_ofFn _).symm,
    show List.ofFn (coarseColumns r c hc z) = marginCode (listedColumns r c U L B hc z)
      from (marginCode_ofFn _).symm]

/-- Exact row-list input supplied by the physical residual program. -/
theorem coarseRows_code
    (hr : 0 < (largeIndices (U, List.ofFn r)).length) {q : ℕ} (e : Fin q ≃ Cells (firstPaperSmall r c U))
    (z : States r c U L) :
    List.ofFn (coarseRows r c hr z) = largePaddedMargins true
      (((((cellCatalog (firstPaperSmall r c U) e,
        viewList (firstPaperSmall r c U) e (physicalProfile _ B r c L z) false),
        (List.ofFn r, List.ofFn c)), U), L)) := by
  rw [show List.ofFn (coarseRows r c hr z) = marginCode (listedRows r c U L B hr z)
    from (marginCode_ofFn _).symm]
  exact listedRows_code r c U L B hr e z

/-- Exact column-list input, preserving the source's complement-view rule. -/
theorem coarseColumns_code
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) {q : ℕ} (e : Fin q ≃ Cells (firstPaperSmall r c U))
    (z : States r c U L) :
    List.ofFn (coarseColumns r c hc z) = largePaddedMargins false
      (((((cellCatalog (firstPaperSmall r c U) e,
        complementValues (U, viewList (firstPaperSmall r c U) e (physicalProfile _ B r c L z) true)),
        (List.ofFn r, List.ofFn c)), U), L)) := by
  rw [show List.ofFn (coarseColumns r c hc z) = marginCode (listedColumns r c U L B hc z)
    from (marginCode_ofFn _).symm]
  exact listedColumns_code r c U L B hc e
    (fun a => capacity_small r c U L a.val.1 a.val.2 a.property) z

lemma dimensions
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) : nr + 1 ≤ d ∧ nc + 1 ≤ d := by
  simpa only [tailCount_eq_referenceFree r U hr, tailCount_eq_referenceFree c U hc] using
    PhysicalLatticeCompletion.finite_dimensions r c U (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)

lemma free_dimension
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) : nr * nc ≤ d - 1 := by
  simpa only [tailCount_eq_referenceFree r U hr, tailCount_eq_referenceFree c U hc] using
    PhysicalLatticeCompletion.finite_free_dimension r c U (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)

lemma dimension_fourteen
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) : 14 ≤ d := PhysicalLatticeCompletion.dimension_fourteen r c U (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none)

lemma coarse_row_lower
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (i : Fin (nr + 1)) :
    (nc + 1) * (3 * d) ≤ coarseRows r c hr z i := by
  rw [fullCount_card c U hc]
  change Fintype.card (LargeColumns c U) * L ≤
    listedRows r c U L B hr z (finSuccEquiv nr i)
  rw [← listedReference_row r c U L B hr z]
  exact DilatedCompletionMargins.reference_row_lower r c U L (largeOptionEquiv r U hr none) z
    (listedReferenceIndex r U hr (finSuccEquiv nr i))

lemma coarse_column_lower
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (j : Fin (nc + 1)) :
    (nr + 1) * (3 * d) ≤ coarseColumns r c hc z j := by
  rw [fullCount_card r U hr]
  change Fintype.card (LargeRows r U) * L ≤
    listedColumns r c U L B hc z (finSuccEquiv nc j)
  rw [← listedReference_column r c U L B hc z]
  exact DilatedCompletionMargins.reference_column_lower r c U L (largeOptionEquiv c U hc none) z
    (listedReferenceIndex c U hc (finSuccEquiv nc j))

lemma coarse_row_upper
    (hr : 0 < (largeIndices (U, List.ofFn r)).length) (z : States r c U L) (i : Fin (nr + 1)) :
    coarseRows r c hr z i ≤ (∑ i, r i) + d * L := by
  change listedRows r c U L B hr z (finSuccEquiv nr i) ≤ _
  rw [← listedReference_row r c U L B hr z]
  have h := PhysicalLatticeCompletion.finite_row_upper r c U L (largeOptionEquiv r U hr none) z
    ((PhysicalLatticeCompletion.rowIndex r U (largeOptionEquiv r U hr none)).symm
      (listedReferenceIndex r U hr (finSuccEquiv nr i)))
  simpa only [PhysicalLatticeCompletion.finiteRows, Equiv.apply_symm_apply] using h

lemma dense_row_upper
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (i : Option (Fin nr)) :
    DenseLatticeCompletion.denseRows (d^12) nc (coarseRows r c hr z) i ≤
      PhysicalLatticeCompletion.fineRowBound (J := Fin n) r := by
  have hrow := coarse_row_upper r c hr z ((finSuccEquiv nr).symm i)
  have hdim := (dimensions r c hr hc).2
  have hin : coarseRows r c hr z ((finSuccEquiv nr).symm i) + 2 * (nc + 1) ≤
      (∑ i, r i) + d * L + 2 * d := by omega
  exact Nat.mul_le_mul_left (d^12) hin

theorem fineBits_le_reserved
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ) :
    DenseLatticeCompletion.fineBits d (coarseRows r c hr z) (coarseColumns r c hc z)
      (finePrecision h) ≤ PhysicalLatticeCompletion.reservedFineBits (J := Fin n) r h := by
  exact DenseLatticeCompletion.fineBits_polynomial (m := nr) (n := nc) d
    (PhysicalLatticeCompletion.fineRowBound (J := Fin n) r)
    (PhysicalLatticeCompletion.fineBinaryLength (J := Fin n) r) (finePrecision h)
    (coarseRows r c hr z) (coarseColumns r c hc z)
    (by have he := free_dimension r c hr hc; omega)
    (dense_row_upper r c hr hc z) (le_refl _)

theorem completionBits_le_reserved
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ) :
    DenseLatticeCompletion.completionBits d (coarseRows r c hr z) (coarseColumns r c hc z) h ≤
      PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r h := by
  exact Nat.mul_le_mul_left (retries h) (fineBits_le_reserved r c hr hc z h)

/-- Exact entry-preserving physical-fibre equivalence in computed list order. -/
def finiteFibreEquiv
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) :
    Fibre r c U L z ≃ Table (coarseRows r c hr z) (coarseColumns r c hc z) :=
  (listedFibreEquiv r c U L B hr hc z
    (physical_paper_capacity _ r c _ L U dimension_le_allowance z)).trans
    (tableReindex (finSuccEquiv nr) (finSuccEquiv nc)
      (listedRows r c U L B hr z) (listedColumns r c U L B hc z))

lemma finiteFibreEquiv_entry
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (A : Fibre r c U L z)
    (i : Fin (nr + 1)) (j : Fin (nc + 1)) :
    (finiteFibreEquiv r c hr hc z A).val i j =
      (referenceFibreEquiv r c U L B (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none) z
        (physical_paper_capacity _ r c _ L U dimension_le_allowance z) A).val
        (listedReferenceIndex r U hr (finSuccEquiv nr i))
        (listedReferenceIndex c U hc (finSuccEquiv nc j)) := by
  exact listedFibreEquiv_entry r c U L B hr hc z
    (physical_paper_capacity _ r c _ L U dimension_le_allowance z) A
    (finSuccEquiv nr i) (finSuccEquiv nc j)

/-- Finite table returned from the actual complete program on a common word. -/
def programTable
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ)
    (bits : Fin (PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r h) → Bool) :
    Table (coarseRows r c hr z) (coarseColumns r c hc z) :=
  CompletionSamplerSemantics.programTable (m := nr) (n := nc) d (dimension_fourteen r c hr hc)
    (coarseRows r c hr z) (coarseColumns r c hc z) (coarse_totals r c hr hc z) h
    (prefixWord (completionBits_le_reserved r c hr hc z h) bits)

/-- Pointwise code identity with the actual executable completion program.
The supplied common word is truncated at its computed state-dependent width. -/
theorem programTable_code
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ)
    (bits : Fin (PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r h) → Bool) :
    CompletionSamplerProgram.draw
      (CompletionSamplerSemantics.parameters (m := nr) (n := nc) d (coarseRows r c hr z) (coarseColumns r c hc z) h,
        List.ofFn bits) = matrixCode (programTable r c hr hc z h bits).val :=
  CompletionSamplerSemantics.draw_prefix_code (m := nr) (n := nc) d (dimension_fourteen r c hr hc)
    (coarseRows r c hr z) (coarseColumns r c hc z) (coarse_totals r c hr hc z) h _
    (completionBits_le_reserved r c hr hc z h) bits

theorem programTable_accuracy
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ) :
    variation (mapLaw (uniformLaw
      (α := Fin (PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r h) → Bool))
      (programTable r c hr hc z h))
      (LatticeCompletionAccuracy.originalUniform (coarseRows r c hr z) (coarseColumns r c hc z)
        (GreedyFeasibleTable.table _ _ (coarse_totals r c hr hc z))) ≤ dyadic h :=
  CompletionSamplerSemantics.padded_programTable_variation (m := nr) (n := nc) d (dimension_fourteen r c hr hc)
    (coarseRows r c hr z) (coarseColumns r c hc z) (coarse_totals r c hr hc z)
    (dimensions r c hr hc).1 (dimensions r c hr hc).2 (free_dimension r c hr hc)
    (coarse_row_lower r c hr hc z) (coarse_column_lower r c hr hc z) h _
    (completionBits_le_reserved r c hr hc z h)

/-- Exact physical completion returned by every reserved Boolean word. -/
def completionDraw
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ)
    (bits : Fin (PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r h) → Bool) :
    Fibre r c U L z := (finiteFibreEquiv r c hr hc z).symm (programTable r c hr hc z h bits)

def completionLaw
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ) : RationalLaw (Fibre r c U L z) :=
  mapLaw (uniformLaw
    (α := Fin (PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r h) → Bool))
    (completionDraw r c hr hc z h)

theorem completionLaw_accuracy
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ) :
    variation (completionLaw r c hr hc z h) (uniformLaw (α := Fibre r c U L z)) ≤ dyadic h := by
  let E := finiteFibreEquiv r c hr hc z
  letI : Nonempty (Table (coarseRows r c hr z) (coarseColumns r c hc z)) :=
    ⟨GreedyFeasibleTable.table _ _ (coarse_totals r c hr hc z)⟩
  change variation (mapLaw (uniformLaw (α := Fin (PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r h) → Bool))
    (fun bits => E.symm (programTable r c hr hc z h bits))) (uniformLaw (α := Fibre r c U L z)) ≤ _
  rw [mapLaw_equiv_output, ← equivLaw_uniform E.symm, variation_equiv]
  exact programTable_accuracy r c hr hc z h

/-- Transport the fixed computed-list completion law to any supplied
reference coordinates. This does not assume order invariance of dense laws. -/
def oracleFamily
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (h : ℕ) : OracleFamily r c U L := fun i j z =>
  equivLaw (referenceFibreMap r c U L i j z).symm (completionLaw r c hr hc z h)

theorem oracleFamily_accuracy
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (h : ℕ) :
    ∀ (i : LargeRows r U) (j : LargeColumns c U) (z : States r c U L), variation (oracleFamily r c hr hc h i j z)
      (uniformLaw (α := ReferenceTable r c U L i j z)) ≤ dyadic h := by
  intro i j z
  unfold oracleFamily
  rw [← equivLaw_uniform (referenceFibreMap r c U L i j z).symm, variation_equiv]
  exact completionLaw_accuracy r c hr hc z h

/-- Reference-table realization for the actual computed reference pair. -/
def referenceDraw
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ)
    (bits : Fin (PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r h) → Bool) :
    ReferenceTable r c U L (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none) z :=
  (referenceFibreMap r c U L (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none) z).symm (completionDraw r c hr hc z h bits)

theorem referenceDraw_law
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (z : States r c U L) (h : ℕ) :
    mapLaw (uniformLaw
      (α := Fin (PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r h) → Bool))
      (referenceDraw r c hr hc z h) = oracleFamily r c hr hc h (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none) z := by
  unfold referenceDraw oracleFamily completionLaw
  exact mapLaw_equiv_output _ _ _

/-- The actual computed pair used by the list program throughout the walk. -/
def outerLaw
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (htotal : ∑ i, r i = ∑ j, c j) (fallback : Table r c)
    (T R hStep hTerminal : ℕ) : RationalLaw (Table r c) :=
  PhysicalReferenceWalk.idealReferenceOracleOuterLaw r c htotal (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none) fallback T R
    (oracleFamily r c hr hc hStep) (oracleFamily r c hr hc hTerminal)

theorem outerLaw_variation
    (hr : 0 < (largeIndices (U, List.ofFn r)).length)
    (hc : 0 < (largeIndices (U, List.ofFn c)).length) (htotal : ∑ i, r i = ∑ j, c j) (fallback : Table r c)
    (T R hStep hTerminal : ℕ) :
    letI := table_nonempty r c htotal
    (variation (outerLaw r c hr hc htotal fallback T R hStep hTerminal)
      (uniformLaw (α := Table r c)) : ℝ) ≤
      Real.exp (-(R : ℝ) / successAllowance r c U) +
      (R : ℝ) * (massAllowance (J := Fin n) r U L * Real.exp (-(T : ℝ) / idealGapAllowance d)) +
      (R : ℝ) * ((T : ℝ) * (proposalAllowance d : ℝ) * (dyadic hStep : ℝ) +
        (dyadic hTerminal : ℝ)) :=
  PhysicalReferenceWalk.idealReferenceOracleOuterLaw_variation r c htotal (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none) fallback T R
    (oracleFamily r c hr hc hStep) (oracleFamily r c hr hc hTerminal)
    (dyadic hStep) (dyadic hTerminal) (dyadic_positive hStep).le
    (oracleFamily_accuracy r c hr hc hStep (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none))
    (oracleFamily_accuracy r c hr hc hTerminal (largeOptionEquiv r U hr none) (largeOptionEquiv c U hc none))

end
end Math115.ListedLatticeCompletion
