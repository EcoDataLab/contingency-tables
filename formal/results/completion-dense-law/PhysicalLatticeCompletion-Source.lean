/-
SPDX-License-Identifier: Apache-2.0
The lattice completion law on the actual physical reference residuals.
Reference rows/columns are relabeled by exact table equivalences. Geometry,
quarter acceptance and finite retry accuracy are supplied by proved modules.
-/
import Math115.DilatedCompletionMargins
import Math115.PhysicalApproximateOracle
import Math115.LatticeCompletionAccuracy
import Math115.DenseLatticeCompletionProvedInputs

namespace Math115.PhysicalLatticeCompletion
open OAI.ContingencyTables OAI.CommonBasesFPRAS
open ReducedSmallChain PhysicalCompletionOracle DilatedCompletionMargins PhysicalRationalKernel
open PhysicalStationarySuccess PhysicalFiniteWalk PhysicalStateNonempty
open SmallGraphProfiles CompletionCounts PaddedCompletions
open PhysicalCompletionFibres FirstPaperPhysicalMarginal
open ResidualMixture FirstSuccess CompletionRetryBudget
open scoped BigOperators Classical

noncomputable section
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

abbrev RowTail (r : I → ℕ) (U : ℕ) (i₀ : LargeRows r U) := {i : LargeRows r U // i ≠ i₀}
abbrev ColumnTail (c : J → ℕ) (U : ℕ) (j₀ : LargeColumns c U) := {j : LargeColumns c U // j ≠ j₀}

abbrev rowFree (r : I → ℕ) (U : ℕ) (i₀ : LargeRows r U) := Fintype.card (RowTail r U i₀)
abbrev columnFree (c : J → ℕ) (U : ℕ) (j₀ : LargeColumns c U) := Fintype.card (ColumnTail c U j₀)

def rowIndex (r : I → ℕ) (U : ℕ) (i₀ : LargeRows r U) :
    Fin (rowFree r U i₀ + 1) ≃ Option (RowTail r U i₀) :=
  (finSuccEquiv _).trans (Equiv.optionCongr (Fintype.equivFin (RowTail r U i₀)).symm)

def columnIndex (c : J → ℕ) (U : ℕ) (j₀ : LargeColumns c U) :
    Fin (columnFree c U j₀ + 1) ≃ Option (ColumnTail c U j₀) :=
  (finSuccEquiv _).trans (Equiv.optionCongr (Fintype.equivFin (ColumnTail c U j₀)).symm)

def finiteRows (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (i₀ : LargeRows r U)
    (z : States r c U L) : Fin (rowFree r U i₀ + 1) → ℕ :=
  fun i => referenceRows r c U L (capacity r c U L) i₀ z (rowIndex r U i₀ i)

def finiteColumns (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (j₀ : LargeColumns c U)
    (z : States r c U L) : Fin (columnFree c U j₀ + 1) → ℕ :=
  fun j => referenceColumns r c U L (capacity r c U L) j₀ z (columnIndex c U j₀ j)

/-- Reindexing preserves every actual reference table and entry. -/
def finiteReferenceEquiv (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L) :
    ReferenceTable r c U L i₀ j₀ z ≃
      Table (finiteRows r c U L i₀ z) (finiteColumns r c U L j₀ z) :=
  tableReindex (rowIndex r U i₀) (columnIndex c U j₀)
    (referenceRows r c U L (capacity r c U L) i₀ z)
    (referenceColumns r c U L (capacity r c U L) j₀ z)

lemma finite_totals (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L) :
    (∑ i, finiteRows r c U L i₀ z i) = ∑ j, finiteColumns r c U L j₀ z j := by
  unfold finiteRows finiteColumns
  rw [(rowIndex r U i₀).sum_comp, (columnIndex c U j₀).sum_comp]
  exact reference_totals r c U L (capacity r c U L) i₀ j₀ z
    (physical_paper_capacity _ r c _ L U dimension_le_allowance z)

lemma row_count_eq (r : I → ℕ) (U : ℕ) (i₀ : LargeRows r U) :
    rowFree r U i₀ + 1 = Fintype.card (LargeRows r U) := by
  simpa only [Fintype.card_option] using Fintype.card_congr (Equiv.optionSubtypeNe i₀)

lemma column_count_eq (c : J → ℕ) (U : ℕ) (j₀ : LargeColumns c U) :
    columnFree c U j₀ + 1 = Fintype.card (LargeColumns c U) := by
  simpa only [Fintype.card_option] using Fintype.card_congr (Equiv.optionSubtypeNe j₀)

lemma finite_row_lower (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L)
    (i : Fin (rowFree r U i₀ + 1)) :
    (columnFree c U j₀ + 1) * L ≤ finiteRows r c U L i₀ z i := by
  rw [column_count_eq]
  exact reference_row_lower r c U L i₀ z (rowIndex r U i₀ i)

lemma finite_column_lower (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L)
    (j : Fin (columnFree c U j₀ + 1)) :
    (rowFree r U i₀ + 1) * L ≤ finiteColumns r c U L j₀ z j := by
  rw [row_count_eq]
  exact reference_column_lower r c U L j₀ z (columnIndex c U j₀ j)

lemma finite_dimensions (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) :
    rowFree r U i₀ + 1 ≤ dimensionAllowance (I := I) (J := J) ∧
      columnFree c U j₀ + 1 ≤ dimensionAllowance (I := I) (J := J) := by
  simpa only [Fintype.card_option] using
    And.intro (reference_block_dimensions r c U i₀ j₀).1
      (reference_block_dimensions r c U i₀ j₀).2.1

lemma finite_free_dimension (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) :
    rowFree r U i₀ * columnFree c U j₀ ≤ dimensionAllowance (I := I) (J := J) - 1 := by
  have hi : rowFree r U i₀ ≤ Fintype.card I :=
    (Fintype.card_subtype_le _).trans (Fintype.card_subtype_le _)
  have hj : columnFree c U j₀ ≤ Fintype.card J :=
    (Fintype.card_subtype_le _).trans (Fintype.card_subtype_le _)
  have hprod := Nat.mul_le_mul hi hj
  have hallow : Fintype.card I * Fintype.card J + 1 ≤ dimensionAllowance (I := I) (J := J) := by
    unfold dimensionAllowance
    nlinarith
  omega

/-- Having both actual reference indices gives the pinned dense sampler's
minimum dimension allowance, even for singleton reference blocks. -/
lemma dimension_fourteen (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) :
    14 ≤ dimensionAllowance (I := I) (J := J) := by
  have hi : 1 ≤ Fintype.card I := Fintype.card_pos_iff.mpr ⟨i₀.val⟩
  have hj : 1 ≤ Fintype.card J := Fintype.card_pos_iff.mpr ⟨j₀.val⟩
  unfold dimensionAllowance
  nlinarith

/-- Every actual finite reference row has a state-independent total bound.
This uses the full-block residual-total theorem, not a dense-law assumption. -/
lemma finite_row_upper (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (i₀ : LargeRows r U) (z : States r c U L) (i : Fin (rowFree r U i₀ + 1)) :
    finiteRows r c U L i₀ z i ≤ (∑ i, r i) + dimensionAllowance (I := I) (J := J) * L := by
  have hprod : Fintype.card (LargeRows r U) * Fintype.card (LargeColumns c U) ≤
      dimensionAllowance (I := I) (J := J) :=
    (Nat.mul_le_mul (Fintype.card_subtype_le _) (Fintype.card_subtype_le _)).trans
      dimension_le_allowance
  calc
    _ ≤ ∑ i, finiteRows r c U L i₀ z i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    _ = ∑ i, referenceRows r c U L (capacity r c U L) i₀ z i :=
      (rowIndex r U i₀).sum_comp _
    _ ≤ (∑ i, r i) + Fintype.card (LargeRows r U) * Fintype.card (LargeColumns c U) * L :=
      reference_total_upper r c U L i₀ z
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_right L hprod) _

local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "U" => IdealOracleScales.cutoff (I := I) (J := J)
local notation "L" => IdealOracleScales.padding (I := I) (J := J)

def finiteFallback (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L) :
    Table (finiteRows r c U L i₀ z) (finiteColumns r c U L j₀ z) :=
  GreedyFeasibleTable.table (finiteRows r c U L i₀ z) (finiteColumns r c U L j₀ z)
    (finite_totals r c U L i₀ j₀ z)

/-- A fine-table draw family on the actual reindexed residual margins. -/
abbrev FineOracleFamily (r : I → ℕ) (c : J → ℕ) :=
  (i₀ : LargeRows r U) → (j₀ : LargeColumns c U) → (z : States r c U L) →
    RationalLaw (LatticeCompletionFinite.FineTable (d^12)
      (finiteRows r c U L i₀ z) (finiteColumns r c U L j₀ z))

/-- Bounded lattice decoding/rejection followed by exact relabeling back
to the actual reference completion. All fallback probability is retained. -/
def latticeOracle (r : I → ℕ) (c : J → ℕ) (fine : FineOracleFamily r c) (h : ℕ) :
    OracleFamily r c U L := fun i₀ j₀ z =>
  equivLaw (finiteReferenceEquiv r c U L i₀ j₀ z).symm
    (retryLaw (fine i₀ j₀ z)
      (LatticeCompletionLaw.trial (d^12) (by have hd := dimension_fourteen r c U i₀ j₀; exact pow_pos (by omega) _)
        (finiteRows r c U L i₀ z) (finiteColumns r c U L j₀ z))
      (finiteFallback r c i₀ j₀ z) (retries h))

/-- The normalized all-state oracle accuracy follows from the proved
geometry and actual physical residual bounds. Only fine-draw TV remains
an explicit realization input in this reusable interface. -/
theorem latticeOracle_accuracy (r : I → ℕ) (c : J → ℕ) (fine : FineOracleFamily r c) (h : ℕ)
    (hfine : ∀ i₀ j₀ z, variation (fine i₀ j₀ z)
      (LatticeCompletionAccuracy.fineUniform (d^12)
        (by have hd := dimension_fourteen r c U i₀ j₀; exact pow_pos (by omega) _)
        (finiteRows r c U L i₀ z) (finiteColumns r c U L j₀ z) (finiteFallback r c i₀ j₀ z)) ≤
          dyadic (finePrecision h)) :
    ∀ i₀ j₀ z, variation (latticeOracle r c fine h i₀ j₀ z)
      (uniformLaw (α := ReferenceTable r c U L i₀ j₀ z)) ≤ dyadic h := by
  intro i₀ j₀ z
  let E := finiteReferenceEquiv r c U L i₀ j₀ z
  letI : Nonempty (Table (finiteRows r c U L i₀ z) (finiteColumns r c U L j₀ z)) :=
    ⟨finiteFallback r c i₀ j₀ z⟩
  have hacc := LatticeCompletionAccuracy.chosen_dilation_accuracy d
    (by have hd := dimension_fourteen r c U i₀ j₀; omega)
    (by simpa using finite_free_dimension r c U i₀ j₀)
    (finiteRows r c U L i₀ z) (finiteColumns r c U L j₀ z)
    (finite_totals r c U L i₀ j₀ z)
    (finite_row_lower r c U L i₀ j₀ z) (finite_column_lower r c U L i₀ j₀ z)
    (finiteFallback r c i₀ j₀ z) (fine i₀ j₀ z) h (hfine i₀ j₀ z)
  change variation (equivLaw E.symm _) (uniformLaw (α := ReferenceTable r c U L i₀ j₀ z)) ≤ _
  rw [← equivLaw_uniform E.symm, variation_equiv]
  exact hacc

theorem lattice_selected_step_accuracy (r : I → ℕ) (c : J → ℕ) [Nonempty (States r c U L)]
    (fine : FineOracleFamily r c) (h : ℕ)
    (hfine : ∀ i₀ j₀ z, variation (fine i₀ j₀ z)
      (LatticeCompletionAccuracy.fineUniform (d^12)
        (by have hd := dimension_fourteen r c U i₀ j₀; exact pow_pos (by omega) _)
        (finiteRows r c U L i₀ z) (finiteColumns r c U L j₀ z) (finiteFallback r c i₀ j₀ z)) ≤
          dyadic (finePrecision h)) (z : States r c U L) :
    variation (selectedStepLaw r c U L (latticeOracle r c fine h) z)
      (selectedTransitionLaw r c U L z) ≤ proposalAllowance d * dyadic h := by
  exact selectedStepLaw_variation r c U L (latticeOracle r c fine h) (dyadic h)
    (dyadic_positive h).le (latticeOracle_accuracy r c fine h hfine) z

theorem lattice_selected_terminal_accuracy (r : I → ℕ) (c : J → ℕ)
    (fine : FineOracleFamily r c) (h : ℕ)
    (hfine : ∀ i₀ j₀ z, variation (fine i₀ j₀ z)
      (LatticeCompletionAccuracy.fineUniform (d^12)
        (by have hd := dimension_fourteen r c U i₀ j₀; exact pow_pos (by omega) _)
        (finiteRows r c U L i₀ z) (finiteColumns r c U L j₀ z) (finiteFallback r c i₀ j₀ z)) ≤
          dyadic (finePrecision h)) (z : States r c U L) :
    variation (selectedCompletionLaw r c U L (latticeOracle r c fine h) z)
      (uniformLaw (α := Fibre r c U L z)) ≤ dyadic h := by
  exact selectedCompletionLaw_variation r c U L (latticeOracle r c fine h) (dyadic h)
    (dyadic_positive h).le (latticeOracle_accuracy r c fine h hfine) z


/-- The actual finite Boolean-word fine law at the reserved inner precision,
on every actual physical reference completion block. -/
def denseFineOracle (r : I → ℕ) (c : J → ℕ) (h : ℕ) : FineOracleFamily r c := fun i₀ j₀ z =>
  DenseLatticeCompletion.fineLaw d (dimension_fourteen r c U i₀ j₀)
    (finiteRows r c U L i₀ z) (finiteColumns r c U L j₀ z)
    (finite_totals r c U L i₀ j₀ z) (finePrecision h)

/-- Concrete normalized approximate ordinary-completion OracleFamily. -/
def denseOracle (r : I → ℕ) (c : J → ℕ) (h : ℕ) : OracleFamily r c U L :=
  latticeOracle r c (denseFineOracle r c h) h

/-- Actual-state accuracy with every dimension, residual-margin, geometric,
analytic and finite fine-law premise discharged. -/
theorem denseOracle_accuracy (r : I → ℕ) (c : J → ℕ) (h : ℕ) :
    ∀ i₀ j₀ z, variation (denseOracle r c h i₀ j₀ z)
      (uniformLaw (α := ReferenceTable r c U L i₀ j₀ z)) ≤ dyadic h := by
  apply latticeOracle_accuracy r c (denseFineOracle r c h) h
  intro i₀ j₀ z
  exact DenseLatticeCompletionProvedInputs.fineLaw_variation d (dimension_fourteen r c U i₀ j₀)
    (finiteRows r c U L i₀ z) (finiteColumns r c U L j₀ z)
    (finite_totals r c U L i₀ j₀ z) (finiteFallback r c i₀ j₀ z)
    (finite_dimensions r c U i₀ j₀).1 (finite_dimensions r c U i₀ j₀).2
    (by have he := finite_free_dimension r c U i₀ j₀; omega) (finePrecision h)

/-- The actual selected transition error, including the unchanged exact
unit branch when one large-block dimension is empty. -/
theorem dense_selected_step_accuracy (r : I → ℕ) (c : J → ℕ) [Nonempty (States r c U L)]
    (h : ℕ) (z : States r c U L) :
    variation (selectedStepLaw r c U L (denseOracle r c h) z)
      (selectedTransitionLaw r c U L z) ≤ proposalAllowance d * dyadic h :=
  selectedStepLaw_variation r c U L (denseOracle r c h) (dyadic h)
    (dyadic_positive h).le (denseOracle_accuracy r c h) z

/-- A fresh terminal call has the requested normalized error at every state;
the empty-block terminal completion retains its exact unique law. -/
theorem dense_selected_terminal_accuracy (r : I → ℕ) (c : J → ℕ) (h : ℕ) (z : States r c U L) :
    variation (selectedCompletionLaw r c U L (denseOracle r c h) z)
      (uniformLaw (α := Fibre r c U L z)) ≤ dyadic h :=
  selectedCompletionLaw_variation r c U L (denseOracle r c h) (dyadic h)
    (dyadic_positive h).le (denseOracle_accuracy r c h) z


/-- The concrete normalized dense completion families in both transition
and fresh terminal positions of the actual restarted physical walk law. -/
def denseOuterLaw (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j)
    (fallback : Table r c) (T R hStep hTerminal : ℕ) : RationalLaw (Table r c) :=
  PhysicalApproximateOracle.idealOracleOuterLaw r c htotal fallback T R
    (denseOracle r c hStep) (denseOracle r c hTerminal)

/-- Full normalized outer-law error with the concrete all-state completion
families. This is a law theorem; finite-bit walk/retry programs and their
machine costs remain separate obligations. -/
theorem denseOuterLaw_variation (r : I → ℕ) (c : J → ℕ) (htotal : ∑ i, r i = ∑ j, c j)
    (fallback : Table r c) (T R hStep hTerminal : ℕ) :
    letI := table_nonempty r c htotal
    (variation (denseOuterLaw r c htotal fallback T R hStep hTerminal)
      (uniformLaw (α := Table r c)) : ℝ) ≤
      Real.exp (-(R : ℝ) / successAllowance r c U) +
      (R : ℝ) * (massAllowance (J := J) r U L * Real.exp (-(T : ℝ) / idealGapAllowance d)) +
      (R : ℝ) * ((T : ℝ) * (proposalAllowance d : ℝ) * (dyadic hStep : ℝ) +
        (dyadic hTerminal : ℝ)) := by
  exact PhysicalApproximateOracle.idealOracleOuterLaw_variation r c htotal fallback T R
    (denseOracle r c hStep) (denseOracle r c hTerminal) (dyadic hStep) (dyadic hTerminal)
    (dyadic_positive hStep).le (dyadic_positive hTerminal).le
    (denseOracle_accuracy r c hStep) (denseOracle_accuracy r c hTerminal)


/-- Common fine-row bound for all states and all reference-index choices. -/
def fineRowBound (r : I → ℕ) : ℕ := d^12 * ((∑ i, r i) + d * L + 2 * d)

/-- Binary fine-margin allowance computed once from the original margins. -/
def fineBinaryLength (r : I → ℕ) : ℕ := Nat.clog 2 (fineRowBound (J := J) r + 2)

/-- A reserved fine-word width independent of state and reference choice. -/
def reservedFineBits (r : I → ℕ) (h : ℕ) : ℕ :=
  25 * (d + fineBinaryLength (J := J) r + finePrecision h + 1)^62

/-- Entire bounded completion reservation, also independent of state. -/
def reservedCompletionBits (r : I → ℕ) (h : ℕ) : ℕ :=
  retries h * reservedFineBits (J := J) r h

lemma dense_fine_row_upper (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L)
    (i : Option (Fin (rowFree r U i₀))) :
    DenseLatticeCompletion.denseRows (d^12) (columnFree c U j₀) (finiteRows r c U L i₀ z) i ≤
      fineRowBound (J := J) r := by
  have hrow := finite_row_upper r c U L i₀ z ((finSuccEquiv (rowFree r U i₀)).symm i)
  have hdim := (finite_dimensions r c U i₀ j₀).2
  have hin : finiteRows r c U L i₀ z ((finSuccEquiv (rowFree r U i₀)).symm i) +
      2 * (columnFree c U j₀ + 1) ≤ (∑ i, r i) + d * L + 2 * d := by omega
  exact Nat.mul_le_mul_left (d^12) hin

/-- Every state's actual dense fine draw fits the same reserved word. -/
theorem fineBits_le_reserved (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L) (h : ℕ) :
    DenseLatticeCompletion.fineBits d (finiteRows r c U L i₀ z) (finiteColumns r c U L j₀ z)
      (finePrecision h) ≤ reservedFineBits (J := J) r h := by
  exact DenseLatticeCompletion.fineBits_polynomial d (fineRowBound (J := J) r)
    (fineBinaryLength (J := J) r) (finePrecision h)
    (finiteRows r c U L i₀ z) (finiteColumns r c U L j₀ z)
    (by have he := finite_free_dimension r c U i₀ j₀; omega)
    (dense_fine_row_upper r c i₀ j₀ z) (le_refl _)

/-- State-dependent inner retry widths fit one common completion word.
Prefix truncation can therefore preserve every conditional draw law exactly. -/
theorem completionBits_le_reserved (r : I → ℕ) (c : J → ℕ)
    (i₀ : LargeRows r U) (j₀ : LargeColumns c U) (z : States r c U L) (h : ℕ) :
    DenseLatticeCompletion.completionBits d (finiteRows r c U L i₀ z)
      (finiteColumns r c U L j₀ z) h ≤ reservedCompletionBits (J := J) r h := by
  exact Nat.mul_le_mul_left (retries h) (fineBits_le_reserved r c i₀ j₀ z h)

end
end Math115.PhysicalLatticeCompletion
