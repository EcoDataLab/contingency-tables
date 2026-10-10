/-
SPDX-License-Identifier: Apache-2.0
Executable greedy initialization and computed branch preparation at ideal scales.
Generic entry identities use the actual free-scale state-success equivalence.
Successful output is identified with the generic matrix reconstruction/test;
the complete outer-loop realizer and its composed cost remain separate.
-/
import Math115.PhysicalBooleanSampler
import Math115.LatticeProfileStep
import OAI.Combinatorics.ContingencyTables.Sampling.OriginalProfileProgram
import OAI.Combinatorics.ContingencyTables.Sampling.OuterMatrixSemantics
import OAI.Combinatorics.ContingencyTables.Transport.ReferenceCompletionEntries
import OAI.Combinatorics.ContingencyTables.Transport.BoundedProfileWalk

namespace Math115.LatticeSamplerPreparation

open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped
open ProfilePrograms DensePrograms

abbrev Margins := List ℕ × List ℕ

/-- Computable ideal padding on the original encoded dimensions. -/
def idealPadding (z : Margins) : ℕ := 3 * marginDimension z

def idealPaddingRealizer : Realizer idealPadding :=
  composition (f := fun z : Margins => (3, marginDimension z))
    (g := fun t : ℕ × ℕ => t.1 * t.2) (pair (constant 3) marginDimensionRealizer) multiply

theorem polynomial_idealPadding : PolynomialTime idealPaddingRealizer :=
  polynomial_composition (f := fun z : Margins => (3, marginDimension z))
    (g := fun t : ℕ × ℕ => t.1 * t.2)
    (polynomial_pair (polynomial_constant 3) polynomial_marginDimension) polynomial_multiply

/-- The original greedy matrix is the fixed outer fallback. -/
def initialFallback (z : Margins) : MatrixCode := GreedyFeasibleTable.listMatrix z.1 z.2

def initialFallbackRealizer : Realizer initialFallback := GreedyFeasibleTable.tableRealizer

theorem polynomial_initialFallback : PolynomialTime initialFallbackRealizer :=
  GreedyFeasibleTable.polynomial_table

/-- The retained initial views are read from the greedy original table,
using the new computed ideal catalogue and cutoff. -/
def initialViewInput (z : Margins) : OriginalViewInput :=
  ((PhysicalComputedProposal.idealMarginCatalog z, PhysicalComputedProposal.idealMarginThreshold z),
    initialFallback z)

def initialViewInputRealizer : Realizer initialViewInput :=
  pair (pair PhysicalComputedProposal.idealMarginCatalogRealizer
    PhysicalComputedProposal.idealMarginThresholdRealizer) initialFallbackRealizer

theorem polynomial_initialViewInput : PolynomialTime initialViewInputRealizer :=
  polynomial_pair (polynomial_pair PhysicalComputedProposal.polynomial_idealMarginCatalog
    PhysicalComputedProposal.polynomial_idealMarginThreshold) polynomial_initialFallback

def initialViews (z : Margins) : List ℕ × List ℕ := originalViews (initialViewInput z)

def initialViewsRealizer : Realizer initialViews := composition initialViewInputRealizer originalViewsRealizer

theorem polynomial_initialViews : PolynomialTime initialViewsRealizer :=
  polynomial_composition polynomial_initialViewInput polynomial_originalViews

def initialCheck (z : Margins) : ProfileCheckData :=
  PhysicalComputedProposal.idealPrepareProfileInput (z, initialViews z)

def initialCheckRealizer : Realizer initialCheck :=
  composition (pair identity initialViewsRealizer) PhysicalComputedProposal.idealPrepareProfileInputRealizer

theorem polynomial_initialCheck : PolynomialTime initialCheckRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_initialViews)
    PhysicalComputedProposal.polynomial_idealPrepareProfileInput

/-- Ordinary initialization configuration. The supplied precision is for
transition calls; a later terminal call may override it independently. -/
def initialConfiguration (p : Margins × ℕ) : ProfileConfiguration :=
  (((initialCheck p.1, idealPadding p.1), (marginDimension p.1, p.2)), initialViews p.1)

def initialConfigurationRealizer : Realizer initialConfiguration :=
  pair (pair (pair (composition first initialCheckRealizer) (composition first idealPaddingRealizer))
    (pair (composition first marginDimensionRealizer) second)) (composition first initialViewsRealizer)

theorem polynomial_initialConfiguration : PolynomialTime initialConfigurationRealizer :=
  polynomial_pair (polynomial_pair
    (polynomial_pair (polynomial_composition polynomial_first polynomial_initialCheck)
      (polynomial_composition polynomial_first polynomial_idealPadding))
    (polynomial_pair (polynomial_composition polynomial_first polynomial_marginDimension) polynomial_second))
    (polynomial_composition polynomial_first polynomial_initialViews)

def largeRows (z : Margins) : List ℕ := largeIndices (PhysicalComputedProposal.idealMarginThreshold z, z.1)
def largeColumns (z : Margins) : List ℕ := largeIndices (PhysicalComputedProposal.idealMarginThreshold z, z.2)

def largeRowsRealizer : Realizer largeRows :=
  composition (pair PhysicalComputedProposal.idealMarginThresholdRealizer first) largeIndicesRealizer

def largeColumnsRealizer : Realizer largeColumns :=
  composition (pair PhysicalComputedProposal.idealMarginThresholdRealizer second) largeIndicesRealizer

theorem polynomial_largeRows : PolynomialTime largeRowsRealizer :=
  polynomial_composition (polynomial_pair PhysicalComputedProposal.polynomial_idealMarginThreshold
    polynomial_first) polynomial_largeIndices

theorem polynomial_largeColumns : PolynomialTime largeColumnsRealizer :=
  polynomial_composition (polynomial_pair PhysicalComputedProposal.polynomial_idealMarginThreshold
    polynomial_second) polynomial_largeIndices

/-- The actual branch guard of the semantic sampler, computed from lists. -/
def bothLargeTest (z : Margins) : Bool :=
  decide (0 < (largeRows z).length) && decide (0 < (largeColumns z).length)

def bothLargeTestRealizer : Realizer bothLargeTest :=
  composition (pair
    (composition (pair (constant 0) (composition largeRowsRealizer listLength)) less)
    (composition (pair (constant 0) (composition largeColumnsRealizer listLength)) less)) boolAnd

theorem polynomial_bothLargeTest : PolynomialTime bothLargeTestRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition (polynomial_pair (polynomial_constant 0)
      (polynomial_composition polynomial_largeRows polynomial_listLength)) polynomial_less)
    (polynomial_composition (polynomial_pair (polynomial_constant 0)
      (polynomial_composition polynomial_largeColumns polynomial_listLength)) polynomial_less)) polynomial_boolAnd

/-- Actual final full table reconstruction/test. The generic list program
computes the branch indices from its metadata; it does not sample again. -/
def finalTrial (x : OuterTrialInput) : Option MatrixCode := outerTrial x

def finalTrialRealizer : Realizer finalTrial := outerTrialRealizer

theorem polynomial_finalTrial : PolynomialTime finalTrialRealizer := polynomial_outerTrial


open OAI.CommonBasesFPRAS SmallGraphProfiles CompletionCounts PaddedCompletions
open PhysicalCompletionFibres FirstPaperPhysicalMarginal FirstPaperProfiles
open SmallContextCoordinates SmallContextFibres ReducedSmallChain
open PhysicalStationarySuccess PhysicalFiniteWalk PhysicalStateNonempty
open scoped BigOperators Classical
noncomputable section

section GenericEntries
universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Successful output unpads exactly the actual large cells at any scales.
This is the generic entry lemma needed by final program reconstruction. -/
lemma successful_entry (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (a : PhysicalStationarySuccess.SuccessfulStateJoint r c U L) (i : I) (j : J) :
    ((PhysicalStationarySuccess.originalStateSuccessEquiv r c U L).symm a).val i j =
      a.val.2.val.val.1 i j - largePadding (PhysicalStationarySuccess.large r c U) L i j := by
  change (PhysicalStationarySuccess.unpadSuccessfulJoint r c U L
    ((PhysicalStationarySuccess.successStateEquiv r c U L).symm a)).val i j = _
  rw [PhysicalStationarySuccess.unpadSuccessfulJoint_val]
  apply congrArg (fun t : ℕ => t - _)
  exact congrArg (fun t => t.val.1 i j)
    (PhysicalStationarySuccess.balancedJointFromState_projection r c U L a.val a.property.1)

lemma initialState_first (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (X : Table r c) (i : I) (j : J)
    (hs : firstPaperSmall r c U i j = true) :
    physicalProfile (firstPaperSmall r c U) (capacity r c U L) r c L (initialState r c U L X)
      (⟨(i, j), hs⟩, false) = X.val i j := by
  let a := PhysicalStationarySuccess.originalStateSuccessEquiv r c U L X
  have he := successful_entry r c U L a i j
  rw [Equiv.symm_apply_apply] at he
  have hp : largePadding (PhysicalStationarySuccess.large r c U) L i j = 0 := by
    simp only [PhysicalStationarySuccess.large, largePadding, Finset.mem_filter,
      Finset.mem_univ, true_and, hs, Bool.true_eq_false, ite_false]
  rw [hp, Nat.sub_zero] at he
  exact (a.val.2.property.2.2.1 i j hs).1.symm.trans he.symm

lemma initialState_second (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (X : Table r c)
    (a : Cells (firstPaperSmall r c U)) :
    physicalProfile (firstPaperSmall r c U) (capacity r c U L) r c L (initialState r c U L X)
      (a, true) = U - X.val a.val.1 a.val.2 := by
  have hb := (PhysicalStationarySuccess.originalStateSuccessEquiv r c U L X).property.1
  have hsum := (balanced_iff_cellSums (firstPaperSmall r c U) (capacity r c U L)
    (physicalProfile _ (capacity r c U L) r c L (initialState r c U L X))
    (fun a => naturalProfile_bounded (initialState r c U L X).val.val (a, true))).mp hb a
  have he := initialState_first r c U L X a.val.1 a.val.2 a.property
  have hcap := capacity_small r c U L a.val.1 a.val.2 a.property
  have heta : (⟨(a.val.1, a.val.2), a.property⟩ : Cells (firstPaperSmall r c U)) = a :=
    Subtype.ext (Prod.eta a.val)
  rw [heta] at he
  rw [he, hcap] at hsum
  omega

end GenericEntries

section FinitePreparation
variable {m n q : ℕ}
variable (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => IdealOracleScales.cutoff (I := Fin m) (J := Fin n)
local notation "L" => IdealOracleScales.padding (I := Fin m) (J := Fin n)
local notation "e₀" => PhysicalComputedProposal.computedCellEquiv r c U

lemma marginDimension_code : marginDimension (List.ofFn r, List.ofFn c) = d := by
  simp only [marginDimension, List.length_ofFn, dimensionAllowance, Fintype.card_fin]

lemma idealPadding_code : idealPadding (List.ofFn r, List.ofFn c) = L := by
  rw [idealPadding, marginDimension_code r c]
  rfl

lemma initialFallback_code (htotal : ∑ i, r i = ∑ j, c j) :
    initialFallback (List.ofFn r, List.ofFn c) =
      matrixCode (GreedyFeasibleTable.table r c htotal).val :=
  GreedyFeasibleTable.listMatrix_ofFn r c

lemma initialState_code (V W : ℕ) (e : Fin q ≃ Cells (firstPaperSmall r c V)) (X : Table r c) :
    PhysicalComputedProposal.stateCode r c V W e (initialState r c V W X) =
      (List.ofFn (fun i => X.val (e i).val.1 (e i).val.2),
       List.ofFn (fun i => V - X.val (e i).val.1 (e i).val.2)) := by
  apply Prod.ext
  · apply congrArg List.ofFn
    funext i
    exact initialState_first r c V W X _ _ (e i).property
  · apply congrArg List.ofFn
    funext i
    exact initialState_second r c V W X (e i)

/-- Generic retained-view program semantics re-proved at free scales.
The old paper's initialViews_code/initialCheck_code is not used. -/
lemma originalViews_free_code (V W : ℕ) (e : Fin q ≃ Cells (firstPaperSmall r c V)) (X : Table r c) :
    originalViews ((cellCatalog (firstPaperSmall r c V) e, V), matrixCode X.val) =
      PhysicalComputedProposal.stateCode r c V W e (initialState r c V W X) := by
  rw [initialState_code r c V W e X]
  have he : originalFirstView ((cellCatalog (firstPaperSmall r c V) e, V), matrixCode X.val) =
      List.ofFn (fun i => X.val (e i).val.1 (e i).val.2) := by
    simp only [originalFirstView, cellCatalog, List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    exact matrixEntry_code X.val (e i).val.1 (e i).val.2
  unfold originalViews
  rw [he, complementValues_ofFn]

lemma initialViews_code (htotal : ∑ i, r i = ∑ j, c j) :
    initialViews (List.ofFn r, List.ofFn c) =
      PhysicalComputedProposal.computedStateCode r c U L
        (initialState r c U L (GreedyFeasibleTable.table r c htotal)) := by
  unfold initialViews initialViewInput
  rw [initialFallback_code r c htotal, PhysicalComputedProposal.idealMarginThreshold_ofFn]
  have hc : PhysicalComputedProposal.idealMarginCatalog (List.ofFn r, List.ofFn c) =
      cellCatalog (firstPaperSmall r c U) e₀ := by
    rw [PhysicalComputedProposal.computedCellEquiv_catalog]
    unfold PhysicalComputedProposal.idealMarginCatalog
    rw [PhysicalComputedProposal.idealMarginThreshold_ofFn]
    rfl
  rw [hc]
  exact originalViews_free_code r c U L e₀ (GreedyFeasibleTable.table r c htotal)

lemma initialCheck_code (htotal : ∑ i, r i = ∑ j, c j) :
    initialCheck (List.ofFn r, List.ofFn c) =
      PhysicalComputedProposal.stateCodeData r c U L e₀
        (initialState r c U L (GreedyFeasibleTable.table r c htotal)) := by
  unfold initialCheck
  rw [initialViews_code r c htotal]
  exact PhysicalComputedProposal.idealPrepareProfileInput_eq r c _

lemma initialConfiguration_code (htotal : ∑ i, r i = ∑ j, c j) (hStep : ℕ) :
    initialConfiguration ((List.ofFn r, List.ofFn c), hStep) =
      (((PhysicalComputedProposal.stateCodeData r c U L e₀
          (initialState r c U L (GreedyFeasibleTable.table r c htotal)), L), (d, hStep)),
       PhysicalComputedProposal.computedStateCode r c U L
          (initialState r c U L (GreedyFeasibleTable.table r c htotal))) := by
  unfold initialConfiguration
  rw [initialCheck_code r c htotal, idealPadding_code r c, marginDimension_code r c,
    initialViews_code r c htotal]

lemma bothLargeTest_code :
    bothLargeTest (List.ofFn r, List.ofFn c) = true ↔ PhysicalBooleanSampler.bothLarge r c := by
  simp only [bothLargeTest, Bool.and_eq_true, decide_eq_true_eq, largeRows, largeColumns,
    PhysicalComputedProposal.idealMarginThreshold_ofFn, PhysicalBooleanSampler.bothLarge]

end FinitePreparation

section FinalReference
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (V W : ℕ)
local notation "small" => firstPaperSmall r c V
local notation "B" => capacity r c V W
local notation "e₀" => PhysicalComputedProposal.computedCellEquiv r c V
variable (hr : 0 < (largeIndices (V, List.ofFn r)).length)
variable (hc : 0 < (largeIndices (V, List.ofFn c)).length)

def listedTable (z : States r c V W) (A : Fibre r c V W z) :
    Table (listedRows r c V W B hr z) (listedColumns r c V W B hc z) :=
  listedFibreEquiv r c V W B hr hc z
    (physical_paper_capacity _ r c _ W V dimension_le_allowance z) A

lemma listedTable_entry (z : States r c V W) (A : Fibre r c V W z) (i) (j) :
    (listedTable r c V W hr hc z A).val i j =
      A.val.val.1 (largeOptionEquiv r V hr i).val (largeOptionEquiv c V hc j).val := by
  rw [listedTable, listedFibreEquiv_entry, referenceFibreEquiv_entry]
  simp only [listedReferenceIndex, Equiv.trans_apply, Equiv.apply_symm_apply]

lemma paddingTest_listed (z : States r c V W) (A : Fibre r c V W z) :
    paddingTest (W, tableOutput (listedTable r c V W hr hc z A)) = true ↔
      ∀ i j, small i j = false → W ≤ A.val.val.1 i j := by
  rw [paddingTest_tableOutput]
  simp_rw [listedTable_entry]
  constructor
  · intro h i j hij
    obtain ⟨hi, hj⟩ := (firstPaperSmall_false_iff r c V i j).mp hij
    obtain ⟨a, ha⟩ := (largeOptionEquiv r V hr).surjective ⟨i, hi⟩
    obtain ⟨b, hb⟩ := (largeOptionEquiv c V hc).surjective ⟨j, hj⟩
    simpa only [ha, hb] using h a b
  · intro h i j
    exact h _ _ ((firstPaperSmall_false_iff r c V _ _).mpr
      ⟨(largeOptionEquiv r V hr i).property, (largeOptionEquiv c V hc j).property⟩)

def referenceOutputData (z : States r c V W) (A : Fibre r c V W z) : OuterTableData :=
  outputData ((PhysicalComputedProposal.stateCodeData r c V W e₀ z, W),
    tableOutput (listedTable r c V W hr hc z A))

lemma referenceOutputData_eq (z : States r c V W) (A : Fibre r c V W z) :
    referenceOutputData r c V W hr hc z A =
      (((cellCatalog small e₀, PhysicalComputedProposal.computedStateCode r c V W z),
        (largeIndices (V, List.ofFn r), largeIndices (V, List.ofFn c))),
        ((V, W), tableOutput (listedTable r c V W hr hc z A))) := rfl

lemma referenceOutputEntry_large (z : States r c V W) (A : Fibre r c V W z) (i) (j) :
    outputEntry (referenceOutputData r c V W hr hc z A,
      ((largeOptionEquiv r V hr i).val.val, (largeOptionEquiv c V hc j).val.val)) =
        A.val.val.1 (largeOptionEquiv r V hr i).val (largeOptionEquiv c V hc j).val - W := by
  have hs : small (largeOptionEquiv r V hr i).val (largeOptionEquiv c V hc j).val = false :=
    (firstPaperSmall_false_iff r c V _ _).mpr
      ⟨(largeOptionEquiv r V hr i).property, (largeOptionEquiv c V hc j).property⟩
  have hnot := (mem_cellCatalog small e₀
    ((largeOptionEquiv r V hr i).val, (largeOptionEquiv c V hc j).val)).not.mpr
      (by simp only [hs, Bool.false_eq_true, not_false_eq_true])
  have hpos := List.idxOf_eq_length hnot
  have hbad : ¬ outputCellPosition (referenceOutputData r c V W hr hc z A,
      ((largeOptionEquiv r V hr i).val.val, (largeOptionEquiv c V hc j).val.val)) <
      (referenceOutputData r c V W hr hc z A).1.1.1.length := by
    change ¬ (cellCatalog small e₀).idxOf
      ((largeOptionEquiv r V hr i).val.val, (largeOptionEquiv c V hc j).val.val) <
      (cellCatalog small e₀).length
    rw [hpos]
    exact Nat.lt_irrefl _
  rw [outputEntry, if_neg hbad]
  change matrixEntry (tableOutput (listedTable r c V W hr hc z A),
    ((largeIndices (V, List.ofFn r)).idxOf (largeOptionEquiv r V hr i).val.val,
      (largeIndices (V, List.ofFn c)).idxOf (largeOptionEquiv c V hc j).val.val)) - W = _
  rw [largeOption_index, largeOption_index, tableOutput_entry, listedTable_entry]

lemma referenceOutputEntry_small (z : States r c V W) (A : Fibre r c V W z)
    (i : Fin m) (j : Fin n) (hs : small i j = true) :
    outputEntry (referenceOutputData r c V W hr hc z A, (i.val, j.val)) = A.val.val.1 i j := by
  rw [referenceOutputData_eq]
  have he := outputEntry_small small e₀ (physicalProfile small B r c W z)
    (largeIndices (V, List.ofFn r)) (largeIndices (V, List.ofFn c)) V W
    (tableOutput (listedTable r c V W hr hc z A)) i j hs
  exact he.trans (by
    simpa only [smallView, hs, dite_eq_left] using (A.property.2.2.1 i j hs).1.symm)

lemma referenceOutputEntry (z : States r c V W) (A : Fibre r c V W z) (i : Fin m) (j : Fin n) :
    outputEntry (referenceOutputData r c V W hr hc z A, (i.val, j.val)) =
      A.val.val.1 i j - largePadding (PhysicalStationarySuccess.large r c V) W i j := by
  cases hs : small i j with
  | true =>
    simpa only [PhysicalStationarySuccess.large, largePadding, Finset.mem_filter,
      Finset.mem_univ, true_and, hs, Bool.true_eq_false, ite_false, Nat.sub_zero] using
        referenceOutputEntry_small r c V W hr hc z A i j hs
  | false =>
    obtain ⟨hi, hj⟩ := (firstPaperSmall_false_iff r c V i j).mp hs
    obtain ⟨a, ha⟩ := (largeOptionEquiv r V hr).surjective ⟨i, hi⟩
    obtain ⟨b, hb⟩ := (largeOptionEquiv c V hc).surjective ⟨j, hj⟩
    simpa only [ha, hb, PhysicalStationarySuccess.large, largePadding, Finset.mem_filter,
      Finset.mem_univ, true_and, hs, ite_true] using referenceOutputEntry_large r c V W hr hc z A a b

/-- Balance is checked on exactly the stored complementary profile views. -/
lemma balancedTest_stateCode (z : States r c V W) :
    balancedTest (PhysicalComputedProposal.computedStateCode r c V W z, V) = true ↔
      Balanced small B (physicalProfile small B r c W z) := by
  rw [PhysicalComputedProposal.computedStateCode, PhysicalComputedProposal.stateCode,
    profileCode, viewList, viewList, balancedTest_ofFn,
    balanced_iff_cellSums small B (physicalProfile small B r c W z)
      (fun a => naturalProfile_bounded z.val.val (a, true))]
  constructor
  · intro h a
    simpa only [Equiv.apply_symm_apply, capacity_small r c V W _ _ a.property] using h (e₀.symm a)
  · intro h i
    simpa only [capacity_small r c V W _ _ (e₀ i).property] using h (e₀ i)

lemma referenceOutputSuccess (z : States r c V W) (A : Fibre r c V W z) :
    outerSuccess (referenceOutputData r c V W hr hc z A) = true ↔
      PhysicalStationarySuccess.StateJointSuccess r c V W ⟨z, A⟩ := by
  rw [referenceOutputData_eq]
  change (balancedTest (PhysicalComputedProposal.computedStateCode r c V W z, V) &&
    paddingTest (W, tableOutput (listedTable r c V W hr hc z A))) = true ↔ _
  rw [Bool.and_eq_true, balancedTest_stateCode r c V W z, paddingTest_listed]
  rfl

lemma referenceOutputMatrix (a : PhysicalStationarySuccess.SuccessfulStateJoint r c V W) :
    outputMatrix (prepareOutput ((PhysicalComputedProposal.stateCodeData r c V W e₀ a.val.1, W),
      tableOutput (listedTable r c V W hr hc a.val.1 a.val.2))) =
        matrixCode ((PhysicalStationarySuccess.originalStateSuccessEquiv r c V W).symm a).val := by
  change outputMatrix ((List.ofFn r, List.ofFn c), referenceOutputData r c V W hr hc a.val.1 a.val.2) = _
  rw [outputMatrix_code]
  apply congrArg matrixCode
  funext i j
  rw [referenceOutputEntry, successful_entry]

/-- Pointwise final-trial seam for the actual listed completion, at free
scales. Only balance and padding success permit conversion to Table r c. -/
theorem outerTrial_reference_free_code (z : States r c V W) (A : Fibre r c V W z) :
    outerTrial ((PhysicalComputedProposal.stateCodeData r c V W e₀ z, W),
      tableOutput (listedTable r c V W hr hc z A)) =
        (PhysicalStationaryLaw.stateTrial r c V W ⟨z, A⟩).map (fun T => matrixCode T.val) := by
  by_cases h : PhysicalStationarySuccess.StateJointSuccess r c V W ⟨z, A⟩
  · have hp := (referenceOutputSuccess r c V W hr hc z A).mpr h
    calc
      _ = some (outputMatrix (prepareOutput ((PhysicalComputedProposal.stateCodeData r c V W e₀ z, W),
          tableOutput (listedTable r c V W hr hc z A)))) := ite_eq_left hp
      _ = some (matrixCode ((PhysicalStationarySuccess.originalStateSuccessEquiv r c V W).symm
          ⟨⟨z, A⟩, h⟩).val) := congrArg some (referenceOutputMatrix r c V W hr hc ⟨⟨z, A⟩, h⟩)
      _ = _ := by
        simp only [PhysicalStationaryLaw.stateTrial, FirstSuccess.partialEquivDraw, dite_eq_left h, Option.map_some]
  · have hp : outerSuccess (referenceOutputData r c V W hr hc z A) ≠ true :=
      fun hp => h ((referenceOutputSuccess r c V W hr hc z A).mp hp)
    calc
      _ = none := ite_eq_right hp
      _ = _ := by
        simp only [PhysicalStationaryLaw.stateTrial, FirstSuccess.partialEquivDraw, dite_eq_right h, Option.map_none]

end FinalReference

section IdealFinal
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "U" => IdealOracleScales.cutoff (I := Fin m) (J := Fin n)
local notation "L" => IdealOracleScales.padding (I := Fin m) (J := Fin n)
local notation "e₀" => PhysicalComputedProposal.computedCellEquiv r c U
variable (hr : 0 < (largeIndices (IdealOracleScales.cutoff (I := Fin m) (J := Fin n), List.ofFn r)).length)
variable (hc : 0 < (largeIndices (IdealOracleScales.cutoff (I := Fin m) (J := Fin n), List.ofFn c)).length)

/-- Ideal-scale wrapper for the exact terminal/listed final reconstruction. -/
theorem outerTrial_reference_code (z : States r c U L) (A : Fibre r c U L z) :
    outerTrial ((PhysicalComputedProposal.stateCodeData r c U L e₀ z, L),
      tableOutput (listedTable r c U L hr hc z A)) =
        (PhysicalStationaryLaw.stateTrial r c U L ⟨z, A⟩).map (fun T => matrixCode T.val) :=
  outerTrial_reference_free_code r c U L hr hc z A

end IdealFinal
end
end Math115.LatticeSamplerPreparation
