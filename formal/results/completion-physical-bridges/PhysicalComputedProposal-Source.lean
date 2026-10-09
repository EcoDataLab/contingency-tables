/-
SPDX-License-Identifier: Apache-2.0
Computed physical proposal at free cutoff/padding scales. The literal list
programs are unchanged upstream programs; semantic wrappers are generalized
from openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
PolynomialTime concerns the encoded proposal and preparation only, not the
complete completion/walk sampler or its cost.
-/
import Math115.PhysicalCompletionOracle
import Math115.IdealOracleScales
import OAI.Combinatorics.ContingencyTables.Sampling.FirstPaperPreparedProposal

set_option maxHeartbeats 1200000

namespace Math115.PhysicalComputedProposal
open OAI.ContingencyTables OAI.CommonBasesFPRAS
open ReducedSmallChain PhysicalCompletionOracle PhysicalRationalKernel
open SmallGraphProfiles SmallContextCoordinates SmallContextFibres
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open CompletionCounts PaddedCompletions SmallContextEnumeration RowMajorEnumeration
open IntegerWeightedTransport ProfilePrograms ResidualMixture FirstSuccess FairBits
open scoped BigOperators Classical
universe u
noncomputable section

section Feasibility
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "small" => firstPaperSmall r c U
local notation "B" => capacity r c U L

/-- Padded residual margins can be computed before establishing feasibility. -/
def profileRows (z : SmallProfile small) (i : I) : ℕ :=
  r i-smallRow small (smallView small z false) i+rowLargeCount small i*L

def profileColumns (z : SmallProfile small) (j : J) : ℕ :=
  c j-smallColumn small B (smallView small z true) j+columnLargeCount small j*L

/-- Each field is a finite integer test on the candidate profile. -/
structure ProfileFeasible (z : SmallProfile small) : Prop where
  bounded : ∀ a,z a ≤ B a.1.val.1 a.1.val.2
  pattern : Pattern small B z
  residuals : OriginalResidualsNonnegative small B (smallView small z false) (smallView small z true) r c
  rows_outside : ∀ i,¬U ≤ r i → profileRows r c U L z i=0
  columns_outside : ∀ j,¬U ≤ c j → profileColumns r c U L z j=0
  totals : (∑ i,profileRows r c U L z i)=∑ j,profileColumns r c U L z j

omit [LinearOrder I] [LinearOrder J] in
lemma profile_capacity (z : SmallProfile small) :
    ∀ i j,small i j=false → (∑ k,profileRows r c U L z k) ≤ B i j :=
  paper_capacity_excludes_none small (smallView small z false) r d L U dimension_le_allowance

lemma physicalProfile_feasible (x : States r c U L) :
    ProfileFeasible r c U L (physicalProfile small B r c L x) := by
  have hcap := profile_capacity r c U L (physicalProfile small B r c L x)
  exact ⟨naturalProfile_bounded x.val.val,x.val.property,
    physical_original_residuals small B r c L x hcap,
    physical_residual_row_zero r c U L B x hcap,
    physical_residual_column_zero r c U L B x hcap,
    physical_residual_totals small B r c L x hcap⟩

/-- A passing arithmetic test constructs a completion by the greedy
rectangle algorithm, proving that its weight is strictly positive. -/
lemma profileFeasible_positive (z : SmallProfile small) (h : ProfileFeasible r c U L z) :
    0 < hardMarginal small B r c L z := by
  have hne := supported_completion_nonempty small
    (fun i => U ≤ r i) (fun j => U ≤ c j) (firstPaperSmall_false_iff r c U)
    (profileRows r c U L z) (profileColumns r c U L z) h.totals h.rows_outside h.columns_outside
  have hc := hardMarginal_eq_completionCount small B r c L z h.bounded (profile_capacity r c U L z)
  rw [ite_eq_left h.residuals] at hc
  rw [hc]
  exact Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hne)

/-- The successful integer tests recover an actual state without
searching the completion space. -/
def stateOfFeasible (z : SmallProfile small) (h : ProfileFeasible r c U L z) : States r c U L :=
  ⟨⟨(fun a => ⟨z a,Nat.lt_succ_of_le (h.bounded a)⟩),h.pattern⟩,
    profileFeasible_positive r c U L z h⟩

lemma stateOfFeasible_profile (z : SmallProfile small) (h : ProfileFeasible r c U L z) :
    physicalProfile small B r c L (stateOfFeasible r c U L z h)=z := rfl

/-- This is the complete test for membership in the chain's state space. -/
theorem profileFeasible_iff (z : SmallProfile small) :
    ProfileFeasible r c U L z ↔ ∃ x : States r c U L,physicalProfile small B r c L x=z := by
  constructor
  · intro h
    exact ⟨stateOfFeasible r c U L z h,rfl⟩
  · rintro ⟨x,rfl⟩
    exact physicalProfile_feasible r c U L x

/-- Failed candidates are discarded. Passing candidates retain all
completion multiplicity through the original physical state type. -/
def decodeProfile (z : SmallProfile small) : Option (States r c U L) :=
  if h : ProfileFeasible r c U L z then some (stateOfFeasible r c U L z h) else none

lemma decodeProfile_eq_some_iff (z : SmallProfile small) (x : States r c U L) :
    decodeProfile r c U L z=some x ↔ physicalProfile small B r c L x=z := by
  constructor
  · intro hx
    unfold decodeProfile at hx
    split_ifs at hx with h
    · have he := Option.some.inj hx
      rw [←he]
      exact stateOfFeasible_profile r c U L z h
  · intro hx
    have h : ProfileFeasible r c U L z := hx ▸ physicalProfile_feasible r c U L x
    rw [decodeProfile,dite_eq_left h]
    congr 1
    apply physicalProfile_injective small B r c L
    exact (stateOfFeasible_profile r c U L z h).trans hx.symm

end Feasibility

section ResidualTests
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
/-- The executable tests need bounds, a local pattern and the row/column
inequalities, with equality on small incident margins. No completion
enumeration or additional residual-total oracle is necessary. -/
theorem profileFeasible_of_lineTests (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (z : SmallProfile (firstPaperSmall r c U))
    (hb : ∀ a,z a ≤ capacity r c U L a.1.val.1 a.1.val.2)
    (hp : Pattern (firstPaperSmall r c U) (capacity r c U L) z)
    (hr : ∀ i,smallRow (firstPaperSmall r c U) (smallView (firstPaperSmall r c U) z false) i≤r i ∧
      (r i<U →
        smallRow (firstPaperSmall r c U) (smallView (firstPaperSmall r c U) z false) i=r i))
    (hc : ∀ j,smallColumn (firstPaperSmall r c U) (capacity r c U L)
      (smallView (firstPaperSmall r c U) z true) j≤c j ∧
      (c j<U →
        smallColumn (firstPaperSmall r c U) (capacity r c U L)
          (smallView (firstPaperSmall r c U) z true) j=c j)) :
    ProfileFeasible r c U L z := by
  refine ⟨hb,hp,⟨fun i => (hr i).1,fun j => (hc j).1⟩,?_,?_,?_⟩
  · intro i hi
    have hi' : r i<U := by omega
    unfold profileRows
    rw [(hr i).2 hi']
    simp [rowLargeCount,firstPaperSmall,hi']
  · intro j hj
    have hj' : c j<U := by omega
    unfold profileColumns
    rw [(hc j).2 hj']
    simp [columnLargeCount,firstPaperSmall,hj']
  · exact padded_residual_totals _ _ z r c _ htotal hp (fun i => (hr i).1) (fun j => (hc j).1)

lemma profileFeasible_lineTests (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (z : SmallProfile (firstPaperSmall r c U)) (h : ProfileFeasible r c U L z) :
    (∀ i,smallRow (firstPaperSmall r c U) (smallView (firstPaperSmall r c U) z false) i≤r i ∧
      (r i<U →
        smallRow (firstPaperSmall r c U) (smallView (firstPaperSmall r c U) z false) i=r i)) ∧
    (∀ j,smallColumn (firstPaperSmall r c U) (capacity r c U L)
      (smallView (firstPaperSmall r c U) z true) j≤c j ∧
      (c j<U →
        smallColumn (firstPaperSmall r c U) (capacity r c U L)
          (smallView (firstPaperSmall r c U) z true) j=c j)) := by
  constructor
  · intro i
    refine ⟨h.residuals.1 i,?_⟩
    intro hi
    have hz := h.rows_outside i (by omega)
    unfold profileRows at hz
    have hb := h.residuals.1 i
    omega
  · intro j
    refine ⟨h.residuals.2 j,?_⟩
    intro hj
    have hz := h.columns_outside j (by omega)
    unfold profileColumns at hz
    have hb := h.residuals.2 j
    omega

end ResidualTests

section Validator
variable {m n q : ℕ}

theorem profileTest_iff (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (e : Fin q ≃ Cells (firstPaperSmall r c U))
    (z : SmallProfile (firstPaperSmall r c U)) :
    profileTest (((cellCatalog (firstPaperSmall r c U) e,
      (viewList (firstPaperSmall r c U) e z false,viewList (firstPaperSmall r c U) e z true)),
      (List.ofFn r,List.ofFn c)),U)=true ↔
        ProfileFeasible r c U L z := by
  let small := firstPaperSmall r c U
  let B := capacity r c U L
  have hU (a : Cells small) : B a.val.1 a.val.2=U :=
    capacity_small r c U L _ _ a.property
  have hb : (∀ a,z a≤U) ↔ ∀ a,z a≤B a.1.val.1 a.1.val.2 := by
    simp only [hU]
  simp only [profileTest,Bool.and_eq_true,cellCatalog,viewList,List.length_ofFn,
    decide_true,true_and]
  change (boundedValues (U,viewList small e z false)=true ∧
    (boundedValues (U,viewList small e z true)=true ∧
    (patternTest ((viewList small e z false,viewList small e z true),U)=true ∧
    (validMargins true (((cellCatalog small e,viewList small e z false),
      (List.ofFn r,List.ofFn c)),U)=true ∧
    validMargins false (((cellCatalog small e,complementValues (U,viewList small e z true)),
      (List.ofFn r,List.ofFn c)),U)=true)))) ↔ _
  constructor
  · rintro ⟨hx,hy,hp,hr,hc⟩
    have hbound : ∀ a,z a≤U := (boundedValues_views small e z U).mp (by simpa using And.intro hx hy)
    apply profileFeasible_of_lineTests r c U L htotal z (hb.mp hbound)
    · exact (patternTest_views small B e z U hU (fun a => hb.mp hbound (a,true))).mp hp
    · exact (validRows_iff small e z r c U).mp hr
    · exact (validColumns_iff small e B z r c U hU).mp hc
  · intro h
    have hbound := hb.mpr h.bounded
    have hh := (boundedValues_views small e z U).mpr hbound
    have hxy := Bool.and_eq_true_iff.mp hh
    have hl := profileFeasible_lineTests r c U L z h
    refine ⟨hxy.1,hxy.2,?_,?_,?_⟩
    · exact (patternTest_views small B e z U hU (fun a => h.bounded (a,true))).mpr h.pattern
    · exact (validRows_iff small e z r c U).mpr hl.1
    · exact (validColumns_iff small e B z r c U hU).mpr hl.2

end Validator

section CodeValidation
variable {m n q : ℕ}
/-- For arbitrary input lists, the Boolean program succeeds exactly
when those lists encode an actual positive-completion state. -/
theorem profileTest_code_iff (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (e : Fin q ≃ Cells (firstPaperSmall r c U))
    (v : List ℕ×List ℕ) :
    profileTest (codeCheckData (cellCatalog (firstPaperSmall r c U) e) (List.ofFn r) (List.ofFn c)
      (U) v)=true ↔
      ∃ x : States r c U L,profileCode (firstPaperSmall r c U) e
        (physicalProfile (firstPaperSmall r c U) (capacity r c U L) r c
          (L) x)=v := by
  constructor
  · intro h
    have hx : v.1.length=q := by
      have hh := (Bool.and_eq_true_iff.mp h).1
      simpa only [codeCheckData,cellCatalog,List.length_ofFn,decide_eq_true_eq] using hh
    have hy : v.2.length=q := by
      have hh := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1
      simpa only [codeCheckData,cellCatalog,List.length_ofFn,decide_eq_true_eq] using hh
    let z := profileOfCode (firstPaperSmall r c U) e v
    have hz : profileCode (firstPaperSmall r c U) e z=v := profileCode_ofCode _ _ v hx hy
    have hp : ProfileFeasible r c U L z := by
      apply (profileTest_iff r c U L htotal e z).mp
      change profileTest (codeCheckData (cellCatalog (firstPaperSmall r c U) e)
        (List.ofFn r) (List.ofFn c) (U)
        (profileCode (firstPaperSmall r c U) e z))=true
      rwa [hz]
    exact ⟨stateOfFeasible r c U L z hp,hz⟩
  · rintro ⟨x,rfl⟩
    exact (profileTest_iff r c U L htotal e _).mpr (physicalProfile_feasible r c U L x)

end CodeValidation

section Arithmetic
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
variable (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
local notation "d" => dimensionAllowance (I := I) (J := J)
local notation "small" => firstPaperSmall r c U
local notation "B" => capacity r c U L
local notation "profile" => physicalProfile small B r c L

/-- A directed repair is identified by its two defect cells. -/
def ArithmeticRepair (v w : SmallProfile small) : Prop :=
  ∃ st : Cells small×Cells small,
    IsDefect (smallView small v false) (smallQ small B v) st.1.val st.2.val ∧
      w=repairedProfile small B v st.1.val st.2.val

/-- All predicates are bounded integer-coordinate tests. -/
def ArithmeticEdge (v w : SmallProfile small) : Prop :=
  (∃ i j,i≠j ∧ 0<v j ∧ w=exchangeTarget v i j) ∨
    ArithmeticRepair r c U L v w ∨ ArithmeticRepair r c U L w v

lemma arithmeticRepair_iff (x y : States r c U L) :
    ArithmeticRepair r c U L (profile x) (profile y) ↔
      ∃ z : PositiveDefects small B r c L,
        naturalProfile z.val=profile x ∧
        rawChoice small U (wordChoices small U
          (repairWord r c U L B (capacity_small r c U L) z))=profile y := by
  constructor
  · rintro ⟨st,hd,hy⟩
    let z : PositiveDefects small B r c L :=
      ⟨x.val.val,⟨st.1.val,st.2.val,st.1.property,st.2.property,hd⟩,x.property⟩
    refine ⟨z,rfl,?_⟩
    rw [repairWord_profile]
    have hl : defectLabels small B r c L z=st := defectLabels_eq_of_spec small B r c L z st hd
    rw [hl]
    exact hy.symm
  · rintro ⟨z,hx,hy⟩
    refine ⟨defectLabels small B r c L z,?_,?_⟩
    · rw [←hx]
      exact defectLabels_spec small B r c L z
    · rw [←hy,repairWord_profile,hx]

/-- On actual states the arithmetic test is exactly the graph relation
used in the Poincare and mixing proofs. -/
theorem arithmeticEdge_iff (x y : States r c U L) :
    ArithmeticEdge r c U L (profile x) (profile y) ↔
      physicalAdjacent r c U L B (capacity_small r c U L) x y := by
  have hx : profile x ∈ vertices small B :=
    (mem_vertices_iff small B _).mpr ⟨naturalProfile_bounded x.val.val,x.val.property⟩
  have hy : profile y ∈ vertices small B :=
    (mem_vertices_iff small B _).mpr ⟨naturalProfile_bounded y.val.val,y.val.property⟩
  rw [ArithmeticEdge,←adjacent_iff_arithmetic,arithmeticRepair_iff,arithmeticRepair_iff]
  change _ ↔ (profile x,profile y) ∈ physicalEdges small B ∪
    repairEdges r c U L B (capacity_small r c U L)
  simp only [Finset.mem_union,physicalEdges,Finset.mem_filter,Finset.mem_product,
    hx,hy,true_and,repairEdges,Finset.mem_image,Finset.mem_univ,Prod.mk.injEq]
  constructor
  · rintro (he|he|he)
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · obtain ⟨z,hz,hw⟩ := he
      exact Or.inr (Or.inr ⟨z,hw,hz⟩)
  · rintro (he|he|he)
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · obtain ⟨z,hz,hw⟩ := he
      exact Or.inr (Or.inr ⟨z,hw,hz⟩)

end Arithmetic

section Neighbors
variable {m n q : ℕ}

theorem mem_rawCodeNeighbors (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (e : Fin q ≃ Cells (firstPaperSmall r c U)) (x y : States r c U L) :
    profileCode (firstPaperSmall r c U) e (physicalProfile (firstPaperSmall r c U) (capacity r c U L) r c
      (L) y) ∈
        rawCodeNeighbors (codeCheckData (cellCatalog (firstPaperSmall r c U) e)
          (List.ofFn r) (List.ofFn c) (U)
          (profileCode (firstPaperSmall r c U) e (physicalProfile (firstPaperSmall r c U) (capacity r c U L) r c
            (L) x))) ↔
      ArithmeticEdge r c U L
        (physicalProfile (firstPaperSmall r c U) (capacity r c U L) r c
          (L) x)
        (physicalProfile (firstPaperSmall r c U) (capacity r c U L) r c
          (L) y) := by
  let small := firstPaperSmall r c U
  let B := capacity r c U L
  let v := physicalProfile small B r c L x
  let w := physicalProfile small B r c L y
  have hU : ∀ a : Cells small,B a.val.1 a.val.2=U :=
    fun a => capacity_small r c U L _ _ a.property
  have hv : ∀ a : Cells small,v (a,true)≤B a.val.1 a.val.2 :=
    fun a => (physicalProfile_feasible r c U L x).bounded (a,true)
  have hw : ∀ a,w a≤B a.1.val.1 a.1.val.2 := (physicalProfile_feasible r c U L y).bounded
  change profileCode small e w ∈ rawCodeNeighbors
    (codeCheckData (cellCatalog small e) (List.ofFn r) (List.ofFn c) U (profileCode small e v)) ↔
      ArithmeticEdge r c U L v w
  simp only [rawCodeNeighbors,codeCheckData,List.mem_append]
  rw [mem_codeExchangeList,mem_forwardRepairList small e B U hU v hv,
    mem_checkedInverseRepairList small e B U hU v w hw]
  simp only [(profileCode_injective small e).eq_iff,ArithmeticEdge,ArithmeticRepair,Prod.exists]
  rfl

theorem mem_codeNeighbors (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
    (htotal : (∑ i,r i)=∑ j,c j) (e : Fin q ≃ Cells (firstPaperSmall r c U)) (x y : States r c U L) :
    profileCode (firstPaperSmall r c U) e (physicalProfile (firstPaperSmall r c U) (capacity r c U L) r c
      (L) y) ∈
        codeNeighbors (codeCheckData (cellCatalog (firstPaperSmall r c U) e)
          (List.ofFn r) (List.ofFn c) (U)
          (profileCode (firstPaperSmall r c U) e (physicalProfile (firstPaperSmall r c U) (capacity r c U L) r c
            (L) x))) ↔
      physicalAdjacent r c (U)
        (L) (capacity r c U L)
        (capacity_small r c U L) x y := by
  rw [codeNeighbors,List.mem_dedup,List.mem_filter]
  have hp := (profileTest_iff r c U L htotal e
    (physicalProfile (firstPaperSmall r c U) (capacity r c U L) r c
      (L) y)).mpr (physicalProfile_feasible r c U L y)
  change _ ∧ _ ↔ _
  have hc : profileTest (candidateData
      (codeCheckData (cellCatalog (firstPaperSmall r c U) e) (List.ofFn r) (List.ofFn c)
        (U)
        (profileCode (firstPaperSmall r c U) e (physicalProfile (firstPaperSmall r c U) (capacity r c U L) r c
          (L) x)),
        profileCode (firstPaperSmall r c U) e (physicalProfile (firstPaperSmall r c U) (capacity r c U L) r c
          (L) y)))=true := hp
  simp only [hc,and_true]
  rw [mem_rawCodeNeighbors,arithmeticEdge_iff]

end Neighbors

lemma physicalProposalLaw_mass_some {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
    (U L : ℕ) (x y : States r c U L) :
    (physicalProposalLaw r c U L x).mass (some y) = unitMoveRat r c U L x y := rfl

section CodeProposal
variable {m n q : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (e : Fin q ≃ Cells (firstPaperSmall r c U))
local notation "small" => firstPaperSmall r c U
local notation "B" => capacity r c U L
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => Nat.clog 2 (32*d^2)

def stateCode (x : States r c U L) : List ℕ×List ℕ :=
  profileCode small e (physicalProfile small B r c L x)

def stateCodeData (x : States r c U L) : ProfileCheckData :=
  codeCheckData (cellCatalog small e) (List.ofFn r) (List.ofFn c) U (stateCode r c U L e x)

def decodeStateCode (v : List ℕ×List ℕ) : Option (States r c U L) :=
  if v.1.length=q ∧ v.2.length=q then decodeProfile r c U L (profileOfCode small e v) else none

lemma decode_stateCode (x : States r c U L) :
    decodeStateCode r c U L e (stateCode r c U L e x)=some x := by
  unfold decodeStateCode stateCode
  rw [ite_eq_left (by simp only [profileCode,viewList,List.length_ofFn,and_self]),profileOfCode_code]
  exact (decodeProfile_eq_some_iff r c U L _ x).mpr rfl

lemma stateCode_injective : Function.Injective (stateCode r c U L e) := by
  intro x y h
  have he := congrArg (decodeStateCode r c U L e) h
  rw [decode_stateCode,decode_stateCode] at he
  exact Option.some.inj he

theorem decodeStateCode_eq_some_iff (v : List ℕ×List ℕ) (x : States r c U L) :
    decodeStateCode r c U L e v=some x ↔ stateCode r c U L e x=v := by
  constructor
  · intro h
    unfold decodeStateCode at h
    split_ifs at h with hlen
    have hx := (decodeProfile_eq_some_iff r c U L _ x).mp h
    exact (congrArg (profileCode small e) hx).trans (profileCode_ofCode small e v hlen.1 hlen.2)
  · rintro rfl
    exact decode_stateCode r c U L e x

def codeNeighborStates (x : States r c U L) : List (States r c U L) :=
  (codeNeighbors (stateCodeData r c U L e x)).filterMap (decodeStateCode r c U L e)

lemma codeNeighborStates_nodup (x : States r c U L) : (codeNeighborStates r c U L e x).Nodup := by
  apply List.Nodup.filterMap
  · intro a b y ha hb
    exact ((decodeStateCode_eq_some_iff r c U L e a y).mp ha).symm.trans
      ((decodeStateCode_eq_some_iff r c U L e b y).mp hb)
  · exact codeNeighbors_nodup _

theorem mem_codeNeighborStates (htotal : (∑ i,r i)=∑ j,c j) (x y : States r c U L) :
    y∈codeNeighborStates r c U L e x ↔ physicalAdjacent r c U L B (capacity_small r c U L) x y := by
  simp only [codeNeighborStates,List.mem_filterMap]
  constructor
  · rintro ⟨v,hv,hy⟩
    have he := (decodeStateCode_eq_some_iff r c U L e v y).mp hy
    rw [←he] at hv
    exact (mem_codeNeighbors r c U L htotal e x y).mp hv
  · intro h
    exact ⟨stateCode r c U L e y,(mem_codeNeighbors r c U L htotal e x y).mpr h,decode_stateCode r c U L e y⟩

lemma codeNeighborStates_length (x : States r c U L) :
    (codeNeighborStates r c U L e x).length≤6*d^2 := by
  have hq : q≤d := by
    calc
      q = Fintype.card (Cells small) := by simpa only [Fintype.card_fin] using Fintype.card_congr e
      _ ≤ Fintype.card (Fin m×Fin n) := Fintype.card_subtype_le _
      _ ≤ d := by simpa only [Fintype.card_prod] using (dimension_le_allowance (I := Fin m) (J := Fin n))
  have hc : (codeNeighbors (stateCodeData r c U L e x)).length≤6*q^2 :=
    codeNeighbors_length _ q (by simp [stateCodeData,codeCheckData,stateCode,profileCode,viewList])
      (by simp [stateCodeData,codeCheckData,stateCode,profileCode,viewList])
  exact (List.length_filterMap_le _ _).trans (hc.trans (by gcongr))

lemma codeNeighborStates_codes (x : States r c U L) :
    (codeNeighborStates r c U L e x).length≤2^s := by
  calc
    _ ≤ 6*d^2 := codeNeighborStates_length r c U L e x
    _ ≤ 32*d^2 := Nat.mul_le_mul_right _ (by decide)
    _ ≤ 2^s := Nat.le_pow_clog (by decide) _

lemma codeNeighbors_decode_total (htotal : (∑ i,r i)=∑ j,c j) (x : States r c U L) :
    ∀ v∈codeNeighbors (stateCodeData r c U L e x),∃ y,decodeStateCode r c U L e v=some y := by
  intro v hv
  have hp := (List.mem_filter.mp (List.mem_dedup.mp hv)).2
  obtain ⟨y,hy⟩ := (profileTest_code_iff r c U L htotal e v).mp hp
  exact ⟨y,(decodeStateCode_eq_some_iff r c U L e v y).mpr hy⟩

private lemma getElem_filterMap_total {A C : Type*} (f : A → Option C) (xs : List A)
    (h : ∀ a∈xs,∃ b,f a=some b) (i : ℕ) :
    (xs[i]?).bind f=(xs.filterMap f)[i]? := by
  induction xs generalizing i with
  | nil => simp
  | cons a xs ih =>
    obtain ⟨b,hb⟩ := h a (by simp)
    have ht : ∀ a∈xs,∃ b,f a=some b := fun a ha => h a (by simp [ha])
    cases i with
    | zero => simp [hb]
    | succ i => simpa only [List.getElem?_cons_succ,List.filterMap_cons,hb] using ih ht i

def decodedCodeProposal (x : States r c U L) (bits : Fin s → Bool) : Option (States r c U L) :=
  (codeNeighborProposal (stateCodeData r c U L e x,List.ofFn bits)).bind (decodeStateCode r c U L e)

lemma decodedCodeProposal_apply (x : States r c U L) (bits : Fin s → Bool) :
    decodedCodeProposal r c U L e x bits=
      (codeNeighborProposal (stateCodeData r c U L e x,List.ofFn bits)).bind (decodeStateCode r c U L e) := rfl

lemma decodedCodeProposal_eq (htotal : (∑ i,r i)=∑ j,c j) (x : States r c U L)
    (bits : Fin s → Bool) :
    decodedCodeProposal r c U L e x bits=listBitDraw (codeNeighborStates r c U L e x) s bits := by
  unfold decodedCodeProposal codeNeighborProposal
  rw [listWordChoice_ofFn]
  exact getElem_filterMap_total (decodeStateCode r c U L e) _
    (codeNeighbors_decode_total r c U L e htotal x) _

/-- The implemented binary neighbor choice has exactly the proposal
law used by the already-proved small-chain mixing estimate. -/
theorem decodedCodeProposal_law (htotal : (∑ i,r i)=∑ j,c j) (x : States r c U L) :
    mapLaw (uniformLaw (α := Fin s → Bool)) (decodedCodeProposal r c U L e x)=physicalProposalLaw r c U L x := by
  have he : decodedCodeProposal r c U L e x=listBitDraw (codeNeighborStates r c U L e x) s := by
    funext bits
    exact decodedCodeProposal_eq r c U L e htotal x bits
  rw [he]
  apply law_ext_except _ _ none
  intro y hy
  cases y with
  | none => exact False.elim (hy rfl)
  | some y =>
    rw [listBitDraw_mass_decidableEq (inferInstance : DecidableEq (Option (States r c U L)))
      _ (codeNeighborStates_nodup r c U L e x) s (codeNeighborStates_codes r c U L e x) y,
      physicalProposalLaw_mass_some]
    unfold unitMoveRat
    by_cases hxy : physicalAdjacent r c U L B (capacity_small r c U L) x y
    · have hy := (mem_codeNeighborStates r c U L e htotal x y).mpr hxy
      simp only [ite_eq_left hy,ite_eq_left hxy,proposalRat]
    · have hy := mt (mem_codeNeighborStates r c U L e htotal x y).mp hxy
      simp only [ite_eq_right hy,ite_eq_right hxy]

end CodeProposal

section Catalog
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U : ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "small" => firstPaperSmall r c U

def computedCatalog : List (ℕ×ℕ) := smallCellCatalog ((List.ofFn r,List.ofFn c),U)

lemma computedCatalog_nodup : (computedCatalog r c U).Nodup :=
  (cellPairs_nodup (List.ofFn r) (List.ofFn c)).filter _

lemma mem_computedCatalog (ij : ℕ×ℕ) :
    ij∈computedCatalog r c U ↔ ∃ a : Cells small,((a.val.1.val,a.val.2.val):ℕ×ℕ)=ij := by
  rw [computedCatalog,mem_smallCellCatalog]
  simp only [List.length_ofFn]
  constructor
  · rintro ⟨hi,hj,hsmall⟩
    let i : Fin m := ⟨ij.1,hi⟩
    let j : Fin n := ⟨ij.2,hj⟩
    have hs : small i j=true := by
      apply decide_eq_true
      simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi,hj,dite_true,
        Option.getD_some] using hsmall
    exact ⟨⟨(i,j),hs⟩,rfl⟩
  · rintro ⟨a,rfl⟩
    refine ⟨a.val.1.isLt,a.val.2.isLt,?_⟩
    have hs : r a.val.1<U ∨ c a.val.2<U := of_decide_eq_true a.property
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_ofFn,a.val.1.isLt,a.val.2.isLt,
      dite_true,Option.getD_some,Fin.eta] using hs

def catalogCell (i : Fin (computedCatalog r c U).length) : Cells small :=
  Classical.choose ((mem_computedCatalog r c U ((computedCatalog r c U)[i.val])).mp
    (List.getElem_mem i.isLt))

lemma catalogCell_coordinates (i : Fin (computedCatalog r c U).length) :
    ((catalogCell r c U i).val.1.val,(catalogCell r c U i).val.2.val)=
      (computedCatalog r c U)[i.val] :=
  Classical.choose_spec ((mem_computedCatalog r c U ((computedCatalog r c U)[i.val])).mp
    (List.getElem_mem i.isLt))

lemma catalogCell_bijective : Function.Bijective (catalogCell r c U) := by
  constructor
  · intro i j h
    have he := congrArg (fun a : Cells small => (a.val.1.val,a.val.2.val)) h
    rw [catalogCell_coordinates,catalogCell_coordinates] at he
    exact Fin.ext ((computedCatalog_nodup r c U).getElem_inj_iff.mp he)
  · intro a
    have hm : (a.val.1.val,a.val.2.val)∈computedCatalog r c U :=
      (mem_computedCatalog r c U _).mpr ⟨a,rfl⟩
    obtain ⟨i,hi,hval⟩ := List.mem_iff_getElem.mp hm
    refine ⟨⟨i,hi⟩,?_⟩
    have he := (catalogCell_coordinates r c U ⟨i,hi⟩).trans hval
    apply Subtype.ext
    exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

def computedCellEquiv : Fin (computedCatalog r c U).length ≃ Cells small :=
  Equiv.ofBijective (catalogCell r c U) (catalogCell_bijective r c U)

/-- The proof-level cell equivalence enumerates exactly the list made
by the polynomial catalog program, in the same order. -/
theorem computedCellEquiv_catalog :
    cellCatalog small (computedCellEquiv r c U)=computedCatalog r c U := by
  apply List.ext_getElem
  · simp only [cellCatalog,List.length_ofFn]
  · intro i hi hj
    simp only [cellCatalog,List.getElem_ofFn]
    exact catalogCell_coordinates r c U ⟨i,hj⟩

end Catalog

section ComputedProposal
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "s" => Nat.clog 2 (32*d^2)

/-- The actual list catalog fixes the coordinate order used by the program. -/
def computedStateCode (x : States r c U L) : List ℕ × List ℕ :=
  stateCode r c U L (computedCellEquiv r c U) x

def computedProposal (x : States r c U L) (bits : Fin s → Bool) : Option (States r c U L) :=
  decodedCodeProposal r c U L (computedCellEquiv r c U) x bits

/-- Pointwise semantics of the unchanged generic list proposal program. -/
theorem computedProposal_apply (x : States r c U L) (bits : Fin s → Bool) :
    computedProposal r c U L x bits =
      (codeNeighborProposal
        (codeCheckData (computedCatalog r c U) (List.ofFn r) (List.ofFn c) U
          (computedStateCode r c U L x), List.ofFn bits)).bind
        (decodeStateCode r c U L (computedCellEquiv r c U)) := by
  unfold computedProposal decodedCodeProposal stateCodeData
  rw [computedCellEquiv_catalog]
  rfl

/-- Exact law of the computed-order physical proposal at every free scale.
Equal totals discharge the Boolean feasibility test's conservation premise. -/
theorem computedProposal_law (htotal : (∑ i, r i) = ∑ j, c j) (x : States r c U L) :
    mapLaw (uniformLaw (α := Fin s → Bool)) (computedProposal r c U L x) =
      physicalProposalLaw r c U L x :=
  decodedCodeProposal_law r c U L (computedCellEquiv r c U) htotal x

end ComputedProposal

end

section Preparation
open OAI.MatchingFPRAS.TreeTyped

def cubeNat : Realizer (fun n : ℕ => n^3) :=
  (composition (pair squareNat identity) multiply).congr (by
    intro n
    simp only [Function.comp_apply, id_eq]
    ring)

lemma polynomial_cubeNat : PolynomialTime cubeNat :=
  polynomial_congr _ (polynomial_composition
    (polynomial_pair polynomial_squareNat polynomial_identity) polynomial_multiply)

/-- The new cutoff is computed from the encoded margin-list dimensions. -/
def idealMarginThreshold (z : List ℕ × List ℕ) : ℕ := 5 * (marginDimension z)^3

def idealMarginThresholdRealizer : Realizer idealMarginThreshold :=
  (composition (pair (constant 5)
    (composition marginDimensionRealizer cubeNat)) multiply).congr (by intro z; rfl)

theorem polynomial_idealMarginThreshold : PolynomialTime idealMarginThresholdRealizer :=
  polynomial_congr _ (polynomial_composition (polynomial_pair (polynomial_constant 5)
    (polynomial_composition polynomial_marginDimension polynomial_cubeNat)) polynomial_multiply)

def idealMarginCatalog (z : List ℕ × List ℕ) : List (ℕ × ℕ) :=
  smallCellCatalog (z, idealMarginThreshold z)

def idealMarginCatalogRealizer : Realizer idealMarginCatalog :=
  composition (pair identity idealMarginThresholdRealizer) smallCellCatalogRealizer

theorem polynomial_idealMarginCatalog : PolynomialTime idealMarginCatalogRealizer :=
  polynomial_composition (polynomial_pair polynomial_identity polynomial_idealMarginThreshold)
    polynomial_smallCellCatalog

def idealPrepareProfileInput (z : RawProfileInput) : ProfileCheckData :=
  (((idealMarginCatalog z.1, z.2), z.1), idealMarginThreshold z.1)

def idealPrepareProfileInputRealizer : Realizer idealPrepareProfileInput :=
  pair (pair (pair
    (composition (f := fun z : RawProfileInput => z.1) (g := idealMarginCatalog)
      first idealMarginCatalogRealizer) second) first)
    (composition (f := fun z : RawProfileInput => z.1) (g := idealMarginThreshold)
      first idealMarginThresholdRealizer)

theorem polynomial_idealPrepareProfileInput : PolynomialTime idealPrepareProfileInputRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair
    (polynomial_composition polynomial_first polynomial_idealMarginCatalog) polynomial_second)
    polynomial_first) (polynomial_composition polynomial_first polynomial_idealMarginThreshold)

def idealPreparedProposal (z : RawProfileInput × List Bool) : Option (List ℕ × List ℕ) :=
  codeNeighborProposal (idealPrepareProfileInput z.1, z.2)

def idealPreparedProposalRealizer : Realizer idealPreparedProposal :=
  composition (f := fun z : RawProfileInput × List Bool => (idealPrepareProfileInput z.1, z.2))
    (g := codeNeighborProposal)
    (pair (composition (f := fun z : RawProfileInput × List Bool => z.1)
      (g := idealPrepareProfileInput) first idealPrepareProfileInputRealizer) second)
    codeNeighborProposalRealizer

/-- A polynomial binary list program computes the new threshold, catalog,
complete neighbor list and word lookup. -/
theorem polynomial_idealPreparedProposal : PolynomialTime idealPreparedProposalRealizer :=
  polynomial_composition (polynomial_pair
    (polynomial_composition polynomial_first polynomial_idealPrepareProfileInput) polynomial_second)
    polynomial_codeNeighborProposal

end Preparation

noncomputable section
section Ideal
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => IdealOracleScales.cutoff (I := Fin m) (J := Fin n)
local notation "L" => IdealOracleScales.padding (I := Fin m) (J := Fin n)
local notation "s" => Nat.clog 2 (32*d^2)

lemma idealMarginThreshold_ofFn : idealMarginThreshold (List.ofFn r, List.ofFn c) = U := by
  simp only [idealMarginThreshold, marginDimension, List.length_ofFn,
    IdealOracleScales.cutoff, IdealOracleScales.idealU, dimensionAllowance, Fintype.card_fin]

lemma idealPrepareProfileInput_eq (x : States r c U L) :
    idealPrepareProfileInput ((List.ofFn r, List.ofFn c), computedStateCode r c U L x) =
      stateCodeData r c U L (computedCellEquiv r c U) x := by
  unfold idealPrepareProfileInput stateCodeData codeCheckData
  rw [computedCellEquiv_catalog]
  simp only [idealMarginCatalog, idealMarginThreshold_ofFn, computedCatalog, computedStateCode]

/-- Pointwise program identification uses exactly the computed catalogue order. -/
theorem idealPreparedProposal_eq (x : States r c U L) (bits : Fin s → Bool) :
    (idealPreparedProposal
      (((List.ofFn r, List.ofFn c), computedStateCode r c U L x), List.ofFn bits)).bind
      (decodeStateCode r c U L (computedCellEquiv r c U)) =
        computedProposal r c U L x bits := by
  have hi := idealPrepareProfileInput_eq r c x
  have hp := congrArg (fun z => codeNeighborProposal (z, List.ofFn bits)) hi
  have hb := congrArg (fun z => z.bind (decodeStateCode r c U L (computedCellEquiv r c U))) hp
  simpa only [idealPreparedProposal, computedProposal, decodedCodeProposal] using hb

theorem idealComputedProposal_law (htotal : (∑ i, r i) = ∑ j, c j) (x : States r c U L) :
    mapLaw (uniformLaw (α := Fin s → Bool)) (computedProposal r c U L x) =
      physicalProposalLaw r c U L x :=
  computedProposal_law r c U L htotal x

/-- The polynomial preparation program has the complete normalized proposal
law after interpreting its output code, including the unused-word hold mass. -/
theorem idealPreparedProposal_law (htotal : (∑ i, r i) = ∑ j, c j) (x : States r c U L) :
    mapLaw (uniformLaw (α := Fin s → Bool))
      (fun bits => (idealPreparedProposal
        (((List.ofFn r, List.ofFn c), computedStateCode r c U L x), List.ofFn bits)).bind
          (decodeStateCode r c U L (computedCellEquiv r c U))) =
      physicalProposalLaw r c U L x := by
  have he : (fun bits : Fin s → Bool => (idealPreparedProposal
        (((List.ofFn r, List.ofFn c), computedStateCode r c U L x), List.ofFn bits)).bind
          (decodeStateCode r c U L (computedCellEquiv r c U))) = computedProposal r c U L x := by
    funext bits
    exact idealPreparedProposal_eq r c x bits
  rw [he]
  exact idealComputedProposal_law r c htotal x

end Ideal
end
end Math115.PhysicalComputedProposal
