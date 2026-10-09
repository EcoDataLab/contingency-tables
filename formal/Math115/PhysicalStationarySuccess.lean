/-
SPDX-License-Identifier: Apache-2.0
The literal successful physical state/completion pairs at free scales.
-/
import Math115.PhysicalStationaryMass
import OAI.Combinatorics.ContingencyTables.Transport.BalancedJointConstruction
import OAI.Combinatorics.ContingencyTables.Transport.CompletionFibreTransport

set_option maxHeartbeats 1200000

namespace Math115.PhysicalStationarySuccess

noncomputable section

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open ReducedSmallChain PhysicalStateNonempty PhysicalStationaryMass
open SmallGraphProfiles SmallContextCoordinates SmallContextFibres PhysicalCompletionFibres
open FirstPaperProfiles FirstPaperPhysicalMarginal PaddedCompletions CompletionCounts
open SmallContextEnumeration RowMajorEnumeration FiniteExposureVariance

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

omit [LinearOrder I] [LinearOrder J] in
lemma paddedTable_small_rows (small : I → J → Bool) (L : ℕ)
    {r : I → ℕ} {c : J → ℕ} (X : Table r c) (i : I) :
    smallRow small (paddedTable small L X).val i ≤ r i := by
  calc
    _ = ∑ j,if small i j then X.val i j else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      cases hs : small i j <;> simp [paddedTable,hs]
    _ ≤ ∑ j,X.val i j := Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
    _ = _ := X.property.1 i

omit [LinearOrder I] [LinearOrder J] in
lemma paddedTable_small_columns (small : I → J → Bool) (L : ℕ)
    {r : I → ℕ} {c : J → ℕ} (X : Table r c) (j : J) :
    smallColumnView small (paddedTable small L X).val j ≤ c j := by
  calc
    _ = ∑ i,if small i j then X.val i j else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      cases hs : small i j <;> simp [paddedTable,hs]
    _ ≤ ∑ i,X.val i j := Finset.sum_le_sum (fun i _ => by split_ifs <;> omega)
    _ = _ := X.property.2 j

noncomputable def originalJoint (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (X : Table r c) :
    BalancedJoint (firstPaperSmall r c U) (capacity r c U L) r c
      L U := by
  let d := dimensionAllowance (I := I) (J := J)
  let small := firstPaperSmall r c U
  let Y := paddedTable small (L) X
  have hR := paddedTable_small_rows small (L) X
  have hC := paddedTable_small_columns small (L) X
  refine jointOfTable small (capacity r c U L) r c (L) (U)
    (capacity_small r c U L) Y ?_ hR hC ?_
  · intro i j hs
    change X.val i j+(if small i j then 0 else L) ≤ U
    simpa only [hs,ite_true,Nat.add_zero] using small_entry_le r c (U) X i j hs
  · intro i j _
    exact paper_residual_capacity r c d (L) (U) dimension_le_allowance ⟨Y,hR,hC⟩ i j

lemma originalJoint_projection (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (X : Table r c) :
    balancedJointTable (firstPaperSmall r c U) (capacity r c U L) r c
      L U
      (capacity_small r c U L) (originalJoint r c U L X)=
        paddedTable (firstPaperSmall r c U) L X := by
  apply Subtype.ext
  rfl
lemma large_padding_rows (small : I → J → Bool) (r : I → ℕ) (L : ℕ) :
    paddedRows r (largePadding (Finset.univ.filter (fun p : I×J => small p.1 p.2=false)) L)=
      (fun i => r i+rowLargeCount small i*L) := by
  funext i
  unfold paddedRows rowLargeCount
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  cases hs : small i j <;> simp [largePadding,hs]

lemma large_padding_columns (small : I → J → Bool) (c : J → ℕ) (L : ℕ) :
    paddedColumns c (largePadding (Finset.univ.filter (fun p : I×J => small p.1 p.2=false)) L)=
      (fun j => c j+columnLargeCount small j*L) := by
  funext j
  unfold paddedColumns columnLargeCount
  rw [Finset.sum_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  cases hs : small i j <;> simp [largePadding,hs]


noncomputable def large (r : I → ℕ) (c : J → ℕ) (U : ℕ) : Finset (I × J) :=
  Finset.univ.filter (fun p => firstPaperSmall r c U p.1 p.2 = false)

abbrev Joint (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :=
  BalancedJoint (firstPaperSmall r c U) (capacity r c U L) r c
    L U

noncomputable def jointTable (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (a : Joint r c U L) :=
  balancedJointTable (firstPaperSmall r c U) (capacity r c U L) r c
    L U
    (capacity_small r c U L) a

abbrev SuccessfulJoint (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :=
  {a : Joint r c U L // ∀ i j,firstPaperSmall r c U i j=false →
    L ≤ (jointTable r c U L a).val i j}

noncomputable def originalSuccessfulJoint (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (X : Table r c) :
    SuccessfulJoint r c U L := by
  refine ⟨originalJoint r c U L X,?_⟩
  intro i j hs
  unfold jointTable
  rw [originalJoint_projection]
  simp only [paddedTable,hs,Bool.false_eq_true,ite_false]
  omega

noncomputable def unpadSuccessfulJoint (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (a : SuccessfulJoint r c U L) : Table r c := by
  let P := largePadding (large r c U) L
  let Y := jointTable r c U L a.val
  have hm : HasMargins Y.val (paddedRows r P) (paddedColumns c P) := by
    dsimp only [P,large]
    rw [large_padding_rows,large_padding_columns]
    exact Y.property
  exact unpadTable P ⟨Y.val,hm⟩ (by
    intro i j
    cases hs : firstPaperSmall r c U i j with
    | false => simpa only [P,large,largePadding,Finset.mem_filter,Finset.mem_univ,
        true_and,hs,ite_true] using a.property i j hs
    | true => simp [P,large,largePadding,hs])

lemma unpadSuccessfulJoint_val (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (a : SuccessfulJoint r c U L) (i : I) (j : J) :
    (unpadSuccessfulJoint r c U L a).val i j=(jointTable r c U L a.val).val i j-
      largePadding (large r c U) L i j := rfl

/-- Each success produces exactly one original table, and every original
table has exactly one successful state/completion preimage. -/
noncomputable def successfulJointEquiv (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :
    Table r c ≃ SuccessfulJoint r c U L where
  toFun := originalSuccessfulJoint r c U L
  invFun := unpadSuccessfulJoint r c U L
  left_inv X := by
    apply Subtype.ext
    funext i j
    rw [unpadSuccessfulJoint_val]
    change (jointTable r c U L (originalJoint r c U L X)).val i j-_=X.val i j
    unfold jointTable
    rw [originalJoint_projection]
    cases hs : firstPaperSmall r c U i j <;> simp [paddedTable,large,largePadding,hs]
  right_inv a := by
    apply Subtype.ext
    apply balancedJointTable_injective (firstPaperSmall r c U) (capacity r c U L) r c
      L U
      (capacity_small r c U L)
    change jointTable r c U L (originalJoint r c U L (unpadSuccessfulJoint r c U L a))=jointTable r c U L a.val
    unfold jointTable at ⊢
    rw [originalJoint_projection]
    apply Subtype.ext
    funext i j
    change (unpadSuccessfulJoint r c U L a).val i j+
      (if firstPaperSmall r c U i j then 0 else L)=_
    rw [unpadSuccessfulJoint_val]
    cases hs : firstPaperSmall r c U i j with
    | false =>
      have ha := a.property i j hs
      simpa only [large,largePadding,Finset.mem_filter,Finset.mem_univ,true_and,
        hs,ite_true,Bool.false_eq_true,ite_false,jointTable] using Nat.sub_add_cancel ha
    | true => simp [large,largePadding,hs,jointTable]
abbrev Fibre (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (z : States r c U L) :=
  CompletionFibre (firstPaperSmall r c U) (capacity r c U L) r
    (fun i => r i + rowLargeCount (firstPaperSmall r c U) i * L) c
    (fun j => c j + columnLargeCount (firstPaperSmall r c U) j * L)
    (physicalProfile _ (capacity r c U L) r c L z)

abbrev StateJoint (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :=
  (z : States r c U L) × Fibre r c U L z

section Event
variable (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
local notation "small" => firstPaperSmall r c U
local notation "B" => capacity r c U L

/-- Forget the redundant small-profile coordinate while retaining both
full margin views. This projection is injective on all actual joint pairs. -/
def stateJointProjection (a : StateJoint r c U L) := a.2.val

lemma stateJointProjection_injective : Function.Injective (stateJointProjection r c U L) :=
  fibre_projection_injective small B r _ c _ (physicalProfile small B r c (L))
    (physicalProfile_injective small B r c (L))
    (fun z => naturalProfile_bounded z.val.val)

def jointState (a : Joint r c U L) : States r c U L := by
  have hp : 0 < hardMarginal small B r c (L)
      (rawChoice small (U) (wordChoices small (U) a.1)) := by
    rw [hardMarginal_eq_fibre_card small B r c (L) _
      (rawChoice_bounded small B (U) (capacity_small r c U L) _)]
    exact_mod_cast Fintype.card_pos_iff.mpr (⟨a.2⟩ : Nonempty _)
  exact ⟨encodeProfile small B r c (L) (U) (capacity_small r c U L) (.inl a.1),hp⟩

def jointEmbedding (a : Joint r c U L) : StateJoint r c U L :=
  ⟨jointState r c U L a,a.2⟩

lemma jointEmbedding_injective : Function.Injective (jointEmbedding r c U L) := by
  intro a b hab
  apply balancedJointTable_injective small B r c (L) (U) (capacity_small r c U L)
  apply Subtype.ext
  exact congrArg (fun z : StateJoint r c U L => z.2.val.val.1) hab

lemma jointEmbedding_balanced (a : Joint r c U L) :
    Balanced small B (physicalProfile small B r c (L) (jointEmbedding r c U L a).1) :=
  rawChoice_balanced small B (U) (capacity_small r c U L) _

def balancedJointFromState (a : StateJoint r c U L)
    (hb : Balanced small B (physicalProfile small B r c (L) a.1)) : Joint r c U L :=
  ⟨balancedWord small B (U) (capacity_small r c U L) a.1.val.val,
    withProfile (balancedWord_profile small B (U) (capacity_small r c U L) a.1.val.val hb).symm a.2⟩

lemma balancedJointFromState_projection (a : StateJoint r c U L)
    (hb : Balanced small B (physicalProfile small B r c (L) a.1)) :
    (balancedJointFromState r c U L a hb).2.val=a.2.val := by
  exact withProfile_val
    (balancedWord_profile small B (U) (capacity_small r c U L) a.1.val.val hb).symm a.2

lemma embedding_fromState (a : StateJoint r c U L)
    (hb : Balanced small B (physicalProfile small B r c (L) a.1)) :
    jointEmbedding r c U L (balancedJointFromState r c U L a hb)=a := by
  apply stateJointProjection_injective r c U L
  exact balancedJointFromState_projection r c U L a hb

lemma fromState_embedding (a : Joint r c U L) :
    balancedJointFromState r c U L (jointEmbedding r c U L a) (jointEmbedding_balanced r c U L a)=a := by
  apply jointEmbedding_injective r c U L
  exact embedding_fromState r c U L _ _

/-- The success test reads precisely balance and the lower padding bound. -/
def StateJointSuccess (a : StateJoint r c U L) : Prop :=
  Balanced small B (physicalProfile small B r c (L) a.1) ∧
    ∀ i j,small i j=false → L ≤ a.2.val.val.1 i j

abbrev SuccessfulStateJoint := {a : StateJoint r c U L // StateJointSuccess r c U L a}

def successStateEquiv : SuccessfulJoint r c U L ≃ SuccessfulStateJoint r c U L where
  toFun a := ⟨jointEmbedding r c U L a.val,jointEmbedding_balanced r c U L a.val,a.property⟩
  invFun a := ⟨balancedJointFromState r c U L a.val a.property.1,a.property.2⟩
  left_inv a := by
    apply Subtype.ext
    exact fromState_embedding r c U L a.val
  right_inv a := by
    apply Subtype.ext
    exact embedding_fromState r c U L a.val a.property.1

/-- Every accepted actual state/completion pair unpads to one original
table, and every original table has one such pair. -/
def originalStateSuccessEquiv : Table r c ≃ SuccessfulStateJoint r c U L :=
  (successfulJointEquiv r c U L).trans (successStateEquiv r c U L)

end Event

end

end Math115.PhysicalStationarySuccess
