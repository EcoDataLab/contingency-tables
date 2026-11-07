import Research.PhysicalTraceMargins
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalOriginalResiduals
import OAI.Combinatorics.ContingencyTables.Sampling.SmallCoordinateSums

namespace Math115.PhysicalDefectTrace

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts SmallContextCoordinates SmallContextFibres
open SmallGraphProfiles FiniteExposureVariance CompletionTranslation RowMajorEnumeration
open IntegerWeightedTransport FactorialSignatures
open Math115.ReducedSmallChain

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

def IsBalanced (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x : States r c U L) : Prop :=
  Balanced (firstPaperSmall r c U) (capacity r c U L)
    (physicalProfile _ (capacity r c U L) r c L x)

abbrev BalancedVertices (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :=
  {x : States r c U L // IsBalanced r c U L x}

abbrev DefectVertices (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :=
  {x : States r c U L // ¬IsBalanced r c U L x}

def partitionEquiv (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :
    BalancedVertices r c U L ⊕ DefectVertices r c U L ≃ States r c U L :=
  Equiv.sumCompl (IsBalanced r c U L)

lemma defect_isSingleDefect (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (x : DefectVertices r c U L) :
    SingleDefect (firstPaperSmall r c U) (capacity r c U L)
      (physicalProfile _ (capacity r c U L) r c L x.val) := by
  exact x.val.val.property.resolve_left x.property

omit [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J] in
lemma balanced_cellSum (small : I → J → Bool) (B : I → J → ℕ) (z : SmallProfile small)
    (hb : Balanced small B z) (hbox : ∀ k, z k≤B k.1.val.1 k.1.val.2) (a : Cells small) :
    z (a,false)+z (a,true)=B a.val.1 a.val.2 := by
  have h := hb a.val.1 a.val.2
  have he : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small)=a := Subtype.ext (Prod.eta a.val)
  simp only [smallView,smallQ,a.property,dite_true,he] at h
  have hc := hbox (a,true)
  dsimp only at hc
  omega


lemma linearObservable_selected (small : I → J → Bool) (z : SmallProfile small)
    (p : Cells small×Bool → Prop) [DecidablePred p] :
    linearObservable (fun k => if p k then 1 else 0) z=
      ((∑ k,if p k then z k else 0:ℕ):ℤ) := by
  simp only [linearObservable,ite_mul,one_mul,zero_mul,Nat.cast_sum,Nat.cast_ite,Nat.cast_zero]

lemma linearObservable_cell (small : I → J → Bool) (z : SmallProfile small) (a : Cells small) :
    linearObservable (fun k => if k.1=a then 1 else 0) z=
      ((z (a,false)+z (a,true):ℕ):ℤ) := by
  simp [linearObservable,Fintype.sum_prod_type,Fintype.sum_bool,ite_mul,
    Finset.sum_add_distrib,Nat.cast_add,add_comm]

lemma balanced_exchange_cells (small : I → J → Bool) (B : I → J → ℕ)
    (D : SmallProfile small) (i j : Cells small×Bool) (hi : 0<D i) (hj : 0<D j)
    (hX : Balanced small B (removeOne D i)) (hY : Balanced small B (removeOne D j))
    (hbX : ∀ k,removeOne D i k≤B k.1.val.1 k.1.val.2)
    (hbY : ∀ k,removeOne D j k≤B k.1.val.1 k.1.val.2) : i.1=j.1 := by
  by_contra hne
  let a : Cells small×Bool → ℤ := fun k => if k.1=i.1 then 1 else 0
  have hx : linearObservable a (removeOne D i)=(B i.1.val.1 i.1.val.2:ℤ) := by
    rw [linearObservable_cell,balanced_cellSum small B _ hX hbX i.1]
  have hy : linearObservable a (removeOne D j)=(B i.1.val.1 i.1.val.2:ℤ) := by
    rw [linearObservable_cell,balanced_cellSum small B _ hY hbY i.1]
  rw [linearObservable_removeOne a D i hi] at hx
  rw [linearObservable_removeOne a D j hj] at hy
  have hai : a i=1 := by simp [a]
  have haj : a j=0 := by simp [a,Ne.symm hne]
  rw [hai] at hx
  rw [haj] at hy
  omega

/-- A unit exchange cannot join two actual positive balanced states: it must
move the two views of one cell, contradicting that cell's fixed small line. -/
theorem balanced_exchange_impossible (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (x y : States r c U L) (hxB : IsBalanced r c U L x) (hyB : IsBalanced r c U L y) :
    ¬IntegerExchangeAdjacent (physicalProfile _ (capacity r c U L) r c L x)
      (physicalProfile _ (capacity r c U L) r c L y) := by
  intro he
  obtain ⟨D,i,j,hij,hi,hj,hx,hy⟩ := he
  let small := firstPaperSmall r c U
  let B := capacity r c U L
  have hcell : i.1=j.1 := balanced_exchange_cells small B D i j hi hj
    (by rw [←hx];exact hxB) (by rw [←hy];exact hyB)
    (by rw [←hx];exact naturalProfile_bounded x.val.val)
    (by rw [←hy];exact naturalProfile_bounded y.val.val)
  have hview : i.2≠j.2 := by
    intro hv
    exact hij (Prod.ext hcell hv)
  have hsmall : r i.1.val.1<U ∨ c i.1.val.2<U := by
    have hs := i.1.property
    simpa only [small,firstPaperSmall,decide_eq_true_eq] using hs
  rcases hsmall with hrow|hcol
  · let a : Cells small×Bool → ℤ := fun k => if k.1.val.1=i.1.val.1 ∧ k.2=false then 1 else 0
    have hobs : linearObservable a (physicalProfile small B r c L y)=
        linearObservable a (physicalProfile small B r c L x) := by
      dsimp only [a]
      rw [linearObservable_selected,linearObservable_selected]
      change (selectedRow small (physicalProfile small B r c L y) false i.1.val.1:ℤ)=
        (selectedRow small (physicalProfile small B r c L x) false i.1.val.1:ℤ)
      rw [physical_smallRow_fixed r c U L y _ hrow,physical_smallRow_fixed r c U L x _ hrow]
    rw [hy,hx,linearObservable_removeOne a D j hj,linearObservable_removeOne a D i hi] at hobs
    have hai : a i=(if i.2=false then 1 else 0) := by simp [a]
    have haj : a j=(if j.2=false then 1 else 0) := by simp [a,←hcell]
    rw [hai,haj] at hobs
    have heq : i.2=j.2 := by cases hv : i.2 <;> cases hw : j.2 <;> simp_all <;> omega
    exact hview heq
  · let a : Cells small×Bool → ℤ := fun k => if k.1.val.2=i.1.val.2 ∧ k.2=true then 1 else 0
    have hobs : linearObservable a (physicalProfile small B r c L y)=
        linearObservable a (physicalProfile small B r c L x) := by
      dsimp only [a]
      rw [linearObservable_selected,linearObservable_selected]
      change (selectedColumn small (physicalProfile small B r c L y) true i.1.val.2:ℤ)=
        (selectedColumn small (physicalProfile small B r c L x) true i.1.val.2:ℤ)
      rw [physical_selectedColumn_equal r c U L y x _ hcol]
    rw [hy,hx,linearObservable_removeOne a D j hj,linearObservable_removeOne a D i hi] at hobs
    have hai : a i=(if i.2=true then 1 else 0) := by simp [a]
    have haj : a j=(if j.2=true then 1 else 0) := by simp [a,←hcell]
    rw [hai,haj] at hobs
    have heq : i.2=j.2 := by cases hv : i.2 <;> cases hw : j.2 <;> simp_all <;> omega
    exact hview heq

/-- Actual source graph has no balanced-to-balanced edges, including its
added designated repairs. No graph-decomposition hypothesis is supplied. -/
theorem physicalAdjacent_no_balanced_balanced (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (x y : States r c U L) (hxB : IsBalanced r c U L x) (hyB : IsBalanced r c U L y) :
    ¬physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x y := by
  intro hxy
  rcases Finset.mem_union.mp hxy with hex|hrp
  · exact balanced_exchange_impossible r c U L x y hxB hyB (Finset.mem_filter.mp hex).2
  · rcases Finset.mem_union.mp hrp with hfw|hbw
    · obtain ⟨z,_,hz⟩ := Finset.mem_image.mp hfw
      have he := congrArg Prod.fst hz
      dsimp only at he
      have hb := (congrArg (Balanced (firstPaperSmall r c U) (capacity r c U L)) he).mpr hxB
      exact balanced_not_defect _ _ _ hb z.property.1
    · obtain ⟨z,_,hz⟩ := Finset.mem_image.mp hbw
      have he := congrArg Prod.snd hz
      dsimp only at he
      have hb := (congrArg (Balanced (firstPaperSmall r c U) (capacity r c U L)) he).mpr hyB
      exact balanced_not_defect _ _ _ hb z.property.1

end
end Math115.PhysicalDefectTrace

#print axioms Math115.PhysicalDefectTrace.physicalAdjacent_no_balanced_balanced
