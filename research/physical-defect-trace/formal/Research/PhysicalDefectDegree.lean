import Research.DefectCoordinateGeometry
import Research.PhysicalTraceMargins

set_option maxHeartbeats 1000000

namespace Math115.PhysicalDefectDegree
open OAI.ContingencyTables
open scoped BigOperators Classical
open SmallContextCoordinates CompletionCounts SmallGraphProfiles IntegerWeightedTransport
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open SmallContextFibres FactorialSignatures SmallContextEnumeration RowMajorEnumeration
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace Research.DefectCoordinateGeometry

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

/-- Literal fixed selected-line sums imply the exact coordinate geometry. -/
lemma permitted_of_fixed_lines (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (D : SmallProfile (firstPaperSmall r c U))
    (i j : Cells (firstPaperSmall r c U) × Bool) (hi : 0<D i) (hj : 0<D j)
    (hrow : ∀ k,r k<U → selectedRow (firstPaperSmall r c U) (removeOne D i) false k=
      selectedRow (firstPaperSmall r c U) (removeOne D j) false k)
    (hcol : ∀ k,c k<U → selectedColumn (firstPaperSmall r c U) (removeOne D i) true k=
      selectedColumn (firstPaperSmall r c U) (removeOne D j) true k) : permitted r c U i j := by
  have hR (k : I) (hk : r k<U) :
      (i.1.val.1=k ∧ i.2=false) ↔ (j.1.val.1=k ∧ j.2=false) :=
    remove_selected_sum_equiv (fun a : Cells (firstPaperSmall r c U) × Bool => a.1.val.1=k ∧ a.2=false) D i j hi hj (by simpa only [selectedRow] using hrow k hk)
  have hC (k : J) (hk : c k<U) :
      (i.1.val.2=k ∧ i.2=true) ↔ (j.1.val.2=k ∧ j.2=true) :=
    remove_selected_sum_equiv (fun a : Cells (firstPaperSmall r c U) × Bool => a.1.val.2=k ∧ a.2=true) D i j hi hj (by simpa only [selectedColumn] using hcol k hk)
  rcases i with ⟨s,b⟩
  rcases j with ⟨t,d⟩
  cases b <;> cases d
  · intro hor
    rcases hor with hs | ht
    · exact ((hR s.val.1 hs).mp ⟨rfl,rfl⟩).1.symm
    · exact ((hR t.val.1 ht).mpr ⟨rfl,rfl⟩).1
  · refine ⟨?_,?_⟩
    · by_contra hn
      have hs : r s.val.1<U := by omega
      exact Bool.noConfusion ((hR s.val.1 hs).mp ⟨rfl,rfl⟩).2
    · by_contra hn
      have ht : c t.val.2<U := by omega
      exact Bool.noConfusion ((hC t.val.2 ht).mpr ⟨rfl,rfl⟩).2
  · refine ⟨?_,?_⟩
    · by_contra hn
      have hs : c s.val.2<U := by omega
      exact Bool.noConfusion ((hC s.val.2 hs).mp ⟨rfl,rfl⟩).2
    · by_contra hn
      have ht : r t.val.1<U := by omega
      exact Bool.noConfusion ((hR t.val.1 ht).mpr ⟨rfl,rfl⟩).2
  · intro hor
    rcases hor with hs | ht
    · exact ((hC s.val.2 hs).mp ⟨rfl,rfl⟩).1.symm
    · exact ((hC t.val.2 ht).mpr ⟨rfl,rfl⟩).1

/-- Actual positive physical states enforce those fixed selected-line sums. -/
lemma physical_exchange_permitted (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (x y : States r c U L) (D : SmallProfile (firstPaperSmall r c U))
    (i j : Cells (firstPaperSmall r c U) × Bool) (hi : 0<D i) (hj : 0<D j)
    (hX : physicalProfile _ (capacity r c U L) r c L x=removeOne D i)
    (hY : physicalProfile _ (capacity r c U L) r c L y=removeOne D j) : permitted r c U i j := by
  apply permitted_of_fixed_lines r c U D i j hi hj
  · intro k hk
    rw [←hX,←hY]
    exact (physical_smallRow_fixed r c U L x k hk).trans
      (physical_smallRow_fixed r c U L y k hk).symm
  · intro k hk
    rw [←hX,←hY]
    exact physical_selectedColumn_equal r c U L x y k hk

omit [Fintype I] [Fintype J] in
lemma cellMass_of_cellDefect (small : I → J → Bool) (B : I → J → ℕ)
    (X : SmallProfile small) (s t : Cells small) (hd : CellSumDefect small B X s t) :
    ∀ a,cellMass (fun a : Cells small => B a.val.1 a.val.2) X a=
      (if a=t then 1 else 0)-(if a=s then 1 else 0) := by
  intro a
  have haN := hd.2 a
  have ha := congrArg (fun n : ℕ => (n:ℤ)) haN
  push_cast at ha
  change (X (a,false):ℤ)+(X (a,true):ℤ)-(B a.val.1 a.val.2:ℤ)=
    (if a=t then 1 else 0)-(if a=s then 1 else 0)
  split_ifs at ha ⊢ <;> omega

omit [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J] in
lemma cellMass_of_cellBalanced (small : I → J → Bool) (B : I → J → ℕ)
    (X : SmallProfile small) (hb : CellSumBalanced small B X) :
    ∀ a,cellMass (fun a : Cells small => B a.val.1 a.val.2) X a=0 := by
  intro a
  have haN := hb a
  have ha := congrArg (fun n : ℕ => (n:ℤ)) haN
  push_cast at ha
  change (X (a,false):ℤ)+(X (a,true):ℤ)-(B a.val.1 a.val.2:ℤ)=0
  omega

/-- The signed pattern is derived from the source's bounded physical pattern. -/
lemma physical_signedPattern (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (y : States r c U L) :
    SignedPattern (fun a : Cells (firstPaperSmall r c U) => capacity r c U L a.val.1 a.val.2)
      (physicalProfile _ (capacity r c U L) r c L y) := by
  let small := firstPaperSmall r c U
  let B := capacity r c U L
  let Y := physicalProfile small B r c L y
  have hp : Pattern small B Y := y.val.property
  have h := (pattern_iff_cellSums small B Y
    (fun a => naturalProfile_bounded y.val.val (a,true))).mp hp
  rcases h with hbal | ⟨s,t,hd⟩
  · exact Or.inl (cellMass_of_cellBalanced small B Y hbal)
  · right
    exact ⟨s,t,hd.1,cellMass_of_cellDefect small B Y s t hd⟩

/-- Every actual positive physical unit neighbor of this defect belongs to
one of the four explicitly bounded coordinate-anchor candidate sets. -/
lemma physical_exchange_mem_defectCandidates (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (x y : States r c U L) (s t : Cells (firstPaperSmall r c U))
    (hdef : CellSumDefect (firstPaperSmall r c U) (capacity r c U L)
      (physicalProfile _ (capacity r c U L) r c L x) s t)
    (hxy : IntegerExchangeAdjacent (physicalProfile _ (capacity r c U L) r c L x)
      (physicalProfile _ (capacity r c U L) r c L y)) :
    physicalProfile _ (capacity r c U L) r c L y ∈ defectCandidates r c U
      (physicalProfile _ (capacity r c U L) r c L x) s t := by
  obtain ⟨D,i,j,hij,hi,hj,hX,hY⟩ := hxy
  have hp := physical_exchange_permitted r c U L x y D i j hi hj hX hY
  have hsigX := cellMass_of_cellDefect _ (capacity r c U L) _ s t hdef
  have hsigY := physical_signedPattern r c U L y
  have ha := pattern_exchange_anchors
    (fun a : Cells (firstPaperSmall r c U) => capacity r c U L a.val.1 a.val.2)
    D i j hi hj (permitted_distinct_cells r c U i j hij hp) s t hdef.1
    (by intro a; rw [←hX]; exact hsigX a) (by rw [←hY]; exact hsigY)
  have htarg : physicalProfile _ (capacity r c U L) r c L y=
      exchangeTarget (physicalProfile _ (capacity r c U L) r c L x) i j := by
    rw [hX,hY]
    exact removeOne_eq_exchangeTarget D i j hij hi
  rw [htarg]
  exact exchangeTarget_mem_defectCandidates r c U _ s t i j hij hp ha

/-- Actual full physical degree at a defect is at most 4p-3. The four anchor
sets are derived from actual margin and pattern constraints. Reverse repairs
have balanced targets, and at most one designated forward repair is added. -/
theorem physical_defect_degree_le (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (x : States r c U L)
    (hx : SingleDefect (firstPaperSmall r c U) (capacity r c U L)
      (physicalProfile _ (capacity r c U L) r c L x)) :
    (Finset.univ.filter (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x)).card ≤
      4*Fintype.card (Cells (firstPaperSmall r c U))-3 := by
  let small := firstPaperSmall r c U
  let B := capacity r c U L
  let p := physicalProfile small B r c L
  obtain ⟨s,t,hs,ht,hd⟩ := hx
  let sC : Cells small := ⟨s,hs⟩
  let tC : Cells small := ⟨t,ht⟩
  have hcell : CellSumDefect small B (p x) sC tC :=
    (defect_iff_cellSums small B (p x) (fun a => naturalProfile_bounded x.val.val (a,true)) sC tC).mp hd
  have hsingle : SingleDefect small B (p x) := ⟨s,t,hs,ht,hd⟩
  let src := fun z : PositiveDefects small B r c L => naturalProfile z.val
  let tgt := fun z : PositiveDefects small B r c L => rawChoice small U
    (wordChoices small U (repairWord r c U L B (capacity_small r c U L) z))
  let R := (Finset.univ.filter (fun z => src z=p x)).image tgt
  have hsrc : Function.Injective src := by
    intro a b he
    apply Subtype.ext
    exact naturalProfile_injective small B he
  have hR : R.card ≤ 1 := by
    have hsmall : (Finset.univ.filter (fun z => src z=p x)).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      exact hsrc ((Finset.mem_filter.mp ha).2.trans (Finset.mem_filter.mp hb).2.symm)
    exact Finset.card_image_le.trans hsmall
  have hsub : (Finset.univ.filter
      (physicalAdjacent r c U L B (capacity_small r c U L) x)).image p ⊆
      defectCandidates r c U (p x) sC tC ∪ R := by
    intro v hv
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hv
    have he := (Finset.mem_filter.mp hy).2
    change (p x,p y) ∈ physicalEdges small B ∪ repairEdges r c U L B (capacity_small r c U L) at he
    rcases Finset.mem_union.mp he with hunit | hrepair
    · exact Finset.mem_union_left R (physical_exchange_mem_defectCandidates r c U L x y sC tC hcell
        (Finset.mem_filter.mp hunit).2)
    · unfold repairEdges at hrepair
      rcases Finset.mem_union.mp hrepair with hf | hr
      · obtain ⟨z,hz,heq⟩ := Finset.mem_image.mp hf
        have hsx : src z=p x := congrArg Prod.fst heq
        have hty : tgt z=p y := congrArg Prod.snd heq
        exact Finset.mem_union_right _ (Finset.mem_image.mpr
          ⟨z,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hsx⟩,hty⟩)
      · obtain ⟨z,hz,heq⟩ := Finset.mem_image.mp hr
        have htx : tgt z=p x := congrArg Prod.fst heq
        have hbal : Balanced small B (tgt z) := rawChoice_balanced small B U
          (capacity_small r c U L) (wordChoices small U (repairWord r c U L B (capacity_small r c U L) z))
        rw [htx] at hbal
        exact False.elim (balanced_not_defect small B (p x) hbal hsingle)
  have hpcard : 1 ≤ Fintype.card (Cells small) := Fintype.card_pos_iff.mpr ⟨sC⟩
  calc
    _ = ((Finset.univ.filter (physicalAdjacent r c U L B (capacity_small r c U L) x)).image p).card :=
      (Finset.card_image_of_injective _ (physicalProfile_injective small B r c L)).symm
    _ ≤ (defectCandidates r c U (p x) sC tC ∪ R).card := Finset.card_le_card hsub
    _ ≤ (defectCandidates r c U (p x) sC tC).card+R.card := Finset.card_union_le _ _
    _ ≤ 4*(Fintype.card (Cells small)-1)+1 :=
      Nat.add_le_add (defectCandidates_card_le r c U (p x) sC tC) hR
    _ = _ := by dsimp only [small] at hpcard ⊢; omega

/-- Nonbalanced actual physical states are defects by their source Pattern;
this is the form required by the balanced/defect trace partition. -/
theorem physical_nonbalanced_degree_le (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (x : States r c U L)
    (hx : ¬ Balanced (firstPaperSmall r c U) (capacity r c U L)
      (physicalProfile _ (capacity r c U L) r c L x)) :
    (Finset.univ.filter (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x)).card ≤
      4*Fintype.card (Cells (firstPaperSmall r c U))-3 := by
  have hp := x.val.property
  rcases hp with hb | hd
  · exact False.elim (hx hb)
  · exact physical_defect_degree_le r c U L x hd

end
end Math115.PhysicalDefectDegree

