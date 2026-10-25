import Math115.ReducedSmallChain
import OAI.Combinatorics.ContingencyTables.Sampling.SmallPatternArithmetic

namespace Research.DefectCoordinateGeometry
open OAI.ContingencyTables
open scoped BigOperators Classical
open SmallContextCoordinates CompletionCounts SmallGraphProfiles IntegerWeightedTransport
open PhysicalCompletionFibres FactorialSignatures

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

/-- The exact unit-coordinate transfer restrictions imposed by the fixed
small row/column margins. Mixed-view transfers require both lines free. -/
def permitted (r : I → ℕ) (c : J → ℕ) (U : ℕ) :
    (Cells (firstPaperSmall r c U) × Bool) → (Cells (firstPaperSmall r c U) × Bool) → Prop
  | (s,false), (t,false) => (r s.val.1<U ∨ r t.val.1<U) → s.val.1=t.val.1
  | (s,true), (t,true) => (c s.val.2<U ∨ c t.val.2<U) → s.val.2=t.val.2
  | (s,false), (t,true) => U≤r s.val.1 ∧ U≤c t.val.2
  | (s,true), (t,false) => U≤c s.val.2 ∧ U≤r t.val.1

omit [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J] in
lemma permitted_symmetric (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (a b : Cells (firstPaperSmall r c U) × Bool) :
    permitted r c U a b ↔ permitted r c U b a := by
  rcases a with ⟨s,a⟩
  rcases b with ⟨t,b⟩
  cases a <;> cases b <;> simp [permitted, eq_comm, and_comm, or_comm]

omit [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J] in
/-- A small cell cannot supply both target views of one transfer anchor:
that would force its row and column both to be large. -/
lemma permitted_target_not_both (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (a : Cells (firstPaperSmall r c U) × Bool) (t : Cells (firstPaperSmall r c U)) :
    ¬ (permitted r c U a (t,false) ∧ permitted r c U a (t,true)) := by
  have ht : r t.val.1<U ∨ c t.val.2<U := by
    simpa only [firstPaperSmall, decide_eq_true_eq] using t.property
  rcases a with ⟨s,b⟩
  cases b
  · rintro ⟨hf,ht'⟩
    change ((r s.val.1<U ∨ r t.val.1<U) → s.val.1=t.val.1) at hf
    change U≤r s.val.1 ∧ U≤c t.val.2 at ht'
    rcases ht with hr | hc
    · have he := hf (Or.inr hr)
      rw [he] at ht'
      omega
    · omega
  · rintro ⟨hf,ht'⟩
    change U≤c s.val.2 ∧ U≤r t.val.1 at hf
    change ((c s.val.2<U ∨ c t.val.2<U) → s.val.2=t.val.2) at ht'
    rcases ht with hr | hc
    · omega
    · have he := ht' (Or.inr hc)
      rw [he] at hf
      omega

omit [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J] in
lemma permitted_target_bool_unique (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (a : Cells (firstPaperSmall r c U) × Bool) (t : Cells (firstPaperSmall r c U))
    (b d : Bool) (hb : permitted r c U a (t,b)) (hd : permitted r c U a (t,d)) : b=d := by
  cases b <;> cases d
  · rfl
  · exact False.elim (permitted_target_not_both r c U a t ⟨hb,hd⟩)
  · exact False.elim (permitted_target_not_both r c U a t ⟨hd,hb⟩)
  · rfl

omit [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J] in
lemma permitted_distinct_cells (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (a b : Cells (firstPaperSmall r c U) × Bool) (hne : a≠b)
    (hp : permitted r c U a b) : a.1≠b.1 := by
  rcases a with ⟨s,a⟩
  rcases b with ⟨t,b⟩
  intro he
  dsimp only at he
  subst t
  have hs : r s.val.1<U ∨ c s.val.2<U := by
    simpa only [firstPaperSmall, decide_eq_true_eq] using s.property
  cases a <;> cases b
  · exact hne rfl
  · change U≤r s.val.1 ∧ U≤c s.val.2 at hp
    omega
  · change U≤c s.val.2 ∧ U≤r s.val.1 at hp
    omega
  · exact hne rfl

noncomputable def permittedTargets (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (a : Cells (firstPaperSmall r c U) × Bool) :=
  Finset.univ.filter (fun b => b≠a ∧ permitted r c U a b)

/-- Injection into the other actual small cells, not a quadratic coordinate
allowance. Every anchor has at most p-1 permissible target coordinates. -/
theorem permittedTargets_card_le (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (a : Cells (firstPaperSmall r c U) × Bool) :
    (permittedTargets r c U a).card ≤ Fintype.card (Cells (firstPaperSmall r c U))-1 := by
  have hinj : Set.InjOn (fun b : Cells (firstPaperSmall r c U) × Bool => b.1)
      (permittedTargets r c U a) := by
    rintro ⟨s,b⟩ hb ⟨t,d⟩ hd he
    dsimp only at he
    subst t
    exact congrArg (fun e : Bool => (s,e))
      (permitted_target_bool_unique r c U a s b d
        (Finset.mem_filter.mp hb).2.2 (Finset.mem_filter.mp hd).2.2)
  have hsub : (permittedTargets r c U a).image Prod.fst ⊆ Finset.univ.erase a.1 := by
    intro t ht
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp ht
    apply Finset.mem_erase.mpr
    have hh := (Finset.mem_filter.mp hb).2
    exact ⟨(permitted_distinct_cells r c U b a hh.1
      ((permitted_symmetric r c U a b).mp hh.2)),Finset.mem_univ _⟩
  calc
    _ = ((permittedTargets r c U a).image Prod.fst).card := (Finset.card_image_iff.mpr hinj).symm
    _ ≤ (Finset.univ.erase a.1).card := Finset.card_le_card hsub
    _ = _ := by simp

section SelectedSums
variable {C : Type*} [Fintype C] [DecidableEq C]

/-- Equal fixed selected sums force the raised/lowered coordinates to agree
on membership in that selected line. -/
lemma remove_selected_sum_equiv (P : C → Prop) [DecidablePred P] (D : C → ℕ) (i j : C)
    (hi : 0<D i) (hj : 0<D j)
    (he : (∑ a,if P a then removeOne D i a else 0)=
      ∑ a,if P a then removeOne D j a else 0) : P i ↔ P j := by
  have hobs : linearObservable (fun a => if P a then 1 else 0) (removeOne D i)=
      linearObservable (fun a => if P a then 1 else 0) (removeOne D j) := by
    simpa only [linearObservable,ite_mul,one_mul,zero_mul,Nat.cast_sum,
      Nat.cast_ite,Nat.cast_zero] using congrArg (fun n : ℕ => (n:ℤ)) he
  rw [linearObservable_removeOne _ D i hi,linearObservable_removeOne _ D j hj] at hobs
  by_cases hPi : P i <;> by_cases hPj : P j <;> simp [hPi,hPj] at hobs ⊢
  all_goals omega

omit [Fintype C] in
lemma removeOne_eq_exchangeTarget (D : C → ℕ) (i j : C) (hij : i≠j) (hi : 0<D i) :
    removeOne D j=exchangeTarget (removeOne D i) i j := by
  funext a
  unfold exchangeTarget removeOne
  by_cases hai : a=i
  · subst a
    simp only [hij,ite_true,ite_false,Nat.sub_zero]
    omega
  · by_cases haj : a=j
    · subst a
      simp only [hai,ite_true,ite_false,Nat.sub_zero,Nat.add_zero]
    · simp only [hai,haj,ite_false,Nat.sub_zero,Nat.add_zero]

end SelectedSums

section CellSums
variable {C : Type*} [DecidableEq C]

noncomputable def cellMass (B : C → ℕ) (X : C×Bool → ℕ) (a : C) : ℤ :=
  (X (a,false):ℤ)+(X (a,true):ℤ)-B a

noncomputable def SignedPattern (B : C → ℕ) (X : C×Bool → ℕ) : Prop :=
  (∀ a,cellMass B X a=0) ∨
    ∃ s t,s≠t ∧ ∀ a,cellMass B X a=(if a=t then 1 else 0)-(if a=s then 1 else 0)

lemma removeOne_int_value (D : C×Bool → ℕ) (i : C×Bool) (hi : 0<D i) (k : C×Bool) :
    (removeOne D i k:ℤ)=(D k:ℤ)-(if k=i then 1 else 0) := by
  by_cases hk : k=i
  · subst k
    simp only [removeOne,ite_true]
    omega
  · simp only [removeOne,hk,ite_false,Nat.sub_zero,sub_zero]

lemma cellMass_remove_difference (B : C → ℕ) (D : C×Bool → ℕ)
    (i j : C×Bool) (hi : 0<D i) (hj : 0<D j) (a : C) :
    cellMass B (removeOne D j) a-cellMass B (removeOne D i) a=
      (if a=i.1 then 1 else 0)-(if a=j.1 then 1 else 0) := by
  unfold cellMass
  rw [removeOne_int_value D j hj,removeOne_int_value D j hj,
    removeOne_int_value D i hi,removeOne_int_value D i hi]
  rcases i with ⟨s,b⟩
  rcases j with ⟨t,d⟩
  cases b <;> cases d <;> simp only [Prod.mk.injEq, Bool.false_eq_true,
    Bool.true_eq_false, and_false, and_true, ↓reduceIte]
  all_goals ring

/-- A unit exchange between single-defect/balanced patterns must raise a
coordinate of the deficient cell or lower one of the excess cell. The
same-cell case is explicitly excluded by the actual margin geometry. -/
theorem pattern_exchange_anchors (B : C → ℕ) (D : C×Bool → ℕ)
    (i j : C×Bool) (hi : 0<D i) (hj : 0<D j) (hne : i.1≠j.1)
    (s t : C) (hst : s≠t)
    (hX : ∀ a,cellMass B (removeOne D i) a=(if a=t then 1 else 0)-(if a=s then 1 else 0))
    (hY : SignedPattern B (removeOne D j)) : i.1=s ∨ j.1=t := by
  by_contra hnone
  have his : i.1≠s := fun h => hnone (Or.inl h)
  have hjt : j.1≠t := fun h => hnone (Or.inr h)
  have hXs : cellMass B (removeOne D i) s = -1 := by simp [hX,hst]
  have hXt : cellMass B (removeOne D i) t = 1 := by simp [hX,hst.symm]
  have hdS := cellMass_remove_difference B D i j hi hj s
  have hdT := cellMass_remove_difference B D i j hi hj t
  have hYs : cellMass B (removeOne D j) s ≤ -1 := by
    rw [hXs] at hdS
    simp only [Ne.symm his,ite_false] at hdS
    split_ifs at hdS <;> omega
  have hYt : 1 ≤ cellMass B (removeOne D j) t := by
    rw [hXt] at hdT
    simp only [Ne.symm hjt,ite_false] at hdT
    split_ifs at hdT <;> omega
  rcases hY with hbal | ⟨s',t',hst',hdef⟩
  · have h := hbal s
    omega
  · have hs' : s=s' := by
      by_contra hne'
      have h := hdef s
      simp only [hne',ite_false] at h
      split_ifs at h <;> omega
    have ht' : t=t' := by
      by_contra hne'
      have h := hdef t
      simp only [hne',ite_false] at h
      split_ifs at h <;> omega
    subst s'
    subst t'
    have hsame : cellMass B (removeOne D j) i.1=cellMass B (removeOne D i) i.1 :=
      (hdef i.1).trans (hX i.1).symm
    have hdiff := cellMass_remove_difference B D i j hi hj i.1
    simp only [ite_true,hne,ite_false] at hdiff
    omega

end CellSums

noncomputable def raiseCandidates (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (X : SmallProfile (firstPaperSmall r c U)) (a : Cells (firstPaperSmall r c U) × Bool) :=
  (permittedTargets r c U a).image (fun b => exchangeTarget X a b)

noncomputable def lowerCandidates (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (X : SmallProfile (firstPaperSmall r c U)) (a : Cells (firstPaperSmall r c U) × Bool) :=
  (permittedTargets r c U a).image (fun b => exchangeTarget X b a)

noncomputable def defectCandidates (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (X : SmallProfile (firstPaperSmall r c U)) (s t : Cells (firstPaperSmall r c U)) :=
  raiseCandidates r c U X (s,false) ∪ raiseCandidates r c U X (s,true) ∪
    lowerCandidates r c U X (t,false) ∪ lowerCandidates r c U X (t,true)

lemma raiseCandidates_card_le (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (X : SmallProfile (firstPaperSmall r c U)) (a : Cells (firstPaperSmall r c U) × Bool) :
    (raiseCandidates r c U X a).card ≤ Fintype.card (Cells (firstPaperSmall r c U))-1 :=
  Finset.card_image_le.trans (permittedTargets_card_le r c U a)

lemma lowerCandidates_card_le (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (X : SmallProfile (firstPaperSmall r c U)) (a : Cells (firstPaperSmall r c U) × Bool) :
    (lowerCandidates r c U X a).card ≤ Fintype.card (Cells (firstPaperSmall r c U))-1 :=
  Finset.card_image_le.trans (permittedTargets_card_le r c U a)

theorem defectCandidates_card_le (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (X : SmallProfile (firstPaperSmall r c U)) (s t : Cells (firstPaperSmall r c U)) :
    (defectCandidates r c U X s t).card ≤ 4*(Fintype.card (Cells (firstPaperSmall r c U))-1) := by
  have hA := raiseCandidates_card_le r c U X (s,false)
  have hB := raiseCandidates_card_le r c U X (s,true)
  have hC := lowerCandidates_card_le r c U X (t,false)
  have hD := lowerCandidates_card_le r c U X (t,true)
  have hAB := Finset.card_union_le (raiseCandidates r c U X (s,false))
    (raiseCandidates r c U X (s,true))
  have hABC := Finset.card_union_le (raiseCandidates r c U X (s,false) ∪
    raiseCandidates r c U X (s,true)) (lowerCandidates r c U X (t,false))
  have hABCD := Finset.card_union_le (raiseCandidates r c U X (s,false) ∪
    raiseCandidates r c U X (s,true) ∪ lowerCandidates r c U X (t,false))
    (lowerCandidates r c U X (t,true))
  unfold defectCandidates
  omega

lemma exchangeTarget_mem_defectCandidates (r : I → ℕ) (c : J → ℕ) (U : ℕ)
    (X : SmallProfile (firstPaperSmall r c U)) (s t : Cells (firstPaperSmall r c U))
    (i j : Cells (firstPaperSmall r c U) × Bool) (hne : i≠j)
    (hp : permitted r c U i j) (ha : i.1=s ∨ j.1=t) :
    exchangeTarget X i j ∈ defectCandidates r c U X s t := by
  have hraise : exchangeTarget X i j ∈ raiseCandidates r c U X i := by
    exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hne.symm,hp⟩,rfl⟩
  have hlower : exchangeTarget X i j ∈ lowerCandidates r c U X j := by
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,hne,(permitted_symmetric r c U i j).mp hp⟩,rfl⟩
  simp only [defectCandidates, Finset.mem_union]
  rcases ha with hi | hj
  · rcases i with ⟨a,b⟩
    dsimp only at hi
    subst a
    cases b
    · exact Or.inl (Or.inl (Or.inl hraise))
    · exact Or.inl (Or.inl (Or.inr hraise))
  · rcases j with ⟨a,b⟩
    dsimp only at hj
    subst a
    cases b
    · exact Or.inl (Or.inr hlower)
    · exact Or.inr hlower

end
end Research.DefectCoordinateGeometry


