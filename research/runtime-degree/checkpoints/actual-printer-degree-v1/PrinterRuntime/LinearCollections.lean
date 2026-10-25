import ResearchBounds.TreeArithmeticDegree
import OAI.Combinatorics.MatchingCount.Machines.TreeFiniteCollections
import OAI.Combinatorics.MatchingCount.Complexity.TreeChoiceCosts

namespace Math115.PrinterRuntimeNext
open OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds
noncomputable section
variable {A B D : Type} [Codec A] [Codec B] [Codec D]

def AffineOutput (f : A → B) : Prop :=
  ∃ a b : ℕ, ∀ x, weight (f x) ≤ a * weight x + b

lemma typed_weaken {f : A → B} {F : Realizer f} {e t : ℕ}
    (hF : Typed F e) (het : e ≤ t) : Typed F t := by
  obtain ⟨p,hp,hpb⟩ := hF
  exact ⟨p,hp.trans het,hpb⟩

lemma typed_comp_pos {f : A → B} {g : B → D} {F : Realizer f} {G : Realizer g}
    {e t : ℕ} (hF : Typed F e) (hG : Typed G t) (ht : 1 ≤ t) :
    Typed (composition F G) (t*e) := by
  apply typed_weaken (typed_composition hF hG)
  exact max_le (by nlinarith) le_rfl

lemma typed_pair_same {f : A → B} {g : A → D} {F : Realizer f} {G : Realizer g}
    {e : ℕ} (hF : Typed F e) (hG : Typed G e) (he : 1 ≤ e) :
    Typed (pair F G) e := typed_weaken (typed_pair hF hG) (by omega)

lemma typed_comp_affine {f : A → B} {g : B → D} {F : Realizer f} {G : Realizer g}
    {e t : ℕ} (hF : Typed F e) (hG : Typed G t) (hf : AffineOutput f) :
    Typed (composition F G) (max e t) := by
  obtain ⟨a,b,hab⟩ := hf
  obtain ⟨p,hp,hpb⟩ := hF
  obtain ⟨q,hq,hqb⟩ := hG
  let R : Polynomial ℕ := C a*X+C b
  refine ⟨p+q.comp R,degree_add hp (by
    simpa only [Nat.mul_one] using degree_comp hq (degree_affine a b)),fun x => ?_⟩
  have h1 := hpb x
  have h2 := hqb (f x)
  have h3 := polynomial_eval_monotone q (hab x)
  simp only [eval_add,eval_comp,R,eval_add,eval_mul,eval_C,eval_X]
  change F.cost x+G.cost (f x)+weight (g (f x)) ≤ _
  dsimp only at h3
  omega

lemma affine_composition {f : A → B} {g : B → D}
    (hf : AffineOutput f) (hg : AffineOutput g) : AffineOutput (g ∘ f) := by
  obtain ⟨a,b,hf⟩ := hf
  obtain ⟨c,d,hg⟩ := hg
  refine ⟨c*a,c*b+d,fun x => ?_⟩
  have h1 := hg (f x)
  have h2 := Nat.mul_le_mul_left c (hf x)
  change weight (g (f x)) ≤ _
  nlinarith

lemma typed_choose {f : A → Bool} {g h : A → B}
    {F : Realizer f} {G : Realizer g} {H : Realizer h} {e : ℕ}
    (hF : Typed F e) (hG : Typed G e) (hH : Typed H e) (he : 1 ≤ e) :
    Typed (choose F G H) e := by
  obtain ⟨p,hp,hpb⟩ := hF
  obtain ⟨q,hq,hqb⟩ := hG
  obtain ⟨r,hr,hrb⟩ := hH
  refine ⟨p+q+r+7*X+18,?_,fun x => ?_⟩
  · have h1 := degree_add (degree_add (degree_add hp hq) hr)
      (degree_scale 7 (show (X : Polynomial ℕ).natDegree≤1 by simp))
    exact (degree_add h1 (show (18 : Polynomial ℕ).natDegree≤0 by simp)).trans (by omega)
  · have h1 := hpb x
    have h2 := hqb x
    have h3 := hrb x
    simp only [eval_add,eval_mul,eval_ofNat,eval_X]
    change F.cost x+(if f x then G.cost x else H.cost x)+7*weight x+18+
      weight (if f x then g x else h x) ≤ _
    cases f x <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

lemma typed_append : Typed (append (A:=A)) 2 := by
  have hrev : Typed (composition (first (A:=List A) (B:=List A))
      (TreeTyped.reverse (A:=A))) 2 := typed_comp_pos typed_first Math115.DegreeBounds.typed_reverse (by decide)
  have hprep : Typed (pair (composition (first (A:=List A) (B:=List A)) reverse) second) 2 :=
    typed_pair_same hrev (typed_weaken typed_second (by decide)) (by decide)
  have hout : AffineOutput (fun z : List A × List A => (z.1.reverse,z.2)) := by
    refine ⟨1,0,?_⟩
    rintro ⟨as,bs⟩
    simp only [one_mul,add_zero,weight_prod,weight_reverse]
    exact le_rfl
  have hfold : Typed (fold (listCons (A:=A))) 2 := by
    apply typed_fold (e:=1) (s:=1) Math115.DegreeBounds.typed_listCons_arithmetic (2*X+1)
      (by simpa using degree_affine 2 1) (by decide) (by decide)
    intro as bs pre post he
    have hp := weight_prefix he
    have ha := weight_append pre.reverse bs
    rw [weight_reverse] at ha
    simp only [List.foldl_flip_cons_eq_append']
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
    omega
  unfold append
  apply typed_congr
  exact typed_comp_affine hprep hfold hout

lemma affine_append : AffineOutput (fun z : List A × List A => z.1++z.2) := by
  refine ⟨1,0,?_⟩
  rintro ⟨as,bs⟩
  have h := weight_append as bs
  simp only [one_mul,add_zero,weight_prod]
  change weight (as++bs) ≤ 1+weight as+weight bs
  omega

lemma typed_flatten : Typed (flatten (A:=A)) 3 := by
  have hprep : Typed (pair (reverse (A:=List A)) (constant ([] : List A))) 2 :=
    typed_pair_same Math115.DegreeBounds.typed_reverse
      (typed_weaken (typed_constant ([] : List A)) (by decide)) (by decide)
  have hout : AffineOutput (fun as : List (List A) => (as.reverse,([] : List A))) := by
    refine ⟨1,2,fun as => ?_⟩
    simp only [one_mul]
    rw [weight_prod,weight_nil,weight_reverse]
    omega
  have hfold : Typed (fold (append (A:=A))) 3 := by
    apply typed_fold (e:=2) (s:=1) typed_append (2*X+1)
      (by simpa using degree_affine 2 1) (by decide) (by decide)
    intro as bs pre post he
    rw [fold_prepend]
    have h1 := weight_append pre.reverse.flatten bs
    have h2 := weight_flatten pre.reverse
    rw [weight_reverse] at h2
    have h3 := weight_prefix he
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
    omega
  unfold flatten
  apply typed_congr
  exact typed_comp_affine hprep hfold hout

lemma affine_flatten : AffineOutput (List.flatten (α:=A)) :=
  ⟨1,0,fun as => by simpa using weight_flatten as⟩

lemma map_affine_weight {f : A → B} (a b : ℕ)
    (hf : ∀ x,weight (f x) ≤ a*weight x+b) (as : List A) :
    weight (as.map f) ≤ (a+b+1)*weight as := by
  induction as with
  | nil => change 1 ≤ (a+b+1)*1; omega
  | cons x as ih =>
    have h := hf x
    simp only [List.map_cons,weight_cons]
    nlinarith

lemma affine_map {f : A → B} (hf : AffineOutput f) : AffineOutput (List.map f) := by
  obtain ⟨a,b,hab⟩ := hf
  exact ⟨a+b+1,0,fun as => by simpa using map_affine_weight a b hab as⟩

/-- Actual eager map with affine output grows its accumulator only linearly.
This charges every output construction and final reversal. -/
theorem typed_map_affine {f : A → B} {F : Realizer f} {e : ℕ}
    (hF : Typed F e) (he : 1 ≤ e) (hf : AffineOutput f) :
    Typed (TreeTyped.map F) (e+1) := by
  obtain ⟨a,b,hab⟩ := hf
  let S : Realizer (fun z : A × List B => f z.1::z.2) :=
    composition (pair (composition first F) second) listCons
  have hS : Typed S e := by
    dsimp only [S]
    simpa only [Nat.one_mul] using typed_comp_pos (typed_pair_same
      (by simpa using typed_comp_pos typed_first hF he)
      (typed_weaken typed_second he) he) Math115.DegreeBounds.typed_listCons_arithmetic (by decide)
  have hfoldRaw : Typed (fold S) (1+e*1) := by
    apply typed_fold (e:=e) (s:=1) hS (C (a+b+2)*X+1)
      (by simpa using degree_affine (a+b+2) 1) he (by decide)
    intro as bs pre post hsplit
    have hmap := map_affine_weight a b hab pre
    have hp := weight_prefix hsplit
    have hfold : pre.foldl (fun bs x => f x::bs) bs = (pre.map f).reverse++bs := by
      simp [List.foldl_flip_cons_eq_append]
    change weight (pre.foldl (fun bs x => f x::bs) bs) ≤ _
    rw [hfold]
    have ha := weight_append (pre.map f).reverse bs
    rw [weight_reverse] at ha
    simp only [eval_add,eval_mul,eval_C,eval_ofNat,eval_X,weight_prod]
    nlinarith [Nat.mul_le_mul_left (a+b+1) hp]
  have hfold : Typed (fold S) (e+1) := by simpa [Nat.add_comm] using hfoldRaw
  have hprep : Typed (pair (identity (A:=List A)) (constant ([] : List B))) 1 :=
    typed_pair_same typed_identity (typed_constant ([] : List B)) (by decide)
  have hprepout : AffineOutput (fun as : List A => (as,([] : List B))) := by
    refine ⟨1,2,fun as => ?_⟩
    simp only [one_mul]
    rw [weight_prod,weight_nil]
    omega
  have hbody : Typed (composition (pair (identity (A:=List A))
      (constant ([] : List B))) (fold S)) (e+1) := by
    simpa using typed_comp_affine hprep hfold hprepout
  have hbodyout : AffineOutput (fun as : List A => as.foldl (fun bs x => f x::bs) []) := by
    refine ⟨a+b+1,0,fun as => ?_⟩
    have hm := map_affine_weight a b hab as
    have heq : as.foldl (fun bs x => f x::bs) [] = (as.map f).reverse := by
      simp [List.foldl_flip_cons_eq_append]
    simpa only [heq,weight_reverse,add_zero] using hm
  unfold TreeTyped.map
  apply typed_congr
  exact typed_weaken
    (typed_comp_affine hbody Math115.DegreeBounds.typed_reverse hbodyout) (by omega)

lemma affine_flatMap {f : A → List B} (hf : AffineOutput f) :
    AffineOutput (List.flatMap f) := by
  have h := affine_composition (affine_map hf) (affine_flatten (A:=B))
  obtain ⟨a,b,hab⟩ := h
  exact ⟨a,b,fun as => by simpa only [Function.comp_apply,List.flatMap_def] using hab as⟩

/-- Actual map/flatten, including both full intermediate and final outputs. -/
theorem typed_flatMapPoly_affine {f : A → List B} {F : Realizer f} {e : ℕ}
    (hF : Typed F e) (he : 1 ≤ e) (hf : AffineOutput f) :
    Typed (flatMapPoly F) (max (e+1) 3) := by
  unfold flatMapPoly
  apply typed_congr
  exact typed_comp_affine (typed_map_affine hF he hf) typed_flatten (affine_map hf)

end
end Math115.PrinterRuntimeNext
