/- Private checkpoint12 source candidate. Repair v2: original native v3 failure preserved; this repair has no compiler receipt yet.
   Quantifies the exact imported control/list/first-success realizers. -/
import ResearchBounds.TreeDegreeBounds
import OAI.Combinatorics.ContingencyTables.Machines.FirstSuccessProgram

namespace Math115.DrawDegree
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds

variable {A B C D : Type} [Codec A] [Codec B] [Codec C] [Codec D]

lemma typed_weaken {f : A → B} {F : Realizer f} {e t : ℕ}
    (hF : Typed F e) (het : e ≤ t) : Typed F t := by
  obtain ⟨p,hp,hpb⟩ := hF
  exact ⟨p,hp.trans het,hpb⟩

lemma typed_composition_pos {f : A → B} {g : B → C}
    {F : Realizer f} {G : Realizer g} {e t : ℕ}
    (hF : Typed F e) (hG : Typed G t) (ht : 1 ≤ t) :
    Typed (composition F G) (t*e) := by
  apply typed_weaken (typed_composition hF hG)
  exact max_le (by nlinarith) le_rfl

lemma typed_pair_same {f : A → B} {g : A → C}
    {F : Realizer f} {G : Realizer g} {e : ℕ}
    (hF : Typed F e) (hG : Typed G e) (he : 1 ≤ e) : Typed (pair F G) e := by
  exact typed_weaken (typed_pair hF hG) (by omega)

lemma typed_recode {f : C → D} {F : Realizer f} (i : A → C) (g : A → B)
    (hi : ∀ a,encode (i a)=encode a) (ho : ∀ a,encode (f (i a))=encode (g a))
    {e : ℕ} (hF : Typed F e) : Typed (F.recode i g hi ho) e := by
  obtain ⟨p,hp,hpb⟩ := hF
  refine ⟨p,hp,fun a=>?_⟩
  have h := hpb (i a)
  change F.cost (i a)+weight (g a)≤_
  simpa only [weight,hi,ho] using h

lemma typed_choose {f : A → Bool} {g h : A → B}
    {F : Realizer f} {G : Realizer g} {H : Realizer h} {e t u : ℕ}
    (hF : Typed F e) (hG : Typed G t) (hH : Typed H u) :
    Typed (choose F G H) (max (max (max e t) u) 1) := by
  obtain ⟨p,hp,hpb⟩ := hF
  obtain ⟨q,hq,hqb⟩ := hG
  obtain ⟨r,hr,hrb⟩ := hH
  refine ⟨p+q+r+7*X+18,?_,fun a=>?_⟩
  · have h1 := degree_add (degree_add (degree_add hp hq) hr)
      (degree_scale 7 (show (X : Polynomial ℕ).natDegree≤1 by simp))
    simpa using degree_add h1 (show (18 : Polynomial ℕ).natDegree≤0 by simp)
  · have h1 := hpb a
    have h2 := hqb a
    have h3 := hrb a
    simp only [eval_add,eval_mul,eval_ofNat,eval_X]
    change F.cost a+(if f a then G.cost a else H.cost a)+7*weight a+18+
      weight (if f a then g a else h a)≤_
    cases f a <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

lemma typed_choose_same {f : A → Bool} {g h : A → B}
    {F : Realizer f} {G : Realizer g} {H : Realizer h} {e : ℕ}
    (hF : Typed F e) (hG : Typed G e) (hH : Typed H e) (he : 1 ≤ e) :
    Typed (choose F G H) e :=
  typed_weaken (typed_choose hF hG hH) (by omega)

lemma typed_listCons : Typed (listCons (A:=A)) 1 := by
  refine ⟨X+1,by simpa using degree_affine 1 1,fun ⟨a,as⟩=>?_⟩
  simp only [eval_add,eval_X,eval_one,weight_prod,weight_cons]
  change 1+(1+weight a+weight as)≤(1+weight a+weight as)+1
  omega

lemma typed_reverse : Typed (OAI.MatchingFPRAS.TreeTyped.reverse (A:=A)) 2 := by
  unfold OAI.MatchingFPRAS.TreeTyped.reverse
  apply typed_congr
  apply typed_weaken (typed_composition_pos
    (typed_pair_same typed_identity (typed_constant ([] : List A)) (by decide))
    (typed_fold (e:=1) (s:=1) typed_listCons (2*X+1) (by simpa using degree_affine 2 1)
      (by decide) (by decide) ?_) (by decide)) (by decide)
  intro as bs pre post he
  have hp := weight_prefix he
  have h := weight_append pre.reverse bs
  rw [weight_reverse] at h
  simp only [List.foldl_flip_cons_eq_append']
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  omega

lemma typed_listCase (b : B) {g : A×List A → B} {G : Realizer g} {e : ℕ}
    (hG : Typed G e) : Typed (listCase b G) (max e 1) := by
  obtain ⟨p,hp,hpb⟩ := hG
  obtain ⟨q,hq,hqb⟩ := typed_constant (A:=List A) b
  refine ⟨p+q+3,?_,fun as=>?_⟩
  · simpa using degree_add (degree_add hp hq) (show (3 : Polynomial ℕ).natDegree≤0 by simp)
  · simp only [eval_add,eval_ofNat]
    cases as with
    | nil =>
      have hh := hqb []
      change (constant b (A:=List A)).cost []+weight b≤_ at hh
      change 3+(constant b (A:=List A)).cost []+weight b≤_
      omega
    | cons a as =>
      have hh := hpb (a,as)
      have he : weight (a,as)=weight (a::as) := rfl
      rw [he] at hh
      change 3+G.cost (a,as)+weight (g (a,as))≤_
      omega

lemma typed_head (d : A) : Typed (head d) 1 := by
  unfold head
  apply typed_congr
  exact typed_weaken (typed_listCase d typed_first) (by decide)

lemma typed_optionCases [Inhabited B] {f : A→C} {g : A×B→C}
    {F : Realizer f} {G : Realizer g} {e : ℕ}
    (hF : Typed F e) (hG : Typed G e) (he : 1≤e) :
    Typed (optionCases F G) e := by
  unfold optionCases
  apply typed_recode
  dsimp only [Realizer.fst,Realizer.snd]
  apply typed_choose_same (e:=e)
  · exact typed_weaken (typed_composition_pos typed_second typed_first (by decide)) he
  · have harg : Typed (pair (first (A:=A) (B:=Bool×B)) (composition second second)) 1 :=
      typed_pair_same typed_first
        (typed_composition_pos typed_second typed_second (by decide)) (by decide)
    simpa only [Nat.mul_one] using typed_composition_pos harg hG he
  · simpa only [Nat.mul_one] using typed_composition_pos typed_first hF he
  · exact he

lemma typed_mapStep {f : A×B→C} {F : Realizer f} {e : ℕ}
    (hF : Typed F e) (he : 1≤e) : Typed (mapStepRealizer F) e := by
  unfold mapStepRealizer
  have harg : Typed (pair (composition (second (A:=B) (B:=A×List C)) first) first) 1 :=
    typed_pair_same (typed_composition_pos typed_second typed_first (by decide)) typed_first (by decide)
  have hval : Typed (composition (pair (composition (second (A:=B) (B:=A×List C)) first) first) F) e := by
    simpa only [Nat.mul_one] using typed_composition_pos harg hF he
  have hpair : Typed (pair
      (composition (pair (composition (second (A:=B) (B:=A×List C)) first) first) F)
      (composition second second)) e :=
    typed_pair_same hval
      (typed_weaken (typed_composition_pos typed_second typed_second (by decide)) he) he
  have hcons : Typed (composition (pair
      (composition (pair (composition (second (A:=B) (B:=A×List C)) first) first) F)
      (composition second second)) listCons) e := by
    simpa only [Nat.one_mul] using typed_composition_pos hpair typed_listCons (by decide)
  exact typed_pair_same
    (typed_weaken (typed_composition_pos typed_second typed_first (by decide)) he) hcons he

/-- Exact mapWith: all outputs are constructed before any later first-success selection.
    The bound deliberately retains the polynomial growth of the accumulator. -/
lemma typed_mapWith {f : A×B→C} {F : Realizer f} {e : ℕ}
    (hF : Typed F e) (he : 1≤e) :
    Typed (mapWith F) (2*(1+e*(e+1))) := by
  obtain ⟨p,hp,hpb⟩ := hF
  let P : Polynomial ℕ := 2*X+X*(p.comp (1+2*X)+1)+2
  have hP : P.natDegree ≤ e+1 := by
    have ha : (1+2*X : Polynomial ℕ).natDegree≤1 := by
      simpa [add_comm] using degree_affine 2 1
    have hc : (p.comp (1+2*X)+1).natDegree≤e :=
      natDegree_add_le_of_degree_le (by simpa using degree_comp hp ha) (by simp)
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · exact (degree_scale 2 (show (X : Polynomial ℕ).natDegree≤1 by simp)).trans (by omega)
      · simpa [Nat.add_comm] using degree_mul (show (X : Polynomial ℕ).natDegree≤1 by simp) hc
    · simp
  have hfold : Typed (fold (mapStepRealizer F)) (1+e*(e+1)) := by
    apply typed_fold (e:=e) (s:=e+1) (typed_mapStep ⟨p,hp,hpb⟩ he) P hP he (by omega)
    rintro bs ⟨a,cs⟩ pre post hsplit
    let S := weight (bs,(a,cs))
    have hb : weight bs≤S := by dsimp [S]; simp only [weight_prod]; omega
    have ha : weight a≤S := by dsimp [S]; simp only [weight_prod]; omega
    have hc : weight cs≤S := by dsimp [S]; simp only [weight_prod]; omega
    have hl : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix hsplit).trans hb)
    have hm := weight_map_bound (f:=fun b=>f (a,b)) (as:=pre) (N:=p.eval (1+2*S)) (by
      intro b hmem
      have hbs := weight_mem hmem
      have hpre := weight_prefix hsplit
      have hh := hpb (a,b)
      have ht := polynomial_eval_monotone p (show weight (a,b)≤1+2*S by rw [weight_prod]; omega)
      dsimp only at ht
      omega)
    rw [mapStep_fold,weight_prod]
    have happ := weight_append (pre.map fun b=>f (a,b)).reverse cs
    rw [weight_reverse] at happ
    simp only [P,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,eval_comp]
    change _≤2*S+S*(p.eval (1+2*S)+1)+2
    nlinarith [Nat.mul_le_mul_right (p.eval (1+2*S)+1) hl]
  unfold mapWith
  apply typed_congr
  have hinit : Typed (pair (second (A:=A) (B:=List B)) (pair first (constant ([] : List C)))) 1 :=
    typed_pair_same typed_second
      (typed_pair_same typed_first (typed_constant ([] : List C)) (by decide)) (by decide)
  have hbody : Typed (composition (pair (second (A:=A) (B:=List B)) (pair first (constant ([] : List C))))
      (fold (mapStepRealizer F))) (1+e*(e+1)) := by
    simpa only [Nat.mul_one] using typed_composition_pos hinit hfold (by omega)
  exact typed_composition_pos hbody
    (typed_composition_pos typed_second typed_reverse (by decide)) (by decide)

lemma typed_filter {f : A→Bool} {F : Realizer f} {e : ℕ}
    (hF : Typed F e) (he : 1≤e) : Typed (filter F) (2*(e+1)) := by
  have hpred : Typed (composition (first (A:=A) (B:=List A)) F) e := by
    simpa only [Nat.mul_one] using typed_composition_pos typed_first hF he
  have hstep : Typed (choose (composition (first (A:=A) (B:=List A)) F) listCons second) e :=
    typed_choose_same hpred (typed_weaken typed_listCons he) (typed_weaken typed_second he) he
  have hfold : Typed (fold (choose (composition (first (A:=A) (B:=List A)) F) listCons second)) (1+e*1) := by
    apply typed_fold (e:=e) (s:=1) hstep (2*X+1)
      (by simpa using degree_affine 2 1) he (by decide)
    intro as bs pre post hsplit
    change weight (pre.foldl (fun bs a=>if f a then a::bs else bs) bs)≤_
    rw [filter_fold]
    have happ := weight_append (pre.filter f).reverse bs
    rw [weight_reverse] at happ
    have hf := weight_sublist (List.filter_sublist (p:=f) (l:=pre))
    have hp := weight_prefix hsplit
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
    omega
  unfold filter
  apply typed_congr
  have hinit : Typed (pair (identity (A:=List A)) (constant ([] : List A))) 1 :=
    typed_pair_same typed_identity (typed_constant ([] : List A)) (by decide)
  have hbody : Typed (composition (pair (identity (A:=List A)) (constant ([] : List A)))
      (fold (choose (composition (first (A:=A) (B:=List A)) F) listCons second))) (1+e*1) := by
    simpa only [Nat.mul_one] using typed_composition_pos hinit hfold (by omega)
  simpa only [Nat.mul_one,Nat.add_comm] using typed_composition_pos hbody typed_reverse (by decide)

lemma typed_map {f : A→B} {F : Realizer f} {e : ℕ}
    (hF : Typed F e) (he : 1≤e) : Typed (OAI.MatchingFPRAS.TreeTyped.map F) (2*(1+e*(e+1))) := by
  obtain ⟨p,hp,hpb⟩ := hF
  let P : Polynomial ℕ := X+X*(p+1)+1
  have hP : P.natDegree≤e+1 := by
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · exact (show (X : Polynomial ℕ).natDegree≤1 by simp).trans (by omega)
      · have hplus : (p+1).natDegree≤e := natDegree_add_le_of_degree_le hp (by simp)
        simpa [Nat.add_comm] using degree_mul (show (X : Polynomial ℕ).natDegree≤1 by simp) hplus
    · simp
  have hval : Typed (composition (first (A:=A) (B:=List B)) F) e := by
    simpa only [Nat.mul_one] using typed_composition_pos typed_first ⟨p,hp,hpb⟩ he
  have harg : Typed (pair (composition (first (A:=A) (B:=List B)) F) second) e :=
    typed_pair_same hval (typed_weaken typed_second he) he
  have hstep : Typed (composition (pair (composition (first (A:=A) (B:=List B)) F) second) listCons) e := by
    simpa only [Nat.one_mul] using typed_composition_pos harg typed_listCons (by decide)
  have hfold : Typed (fold (composition (pair (composition (first (A:=A) (B:=List B)) F) second) listCons)) (1+e*(e+1)) := by
    apply typed_fold (e:=e) (s:=e+1) hstep P hP he (by omega)
    intro as bs pre post hsplit
    let S := weight (as,bs)
    have ha : weight as≤S := by dsimp [S]; rw [weight_prod]; omega
    have hb : weight bs≤S := by dsimp [S]; rw [weight_prod]; omega
    have hl : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix hsplit).trans ha)
    have hm := weight_map_bound (f:=f) (as:=pre) (N:=p.eval S) (by
      intro a hmem
      have hh := hpb a
      have ht := polynomial_eval_monotone p ((weight_mem hmem).trans ((weight_prefix hsplit).trans ha))
      dsimp only at ht
      omega)
    have hfold : pre.foldl (fun bs a=>f a::bs) bs=(pre.map f).reverse++bs := by
      simp [List.foldl_flip_cons_eq_append]
    change weight (pre.foldl (fun bs a=>f a::bs) bs)≤_
    rw [hfold]
    have happ := weight_append (pre.map f).reverse bs
    rw [weight_reverse] at happ
    simp only [P,eval_add,eval_mul,eval_X,eval_one]
    change _≤S+S*(p.eval S+1)+1
    nlinarith [Nat.mul_le_mul_right (p.eval S+1) hl]
  unfold OAI.MatchingFPRAS.TreeTyped.map
  apply typed_congr
  have hinit : Typed (pair (identity (A:=List A)) (constant ([] : List B))) 1 :=
    typed_pair_same typed_identity (typed_constant ([] : List B)) (by decide)
  have hbody : Typed (composition (pair (identity (A:=List A)) (constant ([] : List B)))
      (fold (composition (pair (composition (first (A:=A) (B:=List B)) F) second) listCons))) (1+e*(e+1)) := by
    simpa only [Nat.mul_one] using typed_composition_pos hinit hfold (by omega)
  exact typed_composition_pos hbody typed_reverse (by decide)

lemma typed_filterWith {f : A×B→Bool} {F : Realizer f} {e : ℕ}
    (hF : Typed F e) (he : 1≤e) :
    Typed (filterWith F) (48*(1+e*(e+1))) := by
  unfold filterWith
  apply typed_congr
  apply typed_weaken (typed_composition_pos
    (typed_composition_pos
      (typed_mapWith (typed_pair_same (typed_weaken typed_second he) hF he) he)
      (typed_filter typed_second (by decide)) (by decide))
    (typed_map typed_first (by decide)) (by decide)) (by ring_nf; simp)

lemma typed_isSome [Inhabited A] : Typed (FirstSuccessProgram.isSomeRealizer (B:=A)) 1 := by
  unfold FirstSuccessProgram.isSomeRealizer
  apply typed_congr
  exact typed_weaken (typed_composition_pos
    (typed_pair_same (typed_constant false) typed_identity (by decide))
    (typed_optionCases (typed_constant false) (typed_constant true) (by decide)) (by decide)) (by decide)

lemma typed_firstSome [Inhabited A] : Typed (FirstSuccessProgram.firstSomeRealizer (B:=A)) 4 := by
  unfold FirstSuccessProgram.firstSomeRealizer
  apply typed_congr
  exact typed_weaken (typed_composition_pos (typed_filter typed_isSome (by decide))
    (typed_head none) (by decide)) (by decide)

lemma typed_default [Inhabited A] : Typed (FirstSuccessProgram.defaultRealizer (B:=A)) 1 := by
  unfold FirstSuccessProgram.defaultRealizer
  apply typed_recode
  exact typed_optionCases typed_identity typed_second (by decide)

/-- Actual supplied-list retry, including evaluation of every trial, firstSome
    filtering, default selection and copies of the original fallback. -/
lemma typed_firstSuccessRetry [Inhabited B] {f : A×C→Option B} {F : Realizer f} {e : ℕ}
    (hF : Typed F e) (he : 1≤e) :
    Typed (FirstSuccessProgram.retryRealizer F) (8*(1+e*(e+1))) := by
  let M := 2*(1+e*(e+1))
  have hinputs : Typed (pair (composition (first (A:=A×B) (B:=List C)) first) second) 1 :=
    typed_pair_same (typed_composition_pos typed_first typed_first (by decide)) typed_second (by decide)
  have hresults : Typed (composition (pair (composition (first (A:=A×B) (B:=List C)) first) second) (mapWith F)) M := by
    simpa only [Nat.mul_one] using typed_composition_pos hinputs (typed_mapWith hF he) (by omega)
  have hselected : Typed (composition
      (composition (pair (composition (first (A:=A×B) (B:=List C)) first) second) (mapWith F))
      FirstSuccessProgram.firstSomeRealizer) (4*M) :=
    typed_composition_pos hresults typed_firstSome (by decide)
  have hpair : Typed (pair (composition first second) (composition
      (composition (pair (composition (first (A:=A×B) (B:=List C)) first) second) (mapWith F))
      FirstSuccessProgram.firstSomeRealizer)) (4*M) :=
    typed_pair_same
      (typed_weaken (typed_composition_pos typed_first typed_second (by decide)) (by dsimp [M]; omega))
      hselected (by dsimp [M]; omega)
  have hfinal := typed_composition_pos hpair typed_default (by decide)
  -- Reuse the identical polynomial witness pointwise. This avoids transporting
  -- Typed's hidden function index from the explicit composite to retry f.
  obtain ⟨p,hp,hpb⟩ := hfinal
  refine ⟨p,(by simpa only [Nat.one_mul, M, ←Nat.mul_assoc, show 4*2=8 by decide] using hp),?_⟩
  intro z
  change (composition
      (pair (composition first second)
        (composition (composition (pair (composition first first) second) (mapWith F))
          FirstSuccessProgram.firstSomeRealizer))
      FirstSuccessProgram.defaultRealizer).cost z+
    weight ((FirstSuccessProgram.firstSome (z.2.map (fun w => f (z.1.1,w)))).getD z.1.2) ≤
      p.eval (weight z)
  exact hpb z

end Math115.DrawDegree
