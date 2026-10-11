/- Private degree bounds for the actual pinned numeric fresh-word program.
   Degree six is an upper bound on charged work plus worst encoded output.
   The numeric measure includes n, not merely the binary length of n. -/
import ResearchBounds.TreeDegreeBounds
import OAI.Combinatorics.MatchingCount.Complexity.OnlineWordCost

namespace Math115.DegreeBounds
open OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped
open OAI.MatchingFPRAS.PhysicalStream Polynomial

def OnlineBounded {A B : Type} [Codec A] [Codec B] {f : A→Experiment B}
    (F : OnlineTree.Realizer f) (measure : A→ℕ) (E : ℕ) : Prop :=
  ∃ p : Polynomial ℕ, p.natDegree≤E ∧
    ∀ a,F.cost a+(f a).worst weight≤p.eval (measure a)

variable {A B D : Type} [Codec A] [Codec B] [Codec D]

lemma online_deterministic {f : A→B} {F : TreeTyped.Realizer f} {m : A→ℕ} {e : ℕ}
    (hF : Bounded F m e) : OnlineBounded (OnlineTree.deterministic F) m e := hF
lemma online_congr {f g : A→Experiment B} {F : OnlineTree.Realizer f} {m : A→ℕ} {e : ℕ}
    (h : ∀ a w,(f a).mean w=(g a).mean w) (hF : OnlineBounded F m e) :
    OnlineBounded (F.congr h) m e := by
  obtain ⟨p,hp,hpb⟩ := hF
  refine ⟨p,hp,fun a=>?_⟩
  change F.cost a+(g a).worst weight≤_
  rw [←Experiment.worst_eq_of_mean_eq (h a)]
  exact hpb a
lemma online_composition {f : A→Experiment B} {g : B→Experiment D}
    {F : OnlineTree.Realizer f} {G : OnlineTree.Realizer g} {m : A→ℕ} {n : B→ℕ}
    {e t u : ℕ} (hF : OnlineBounded F m e) (hG : OnlineBounded G n t)
    (p : Polynomial ℕ) (hp : p.natDegree≤u)
    (hm : ∀ a,(f a).All (fun b=>n b≤p.eval (m a))) :
    OnlineBounded (OnlineTree.composition F G) m (max e (t*u)) := by
  obtain ⟨q,hq,hqb⟩ := hF
  obtain ⟨r,hr,hrb⟩ := hG
  refine ⟨q+2*(r.comp p),degree_add hq (degree_scale 2 (degree_comp hr hp)),fun a=>?_⟩
  have hb : (f a).All (fun b=>G.cost b+(g b).worst weight≤r.eval (p.eval (m a))) :=
    (hm a).mono (fun b hb=>(hrb b).trans (polynomial_eval_monotone r hb))
  have h1 := Experiment.worst_le _ _ _ (hb.mono (fun b hb=>Nat.le_trans (Nat.le_add_right _ _) hb))
  have h2 := Experiment.worst_le _ _ _ (hb.mono (fun b hb=>Nat.le_trans (Nat.le_add_left _ _) hb))
  have h3 := hqb a
  change F.cost a+(f a).worst G.cost+((f a).bind g).worst weight≤_
  rw [Experiment.worst_bind]
  simp only [eval_add,eval_mul,eval_ofNat,eval_comp]
  omega
lemma online_then {f : A→Experiment B} {g : B→Experiment D}
    {F : OnlineTree.Realizer f} {G : OnlineTree.Realizer g} {m : A→ℕ} {e t : ℕ}
    (hF : OnlineBounded F m e) (hG : OnlineBounded G weight t) :
    OnlineBounded (OnlineTree.composition F G) m (max e (t*e)) := by
  obtain ⟨p,hp,hpb⟩ := hF
  apply online_composition ⟨p,hp,hpb⟩ hG p hp
  intro a
  exact (Experiment.all_worst (f a) weight).mono
    (fun b hb=>hb.trans (Nat.le_trans (Nat.le_add_left _ _) (hpb a)))
lemma online_pair {f : A→Experiment B} {g : A→Experiment D}
    {F : OnlineTree.Realizer f} {G : OnlineTree.Realizer g} {m : A→ℕ} {e t u : ℕ}
    (hF : OnlineBounded F m e) (hG : OnlineBounded G m t)
    (p : Polynomial ℕ) (hp : p.natDegree≤u) (hw : ∀ a,weight a≤p.eval (m a)) :
    OnlineBounded (OnlineTree.pair F G) m (max (max e t) u) := by
  obtain ⟨q,hq,hqb⟩ := hF
  obtain ⟨r,hr,hrb⟩ := hG
  refine ⟨27*q+r+45*p+138, ?_,fun a=>?_⟩
  · have h1 := degree_add (degree_scale 27 hq) hr
    have h2 := degree_add h1 (degree_scale 45 hp)
    simpa using degree_add h2 (show (138 : Polynomial ℕ).natDegree≤0 by simp)
  · change (OnlineTree.pair F G).cost a+
      ((f a).bind (fun b=>(g a).map (Prod.mk b))).worst weight≤_
    rw [OnlineTree.pair_cost,OnlineTree.pair_weight]
    have h1 := hqb a
    have h2 := hrb a
    have h3 := hw a
    simp only [eval_add,eval_mul,eval_ofNat]
    omega

lemma typed_listCons : Typed (TreeTyped.listCons (A:=A)) 1 := by
  refine ⟨X+1,by simpa using degree_affine 1 1,fun ⟨a,as⟩=>?_⟩
  simp only [eval_add,eval_X,eval_one,weight_prod,weight_cons]
  change 1+(1+weight a+weight as)≤(1+weight a+weight as)+1
  omega
lemma typed_subtract : Typed TreeTyped.subtract 1 := by
  refine ⟨50*X+100,by simpa using degree_affine 50 100,fun ⟨a,b⟩=>?_⟩
  have ha:=size_le_weight a
  have hb:=size_le_weight b
  have hc:=weight_nat_small (Nat.sub_le a b)
  have ho:=weight_bool (decide (a<b))
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  change (2*weight a+3*(a.bits.length+b.bits.length)+31)+
    (if decide (a<b) then weight (a,b)+2 else
      2*weight a+9*(a.bits.length+b.bits.length)+4*weight (a-b)+32)+
      7*weight (a,b)+18+weight (a-b)≤_
  rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len,weight_prod]
  split <;> omega
lemma typed_predecessor : Typed TreeTyped.predecessor 1 := by
  exact typed_composition (typed_pair typed_identity (typed_constant 1)) typed_subtract
lemma typed_rangeStep : Typed TreeTyped.rangeStepRealizer 1 := by
  exact typed_composition
    (typed_pair (typed_composition typed_first typed_predecessor) typed_second) typed_listCons

/- This reproduces the actual boundedRepeat witness in range_numeric_work:
   range includes n iterations and intermediate states of quadratic weight. -/
lemma range_numeric_degree : Bounded TreeTyped.range id 3 := by
  unfold TreeTyped.range
  apply bounded_congr
  obtain ⟨r,hr,hrb⟩ := bounded_remeasure
    (typed_pair (typed_identity (A:=ℕ)) (typed_constant ([] : List ℕ)))
    (4*X+1) (show (4*X+1 : Polynomial ℕ).natDegree≤1 by simpa using degree_affine 4 1)
    (fun n=>by simpa using weight_nat_numeric n)
  obtain ⟨t,ht,htb⟩ := typed_pair (typed_composition typed_first typed_predecessor) typed_rangeStep
  let q : Polynomial ℕ := 4*X^2+2*X+1
  have hq : q.natDegree≤2 := by
    have h1 := degree_scale 4 (show (X^2 : Polynomial ℕ).natDegree≤2 by simp)
    have h2 := degree_scale 2 (show (X : Polynomial ℕ).natDegree≤1 by simp)
    simpa [q] using degree_add (degree_add h1 h2) (show (1 : Polynomial ℕ).natDegree≤0 by simp)
  let P : Polynomial ℕ := r+X*(t.comp (2+4*X+q)+4*(4*X+1)+12)+10+q
  have hP : P.natDegree≤3 := by
    have hc : (2+4*X+q : Polynomial ℕ).natDegree≤2 := by
      exact natDegree_add_le_of_degree_le
        (show (2+4*X : Polynomial ℕ).natDegree≤2 from
          (by simpa [add_comm] using (degree_affine 4 2).trans (by omega))) hq
    have hd := degree_comp ht hc
    have he := degree_scale 4 (show (4*X+1 : Polynomial ℕ).natDegree≤1 by simpa using degree_affine 4 1)
    have hf := degree_add (degree_add hd he) (show (12 : Polynomial ℕ).natDegree≤0 by simp)
    have hg := degree_mul (show (X : Polynomial ℕ).natDegree≤1 by simp) hf
    have hh := degree_add (degree_add (degree_add hr hg) (show (10 : Polynomial ℕ).natDegree≤0 by simp)) hq
    simpa [P] using hh
  refine ⟨P,hP,fun n=>?_⟩
  let init : ℕ×List ℕ := (n,[])
  let I : ℕ→List ℕ→Prop := fun k zs=>zs.length+k=n ∧ ∀ z∈zs,z<n
  have hstate : ∀ k zs,I k zs→weight zs≤q.eval n := by
    intro k zs hz
    have hh:=weight_map_bound (as:=zs) (f:=id) (N:=4*n+1) (by
      intro z h
      exact (weight_nat_numeric z).trans (by have :=hz.2 z h; omega))
    simp only [List.map_id] at hh
    have hlen : zs.length≤n := by have :=hz.1; omega
    have hm:=Nat.mul_le_mul_right (4*n+2) hlen
    simp only [q,eval_add,eval_mul,eval_ofNat,eval_X,eval_pow,eval_one]
    nlinarith
  have hstep : ∀ k<n,∀ zs,I (k+1) zs→I k (TreeTyped.rangeStep (k+1,zs)) := by
    intro k hk zs hz
    change ((k+1-1)::zs).length+k=n ∧ ∀ z∈((k+1-1)::zs),z<n
    simp only [Nat.add_sub_cancel,List.length_cons,List.mem_cons]
    constructor
    · have :=hz.1; omega
    · intro z h; rcases h with rfl | h
      · exact hk
      · exact hz.2 z h
  let T := t.eval (2+4*n+q.eval n)
  have hc := Repeat.cost_bound (f:=TreeTyped.rangeStep)
    (Repeat.nextRealizer TreeTyped.rangeStepRealizer).cost I n [] T (4*n+1)
    (show I n [] by simp [I]) (by
      intro k hk zs hz
      refine ⟨hstep k hk zs hz,?_⟩
      have h1 := htb (k+1,zs)
      have h2 := weight_nat_numeric (k+1)
      have h3 := hstate (k+1) zs hz
      have h4 := polynomial_eval_monotone t
        (show weight (k+1,zs)≤2+4*n+q.eval n by rw [weight_prod]; omega)
      dsimp only at h4
      dsimp only [T]
      omega) (by
      intro k hk
      exact (weight_nat_numeric (k+1)).trans (by omega))
  have hout := hstate 0 (countDown TreeTyped.rangeStep n [])
    (countDown_invariant I (show I n [] by simp [I]) hstep)
  have hinit := hrb n
  simp only [P,eval_add,eval_mul,eval_ofNat,eval_one,eval_comp,eval_X]
  change (TreeTyped.pair TreeTyped.identity (TreeTyped.constant ([] : List ℕ))).cost n+
    Repeat.cost TreeTyped.rangeStep (Repeat.nextRealizer TreeTyped.rangeStepRealizer).cost n []+
    weight (countDown TreeTyped.rangeStep n [])≤_
  dsimp only [T] at hc
  omega

lemma fresh_step_degree : OnlineBounded OnlineWord.stepRealizer weight 1 := by
  unfold OnlineWord.stepRealizer
  apply online_congr
  have hf := online_deterministic (typed_composition
    (typed_pair (typed_constant (A:=ℕ×List Bool) false) typed_second) typed_listCons)
  have ht := online_deterministic (typed_composition
    (typed_pair (typed_constant (A:=ℕ×List Bool) true) typed_second) typed_listCons)
  obtain ⟨p,hp,hpb⟩ := hf
  obtain ⟨q,hq,hqb⟩ := ht
  refine ⟨p+q+1, ?_,fun a=>?_⟩
  · simpa using degree_add (degree_add hp hq) (show (1 : Polynomial ℕ).natDegree≤0 by simp)
  · change 1+max _ _+max _ _≤_
    have h1 := hpb a
    have h2 := hqb a
    simp only [eval_add,eval_one]
    omega

lemma fresh_list_degree : OnlineBounded OnlineWord.listRealizer weight 2 := by
  obtain ⟨p,hp,hpb⟩ := fresh_step_degree
  obtain ⟨q,hq,hqb⟩ := typed_pair (typed_identity (A:=List ℕ))
    (typed_constant ([] : List Bool))
  let P : Polynomial ℕ := q+X*(p.comp (5*X+2)+14*X+34)+4*X+11
  have hP : P.natDegree≤2 := by
    have h1 := degree_comp hp (show (5*X+2 : Polynomial ℕ).natDegree≤1 by simpa using degree_affine 5 2)
    have h2 := degree_add h1 (degree_scale 14 (show (X : Polynomial ℕ).natDegree≤1 by simp))
    have h3 := degree_add h2 (show (34 : Polynomial ℕ).natDegree≤0 by simp)
    have h4 := degree_mul (show (X : Polynomial ℕ).natDegree≤1 by simp) h3
    have h5 := degree_add (degree_add hq h4) (degree_scale 4 (show (X : Polynomial ℕ).natDegree≤1 by simp))
    simpa [P] using degree_add h5 (show (11 : Polynomial ℕ).natDegree≤0 by simp)
  refine ⟨P,hP,fun as=>?_⟩
  let S := weight as
  have hlen : as.length≤S := list_length_le_weight as
  have bound := OnlineTree.fold_cost_bound OnlineWord.step OnlineWord.stepRealizer.cost as
    ([] : List Bool) (fun k bs=>bs.length+k=as.length) (p.eval (5*S+2)) S
    (by simp) le_rfl (by
      intro a ha k hk bs hb
      simp only [OnlineWord.step,Experiment.All,List.length_cons]
      constructor <;> omega) (by
      intro a ha k hk bs hb
      have ha' : weight a≤S := weight_mem ha
      have hbs := OnlineWord.weight_bools bs
      have hw : weight (a,bs)≤5*S+2 := by rw [weight_prod]; omega
      exact (Nat.le_add_right _ _).trans ((hpb (a,bs)).trans (polynomial_eval_monotone p hw)))
  have hlenmul := Nat.mul_le_mul_right (p.eval (5*S+2)+14*S+34) hlen
  have hout := Experiment.worst_le _ _ _ (OnlineWord.all_weight as.length [])
  have hpre := hqb as
  change (TreeTyped.pair TreeTyped.identity (TreeTyped.constant ([] : List Bool))).cost as+
    OnlineTree.Fold.cost OnlineWord.step OnlineWord.stepRealizer.cost as []+
    (OnlineWord.prepend as.length []).worst weight≤_
  simp only [P,eval_add,eval_mul,eval_comp,eval_X,eval_ofNat]
  dsimp [S] at *
  omega

/-- Actual numeric-sized range followed by all fresh coin reads. -/
lemma fresh_natural_degree : OnlineBounded OnlineWord.naturalRealizer
    (fun n=>n+weight n) 6 := by
  unfold OnlineWord.naturalRealizer
  apply online_congr
  apply online_then _ fresh_list_degree
  apply online_deterministic
  exact bounded_remeasure range_numeric_degree X (by simp) (fun n=>by simp)

end Math115.DegreeBounds
