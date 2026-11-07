/- Quantitative witnesses for the actual pinned TreeTyped arithmetic programs.
   Multiplication's degree-six bound follows its exact list-fold construction;
   no unit-cost arithmetic model is substituted. -/
import ResearchBounds.TreeDegreeBounds

namespace Math115.DegreeBounds
open OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial

variable {A B : Type} [Codec A] [Codec B]

lemma typed_choose {f : A→Bool} {g h : A→B}
    {F : TreeTyped.Realizer f} {G : TreeTyped.Realizer g} {H : TreeTyped.Realizer h}
    {e t u : ℕ} (hF : Typed F e) (hG : Typed G t) (hH : Typed H u) :
    Typed (TreeTyped.choose F G H) (max (max (max e t) u) 1) := by
  obtain ⟨p,hp,hpb⟩ := hF
  obtain ⟨q,hq,hqb⟩ := hG
  obtain ⟨r,hr,hrb⟩ := hH
  refine ⟨p+q+r+7*X+18, ?_,fun a=>?_⟩
  · have h1 := degree_add (degree_add hp hq) hr
    have h2 := degree_add h1 (degree_scale 7 (show (X : Polynomial ℕ).natDegree≤1 by simp))
    simpa using degree_add h2 (show (18 : Polynomial ℕ).natDegree≤0 by simp)
  · have h1:=hpb a
    have h2:=hqb a
    have h3:=hrb a
    simp only [eval_add,eval_mul,eval_ofNat,eval_X]
    change F.cost a+(if f a then G.cost a else H.cost a)+7*weight a+18+
      weight (if f a then g a else h a)≤_
    cases f a <;> simp only [Bool.false_eq_true,↓reduceIte] <;> omega

lemma typed_add : Typed TreeTyped.add 1 := by
  refine ⟨20*X+30,by simpa using degree_affine 20 30,fun ⟨a,b⟩=>?_⟩
  have ha:=size_le_weight a
  have hb:=size_le_weight b
  have ho:=weight_add a b
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  change (2*weight a+5+9*(a.bits.length+b.bits.length)+20)+weight (a+b)≤_
  rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
  omega

lemma typed_toBits : Typed TreeTyped.toBits 1 := by
  refine ⟨X+1,by simpa using degree_affine 1 1,fun _=>?_⟩
  simp only [eval_add,eval_X,eval_one]
  change 1+weight _ ≤ weight _+1
  rw [weight_nat]
  omega

lemma typed_listCons_arithmetic : Typed (TreeTyped.listCons (A:=A)) 1 := by
  refine ⟨X+1,by simpa using degree_affine 1 1,fun ⟨a,as⟩=>?_⟩
  simp only [eval_add,eval_X,eval_one,weight_prod,weight_cons]
  change 1+(1+weight a+weight as)≤(1+weight a+weight as)+1
  omega

lemma typed_reverse : Typed (TreeTyped.reverse (A:=A)) 2 := by
  unfold TreeTyped.reverse
  apply typed_congr
  apply typed_composition (e:=1) (t:=2) (typed_pair typed_identity (typed_constant []))
  apply typed_fold (s:=1) typed_listCons_arithmetic (2*X+1)
    (show (2*X+1 : Polynomial ℕ).natDegree≤1 by simpa using degree_affine 2 1)
    (by omega) (by omega)
  intro as bs pre post he
  have hp:=weight_prefix he
  have hh:=weight_append pre.reverse bs
  rw [weight_reverse] at hh
  simp only [List.foldl_flip_cons_eq_append']
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  omega

lemma typed_double : Typed TreeTyped.double 1 := by
  unfold TreeTyped.double
  apply typed_congr
  exact typed_composition (typed_pair typed_identity typed_identity) typed_add

lemma typed_mulStep : Typed TreeTyped.mulStepRealizer 1 := by
  unfold TreeTyped.mulStepRealizer
  apply typed_congr
  apply typed_pair (e:=1) (t:=1) (typed_composition typed_second typed_first)
  apply typed_composition (e:=1) _ typed_add
  apply typed_pair (e:=1) (t:=1)
  · exact typed_composition (typed_composition typed_second typed_second) typed_double
  · exact typed_choose typed_first (typed_composition typed_second typed_first) (typed_constant 0)

lemma typed_mulFold : Typed (TreeTyped.fold TreeTyped.mulStepRealizer) 3 := by
  apply typed_fold (s:=2) typed_mulStep (10*(X+1)^2)
    (show (10*(X+1)^2 : Polynomial ℕ).natDegree≤2 by
      have h1 : (X+1 : Polynomial ℕ).natDegree≤1 := by simpa using degree_affine 1 1
      simpa using degree_scale 10 (natDegree_pow_le_of_le 2 h1))
    (by omega) (by omega)
  rintro bs ⟨n,c⟩ pre post he
  let S:=weight (bs,(n,c))
  have hpre : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans
    (by dsimp [S]; simp only [weight_prod]; omega))
  have hn : n.size≤S := by have h:=size_le_weight n; dsimp [S]; simp only [weight_prod]; omega
  have hc : c.size≤S := by have h:=size_le_weight c; dsimp [S]; simp only [weight_prod]; omega
  have hn' : weight n≤S := by dsimp [S]; simp only [weight_prod]; omega
  have hs:=mulStep_fold_size pre n c
  have ho:=weight_nat_le (pre.foldl (fun z b=>TreeTyped.mulStep (b,z)) (n,c)).2
  have hr:=mulStep_fold_first pre n c
  rw [←Prod.eta (pre.foldl (fun z b=>TreeTyped.mulStep (b,z)) (n,c)),weight_prod,hr]
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change _≤10*(S+1)^2
  have hmul : pre.length*(n.size+3)≤S*(S+3) := Nat.mul_le_mul hpre (by omega)
  nlinarith

/-- Charged cost and output size of the actual supplied binary multiplication
    realizer. Six is a conservative degree bound, not a lower bound. -/
theorem typed_multiply : Typed TreeTyped.multiply 6 := by
  unfold TreeTyped.multiply
  apply typed_congr
  apply typed_composition (e:=6) _ typed_second
  apply typed_composition (e:=2) _ typed_mulFold
  apply typed_pair (e:=2) (t:=1)
  · exact typed_composition (typed_composition typed_first typed_toBits) typed_reverse
  · exact typed_pair typed_second (typed_constant 0)

end Math115.DegreeBounds
