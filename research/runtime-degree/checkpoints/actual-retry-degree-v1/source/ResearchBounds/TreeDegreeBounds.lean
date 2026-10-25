/- Private quantitative reconstruction of the pinned TreeTyped witnesses.
   The realizer and codec are fixed; no replacement machine is introduced. -/
import OAI.Combinatorics.MatchingCount.Complexity.TreeCostMeasure

namespace Math115.DegreeBounds
open OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial

lemma degree_add {p q : Polynomial ℕ} {a b : ℕ}
    (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (p+q).natDegree ≤ max a b :=
  (natDegree_add_le p q).trans (max_le_max hp hq)
lemma degree_mul {p q : Polynomial ℕ} {a b : ℕ}
    (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (p*q).natDegree ≤ a+b :=
  natDegree_mul_le.trans (Nat.add_le_add hp hq)
lemma degree_comp {p q : Polynomial ℕ} {a b : ℕ}
    (hp : p.natDegree ≤ a) (hq : q.natDegree ≤ b) :
    (p.comp q).natDegree ≤ a*b :=
  natDegree_comp_le.trans (Nat.mul_le_mul hp hq)
lemma degree_scale (k : ℕ) {p : Polynomial ℕ} {a : ℕ} (hp : p.natDegree ≤ a) :
    (C k*p).natDegree ≤ a := (natDegree_C_mul_le k p).trans hp
lemma degree_affine (k c : ℕ) : (C k*X+C c : Polynomial ℕ).natDegree ≤ 1 := by
  exact natDegree_add_le_of_degree_le (degree_scale k (by simp)) (by simp)

def Bounded {A B : Type} [Codec A] [Codec B] {f : A → B}
    (F : TreeTyped.Realizer f) (measure : A → ℕ) (E : ℕ) : Prop :=
  ∃ p : Polynomial ℕ, p.natDegree ≤ E ∧
    ∀ a, F.cost a + weight (f a) ≤ p.eval (measure a)
abbrev Typed {A B : Type} [Codec A] [Codec B] {f : A → B}
    (F : TreeTyped.Realizer f) (E : ℕ) := Bounded F weight E

variable {A B D : Type} [Codec A] [Codec B] [Codec D]

lemma typed_identity : Typed (TreeTyped.identity (A:=A)) 1 := by
  refine ⟨X+1, by simpa using degree_affine 1 1, ?_⟩
  intro a
  simp [TreeTyped.identity, weight, Polynomial.eval_add, Polynomial.eval_X, Nat.add_comm]
lemma typed_first : Typed (TreeTyped.first (A:=A) (B:=B)) 1 := by
  refine ⟨7*X+11, by simpa using degree_affine 7 11, ?_⟩
  intro ⟨a,b⟩
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  change 6*weight a+weight b+11+weight a≤7*(1+weight a+weight b)+11
  omega
lemma typed_second : Typed (TreeTyped.second (A:=A) (B:=B)) 1 := by
  refine ⟨4*X+7, by simpa using degree_affine 4 7, ?_⟩
  intro ⟨a,b⟩
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  change 3*weight a+7+weight b≤4*(1+weight a+weight b)+7
  omega
lemma typed_constantData (b : OAI.MatchingFPRAS.TreeData.Data) :
    Typed (TreeTyped.constantData (A:=A) b) 1 := by
  induction b with
  | nil =>
    refine ⟨X+3, by simpa using degree_affine 1 3, ?_⟩
    intro a
    simp [TreeTyped.constantData,weight,Codec.encode,OAI.MatchingFPRAS.TreeFunction.size_nil]
  | cons b c hb hc =>
    obtain ⟨p,hp,hpb⟩ := hb
    obtain ⟨q,hq,hqb⟩ := hc
    refine ⟨7*p+q+11*X+32, ?_, ?_⟩
    · have h1 := degree_scale 7 hp
      have h2 := degree_add h1 hq
      have h3 := degree_add h2 (degree_scale 11 (show (X : Polynomial ℕ).natDegree≤1 by simp))
      simpa using degree_add h3 (show (32 : Polynomial ℕ).natDegree≤0 by simp)
    · intro a
      have h1 := hpb a
      have h2 := hqb a
      dsimp only at h1 h2
      simp only [eval_add,eval_mul,eval_ofNat,eval_X]
      change (TreeTyped.pair (TreeTyped.constantData b) (TreeTyped.constantData c)).cost a+
        weight (OAI.MatchingFPRAS.TreeData.Data.cons b c) ≤ _
      have he : weight (OAI.MatchingFPRAS.TreeData.Data.cons b c)=1+weight b+weight c := by
        simp [weight,Codec.encode]
        omega
      rw [he]
      change (TreeTyped.constantData b).cost a+(TreeTyped.constantData c).cost a+
        11*weight a+6*weight b+31+(1+weight b+weight c)≤_
      omega
lemma typed_constant (b : B) : Typed (TreeTyped.constant (A:=A) b) 1 :=
  typed_constantData (encode b)

lemma typed_composition {f : A→B} {g : B→D} {F : TreeTyped.Realizer f} {G : TreeTyped.Realizer g}
    {e t : ℕ} (hF : Typed F e) (hG : Typed G t) :
    Typed (TreeTyped.composition F G) (max e (t*e)) := by
  obtain ⟨p,hp,hpb⟩ := hF
  obtain ⟨q,hq,hqb⟩ := hG
  refine ⟨p+q.comp p, degree_add hp (degree_comp hq hp), ?_⟩
  intro a
  have h1 := hpb a
  have h2 := hqb (f a)
  have h3 := polynomial_eval_monotone q (show weight (f a)≤p.eval (weight a) by omega)
  simp only [eval_add,eval_comp]
  change F.cost a+G.cost (f a)+weight (g (f a))≤_
  dsimp only at h3
  omega
lemma typed_pair {f : A→B} {g : A→D} {F : TreeTyped.Realizer f} {G : TreeTyped.Realizer g}
    {e t : ℕ} (hF : Typed F e) (hG : Typed G t) :
    Typed (TreeTyped.pair F G) (max (max e t) 1) := by
  obtain ⟨p,hp,hpb⟩ := hF
  obtain ⟨q,hq,hqb⟩ := hG
  refine ⟨7*p+q+11*X+32, ?_, ?_⟩
  · have h1 := degree_add (degree_scale 7 hp) hq
    have h2 := degree_add h1 (degree_scale 11 (show (X : Polynomial ℕ).natDegree≤1 by simp))
    simpa using degree_add h2 (show (32 : Polynomial ℕ).natDegree≤0 by simp)
  · intro a
    have h1 := hpb a
    have h2 := hqb a
    simp only [eval_add,eval_mul,eval_ofNat,eval_X]
    rw [weight_prod]
    change F.cost a+G.cost a+11*weight a+6*weight (f a)+31+
      (1+weight (f a)+weight (g a))≤_
    omega
lemma typed_congr {f g : A→B} {F : TreeTyped.Realizer f} {e : ℕ}
    (h : ∀ a,f a=g a) (hF : Typed F e) : Typed (F.congr h) e := by
  obtain ⟨p,hp,hpb⟩ := hF
  exact ⟨p,hp,fun a=>by simpa only [TreeTyped.Realizer.congr,←h a] using hpb a⟩

lemma bounded_congr {f g : A→B} {F : TreeTyped.Realizer f} {m : A→ℕ} {e : ℕ}
    (h : ∀ a,f a=g a) (hF : Bounded F m e) : Bounded (F.congr h) m e := by
  obtain ⟨p,hp,hpb⟩ := hF
  exact ⟨p,hp,fun a=>by simpa only [TreeTyped.Realizer.congr,←h a] using hpb a⟩

lemma bounded_remeasure {f : A→B} {F : TreeTyped.Realizer f} {m n : A→ℕ}
    {e t : ℕ} (hF : Bounded F m e) (p : Polynomial ℕ) (hp : p.natDegree≤t)
    (hm : ∀ a,m a≤p.eval (n a)) : Bounded F n (e*t) := by
  obtain ⟨q,hq,hqb⟩ := hF
  exact ⟨q.comp p,degree_comp hq hp,fun a=>(hqb a).trans
    (by simpa using polynomial_eval_monotone q (hm a))⟩

lemma typed_fold {f : A×B→B} {F : TreeTyped.Realizer f} {e s : ℕ}
    (hF : Typed F e) (p : Polynomial ℕ) (hp : p.natDegree≤ s)
    (he : 1≤e) (hs : 1≤ s)
    (hsize : ∀ (as : List A) (b : B) pre post,as=pre++post→
      weight (pre.foldl (fun z a=>f (a,z)) b)≤p.eval (weight (as,b))) :
    Typed (TreeTyped.fold F) (1+e*s) := by
  obtain ⟨q,hq,hqb⟩ := hF
  let P : Polynomial ℕ := X*(q.comp (1+X+p)+14*X+34)+10+p
  have hP : P.natDegree≤1+e*s := by
    have hi : (1+X+p : Polynomial ℕ).natDegree≤ s :=
      natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le (by simp) (by simpa using hs)) hp
    have h1 := degree_comp hq hi
    have h2 : (14*X : Polynomial ℕ).natDegree≤e*s :=
      (degree_scale 14 (show (X : Polynomial ℕ).natDegree≤1 by simp)).trans
        (by nlinarith)
    have h3 : (q.comp (1+X+p)+14*X+34).natDegree≤e*s :=
      natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le h1 h2) (by simp)
    have h4 := degree_mul (show (X : Polynomial ℕ).natDegree≤1 by simp) h3
    exact natDegree_add_le_of_degree_le
      (natDegree_add_le_of_degree_le h4 (by simp)) (hp.trans (by nlinarith))
  refine ⟨P,hP,fun ⟨as,b⟩=>?_⟩
  let S:=weight (as,b)
  let T:=q.eval (1+S+p.eval S)
  have hs : weight as≤S := by dsimp [S]; rw [weight_prod]; omega
  have hc := Fold.cost_prefix_bound (f:=f) F.cost as b T S hs (by
    intro pre a post he
    have hz := hsize as b pre (a::post) he
    change _≤p.eval S at hz
    have ha : weight a≤S := (weight_mem (by simp [he])).trans hs
    have hq' := hqb (a,pre.foldl (fun z c=>f (c,z)) b)
    have hm := polynomial_eval_monotone q (show weight (a,pre.foldl (fun z c=>f (c,z)) b)≤1+S+p.eval S by rw [weight_prod]; omega)
    dsimp only at hm
    dsimp only [T]
    omega)
  have hout := hsize as b as [] (by simp)
  change _≤p.eval S at hout
  have hlen : as.length≤S := (list_length_le_weight as).trans hs
  simp only [P,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp]
  change Fold.cost f F.cost as b+weight (as.foldl (fun z a=>f (a,z)) b)≤_
  change _≤S*(T+14*S+34)+10+p.eval S
  nlinarith

end Math115.DegreeBounds
