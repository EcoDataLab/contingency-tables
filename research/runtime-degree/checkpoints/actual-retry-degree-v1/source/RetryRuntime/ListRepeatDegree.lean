import RetryRuntime.ListSeed
import OAI.Combinatorics.MatchingCount.Tapes.Codec
namespace Math115.RetryRuntimeNext
open OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds

noncomputable section
variable {A B : Type} [Codec A] [Codec B]

lemma typed_mono {f : A→B} {F : Realizer f} {e t : ℕ}
    (hF : Typed F e) (het : e ≤ t) : Typed F t := by
  obtain ⟨p,hp,hpb⟩ := hF
  exact ⟨p,hp.trans het,hpb⟩

lemma typed_reencode {A' B' : Type} [Codec A'] [Codec B']
    {f : A→B} {F : Realizer f} {e : ℕ} (hF : Typed F e)
    (i : A'→A) (g : A'→B')
    (hi : ∀ a,encode (i a)=encode a)
    (hg : ∀ a,encode (g a)=encode (f (i a))) :
    Typed (F.reencode i g hi hg) e := by
  obtain ⟨p,hp,hpb⟩ := hF
  refine ⟨p,hp,fun a=>?_⟩
  simpa only [Realizer.reencode,weight,hi a,←hg a] using hpb (i a)

lemma typed_listCase (b : B) {g : A×List A→B} {G : Realizer g} {e : ℕ}
    (hG : Typed G e) : Typed (listCase b G) e := by
  obtain ⟨q,hq,hqb⟩ := hG
  let K := (constant b (A:=List A)).cost [] + weight b + 3
  refine ⟨q+C K,(by simpa using degree_add hq (show (C K : Polynomial ℕ).natDegree ≤ 0 by simp)),fun as=>?_⟩
  cases as with
  | nil =>
    simp only [eval_add,eval_C]
    change 3+(constant b (A:=List A)).cost []+weight b ≤ q.eval (weight ([] : List A))+K
    dsimp [K]
    omega
  | cons a as =>
    have h := hqb (a,as)
    simp only [eval_add,eval_C,weight_cons]
    change 3+G.cost (a,as)+weight (g (a,as)) ≤ q.eval (1+weight a+weight as)+K
    rw [weight_prod] at h
    dsimp [K]
    omega

lemma typed_head (d : A) : Typed (head d) 1 := by
  unfold head
  apply typed_congr
  exact typed_listCase d typed_first

lemma typed_tail : Typed (tail (A:=A)) 1 := typed_listCase [] typed_second

lemma typed_less : Typed less 1 := by
  refine ⟨10*X+40,by simpa using degree_affine 10 40,fun ⟨a,b⟩=>?_⟩
  have ha := size_le_weight a
  have hb := size_le_weight b
  have ho := weight_bool (decide (a<b))
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  change 2*weight a+3*(a.bits.length+b.bits.length)+31+weight (decide (a<b)) ≤ _
  rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
  omega

lemma typed_boolNot : Typed boolNot 1 := by
  unfold boolNot
  apply typed_congr
  exact typed_choose typed_identity (typed_constant false) (typed_constant true)

lemma typed_natEqual : Typed natEqual 1 := by
  unfold natEqual
  apply typed_congr
  exact typed_choose typed_less (typed_constant false)
    (typed_choose (typed_composition (typed_pair typed_second typed_first) typed_less)
      (typed_constant false) (typed_constant true))

lemma typed_leNat : Typed leNat 1 := by
  unfold leNat
  apply typed_congr
  exact typed_composition
    (typed_composition (typed_pair typed_second typed_first) typed_less) typed_boolNot

lemma typed_minNat : Typed minNat 1 := by
  unfold minNat
  apply typed_congr
  exact typed_choose typed_leNat typed_first typed_second

/-- Quantify the exact pinned repeat witness, keeping numeric iteration allowance
and intermediate encoded size separate. Both degree gates are at least one. -/
lemma bounded_boundedRepeat {init : A→ℕ×B} {f : ℕ×B→B}
    {Init : Realizer init} {F : Realizer f} {measure : A→ℕ} {i t b s : ℕ}
    (hInit : Bounded Init measure i) (hF : Typed F t)
    (p q : Polynomial ℕ) (hp : p.natDegree ≤ b) (hq : q.natDegree ≤ s)
    (hb : 1 ≤ b) (hs : 1 ≤ s) (I : A→ℕ→B→Prop)
    (hn : ∀ a,(init a).1 ≤ p.eval (measure a))
    (hi : ∀ a,I a (init a).1 (init a).2)
    (hstep : ∀ a k,k<(init a).1→∀ z,I a (k+1) z→I a k (f (k+1,z)))
    (hw : ∀ a k z,I a k z→weight z ≤ q.eval (measure a)) :
    Bounded (composition Init (iterateDown F)) measure
      (max i (b+max t 1*max b s)) := by
  obtain ⟨r,hr,hrb⟩ := hInit
  have hNext : Typed (Repeat.nextRealizer F) (max t 1) := by
    -- Reuse the exact pair witness pointwise, avoiding transport of Typed's
    -- hidden function index through simplification of Repeat.nextRealizer.
    obtain ⟨w,hw,hwb⟩ :=
      typed_pair (e:=1) (t:=t) (typed_composition typed_first typed_predecessor_seed) hF
    refine ⟨w,(by simpa [Nat.max_assoc, Nat.max_comm, Nat.max_left_comm] using hw),?_⟩
    intro z
    change (pair (composition first predecessor) F).cost z+
      weight (z.1-1,f z) ≤ w.eval (weight z)
    exact hwb z
  obtain ⟨u,hu,hub⟩ := hNext
  let j := max b s
  let v := max t 1*j
  let P : Polynomial ℕ := r+p*(u.comp (2+4*p+q)+4*(4*p+1)+12)+10+q
  have hbJ : b ≤ j := Nat.le_max_left b s
  have hsJ : s ≤ j := Nat.le_max_right b s
  have hJ : 1 ≤ j := hb.trans hbJ
  have ht1 : 1 ≤ max t 1 := Nat.le_max_right t 1
  have hJv : j ≤ v := by dsimp [v]; nlinarith
  have harg : (2+4*p+q : Polynomial ℕ).natDegree ≤ j := by
    apply natDegree_add_le_of_degree_le
    · exact natDegree_add_le_of_degree_le (by simp) ((degree_scale 4 hp).trans hbJ)
    · exact hq.trans hsJ
  have hbody : (u.comp (2+4*p+q)+4*(4*p+1)+12 : Polynomial ℕ).natDegree ≤ v := by
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · exact degree_comp hu harg
      · exact (degree_scale 4 (natDegree_add_le_of_degree_le (degree_scale 4 hp) (by simp))).trans
          (hbJ.trans hJv)
    · simp
  have hP : P.natDegree ≤ max i (b+v) := by
    apply natDegree_add_le_of_degree_le
    · apply natDegree_add_le_of_degree_le
      · exact natDegree_add_le_of_degree_le (hr.trans (Nat.le_max_left _ _))
          ((degree_mul hp hbody).trans (Nat.le_max_right _ _))
      · simp
    · exact hq.trans (hsJ.trans (hJv.trans (by omega)))
  refine ⟨P,hP,fun a=>?_⟩
  let S := measure a
  let N := (init a).1
  let T := u.eval (2+4*p.eval S+q.eval S)
  have hN : N ≤ p.eval S := hn a
  have hsz : ∀ k<N,weight (k+1) ≤ 4*p.eval S+1 := by
    intro k hk
    have hh := weight_nat_le (k+1)
    have hbit : (k+1).size ≤ k+1 := Nat.size_le.mpr Nat.lt_two_pow_self
    omega
  have hc := Repeat.cost_bound (f:=f) (Repeat.nextRealizer F).cost (I a) N (init a).2
    T (4*p.eval S+1) (hi a) (by
      intro k hk z hz
      refine ⟨hstep a k hk z hz,?_⟩
      have h1 := hub (k+1,z)
      have h2 := hsz k hk
      have h3 := hw a (k+1) z hz
      change weight z ≤ q.eval S at h3
      have h4 := polynomial_eval_monotone u
        (show weight (k+1,z) ≤ 2+4*p.eval S+q.eval S by rw [weight_prod]; omega)
      dsimp only at h4
      dsimp only [T]
      omega) hsz
  have hout := hw a 0 (countDown f N (init a).2)
    (countDown_invariant (I a) (hi a) (hstep a))
  have hinit := hrb a
  change _ ≤ r.eval S at hinit
  simp only [P,eval_add,eval_mul,eval_ofNat,eval_one,eval_comp]
  change Init.cost a+Repeat.cost f (Repeat.nextRealizer F).cost N (init a).2+
    weight (countDown f N (init a).2) ≤ r.eval S+p.eval S*(T+4*(4*p.eval S+1)+12)+10+q.eval S
  change _ ≤ q.eval S at hout
  have hm := Nat.mul_le_mul_right (T+4*(4*p.eval S+1)+12) hN
  omega

lemma typed_boundedRepeat {init : A→ℕ×B} {f : ℕ×B→B}
    {Init : Realizer init} {F : Realizer f} {i t b s : ℕ}
    (hInit : Typed Init i) (hF : Typed F t)
    (p q : Polynomial ℕ) (hp : p.natDegree ≤ b) (hq : q.natDegree ≤ s)
    (hb : 1 ≤ b) (hs : 1 ≤ s) (I : A→ℕ→B→Prop)
    (hn : ∀ a,(init a).1 ≤ p.eval (weight a))
    (hi : ∀ a,I a (init a).1 (init a).2)
    (hstep : ∀ a k,k<(init a).1→∀ z,I a (k+1) z→I a k (f (k+1,z)))
    (hw : ∀ a k z,I a k z→weight z ≤ q.eval (weight a)) :
    Typed (composition Init (iterateDown F)) (max i (b+max t 1*max b s)) :=
  bounded_boundedRepeat hInit hF p q hp hq hb hs I hn hi hstep hw

lemma typed_dropInit : Typed (dropInit (A:=A)) 2 := by
  unfold dropInit
  exact typed_pair (typed_composition
    (typed_pair typed_second (typed_composition typed_first typed_listLength_seed))
    typed_minNat) typed_first

lemma typed_dropFast : Typed (dropFast (A:=A)) 2 := by
  unfold dropFast
  apply typed_congr
  apply typed_boundedRepeat (i:=2) (t:=1) (b:=1) (s:=1) typed_dropInit
    (typed_composition typed_second typed_tail) X X (by simp) (by simp)
    (by omega) (by omega) (fun x _ z=>z.Sublist x.1)
  · intro x
    simp only [eval_X]
    exact (min_le_right _ _).trans ((list_length_le_weight x.1).trans (by rw [weight_prod]; omega))
  · intro x; exact List.Sublist.refl _
  · intro x k hk z hz
    exact (List.tail_sublist z).trans hz
  · intro x k z hz
    simp only [eval_X]
    exact (weight_sublist hz).trans (by rw [weight_prod]; omega)

/-- Conservative degree through the literal fixed takeFast DAG. -/
lemma typed_takeFast : Typed (takeFast (A:=A)) 8 := by
  unfold takeFast
  apply typed_congr
  exact typed_composition (typed_composition (typed_pair
    (typed_composition typed_first typed_reverse)
    (typed_composition (typed_pair (typed_composition typed_first typed_listLength_seed)
      typed_second) typed_subtract_seed)) typed_dropFast) typed_reverse

end
end Math115.RetryRuntimeNext
