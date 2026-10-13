import CountBounds.ScalarCircuitDegreeV2
import ResearchBounds.DrawControlDegree

/-! Reuses the published exact numeric range proof without importing unrelated
online fresh-word compiler dependencies. No actual range implementation changes. -/
namespace Math115.DrawRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds Math115.DrawDegree Math115.WordCountSeedDegrees
open Math115.ListRepeatDegreeV1
noncomputable section
lemma typed_rangeStep : Typed rangeStepRealizer 1 := by
  exact typed_composition
    (typed_pair (typed_composition typed_first typed_predecessor_seed) typed_second) typed_listCons

lemma range_numeric_degree : Bounded TreeTyped.range id 3 := by
  unfold TreeTyped.range
  apply bounded_congr
  obtain ⟨r,hr,hrb⟩ := bounded_remeasure
    (typed_pair (typed_identity (A:=ℕ)) (typed_constant ([] : List ℕ)))
    (4*X+1) (show (4*X+1 : Polynomial ℕ).natDegree≤1 by simpa using degree_affine 4 1)
    (fun n=>by simpa using weight_nat_numeric n)
  obtain ⟨t,ht,htb⟩ := typed_pair (typed_composition typed_first typed_predecessor_seed) typed_rangeStep
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
      change (Repeat.nextRealizer TreeTyped.rangeStepRealizer).cost (k+1,zs)+
        weight (Repeat.next TreeTyped.rangeStep (k+1,zs))≤t.eval (weight (k+1,zs)) at h1
      dsimp only [T]
      exact (Nat.le_add_right _ _).trans (h1.trans h4)) (by
      intro k hk
      exact (weight_nat_numeric (k+1)).trans (by omega))
  have hout := hstate 0 (countDown TreeTyped.rangeStep n [])
    (countDown_invariant I (show I n [] by simp [I]) hstep)
  have hinit : (TreeTyped.pair TreeTyped.identity
      (TreeTyped.constant ([] : List ℕ))).cost n≤r.eval n :=
    (Nat.le_add_right _ _).trans (hrb n)
  simp only [P,eval_add,eval_mul,eval_ofNat,eval_one,eval_comp,eval_X]
  change (TreeTyped.pair TreeTyped.identity (TreeTyped.constant ([] : List ℕ))).cost n+
    Repeat.cost TreeTyped.rangeStep (Repeat.nextRealizer TreeTyped.rangeStepRealizer).cost n []+
    weight (countDown TreeTyped.rangeStep n [])≤
      r.eval n+n*(t.eval (2+4*n+q.eval n)+4*(4*n+1)+12)+10+q.eval n
  dsimp only [T] at hc
  omega

lemma typed_getDFast {A : Type} [Codec A] (d : A) : Typed (getDFast d) 2 := by
  unfold getDFast
  apply typed_congr
  exact typed_composition typed_dropFast (typed_head d)

lemma typed_boundedRange {A : Type} [Codec A] {f : A→ℕ} {F : Realizer f}
    {e d : ℕ} (hF : Typed F e) (p : Polynomial ℕ) (hp : p.natDegree≤d)
    (hn : ∀ a,f a≤p.eval (weight a)) :
    Typed (composition F range) (max e (3*d)) := by
  obtain ⟨q,hq,hqb⟩ := hF
  obtain ⟨r,hr,hrb⟩ := range_numeric_degree
  refine ⟨q+r.comp p,degree_add hq (degree_comp hr hp),fun a=>?_⟩
  have h1:=hqb a
  have h2:=hrb (f a)
  have h3:=polynomial_eval_monotone r (hn a)
  simp only [eval_add,eval_comp]
  change F.cost a+range.cost (f a)+weight (List.range (f a))≤_
  dsimp only [id] at h2
  dsimp only at h3
  omega
end
end Math115.DrawRuntimeNext
