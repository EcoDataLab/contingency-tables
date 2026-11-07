import RetryRuntime.MapWithDegree
namespace Math115.AffineMapWithNext
open OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds Math115.PrinterRuntimeNext Math115.RetryRuntimeNext
variable {A B C : Type} [Codec A] [Codec B] [Codec C]
noncomputable section

/-- Output size alone, independent of a realizer's charged work. -/
def OutputBound (f : A → B) (s : ℕ) : Prop :=
  ∃ p : Polynomial ℕ, p.natDegree ≤ s ∧ ∀ a, weight (f a) ≤ p.eval (weight a)

lemma typed_comp_output {f : A → B} {g : B → C} {F : Realizer f} {G : Realizer g}
    {e t s : ℕ} (hF : Typed F e) (hG : Typed G t) (hf : OutputBound f s) :
    Typed (composition F G) (max e (t*s)) := by
  obtain ⟨p,hp,hpb⟩ := hF
  obtain ⟨q,hq,hqb⟩ := hG
  obtain ⟨r,hr,hrb⟩ := hf
  refine ⟨p+q.comp r,degree_add hp (degree_comp hq hr),fun a => ?_⟩
  have h1 := hpb a
  have h2 := hqb (f a)
  have h3 := polynomial_eval_monotone q (hrb a)
  simp only [eval_add,eval_comp]
  change F.cost a+G.cost (f a)+weight (g (f a)) ≤ _
  dsimp only at h3
  omega

/-- An independent bound on the entire mapped list controls both the fold
accumulator and the final reversal of the exact eager mapWith program. -/
theorem typed_mapWith_output {f : A×B → C} {F : Realizer f} {e s : ℕ}
    (hF : Typed F e) (he : 1 ≤ e) (hs : 1 ≤ s)
    (hout : OutputBound (fun z : A×List B => z.2.map (fun b => f (z.1,b))) s) :
    Typed (mapWith F) (max (1+e*s) (2*s)) := by
  obtain ⟨p,hp,hpb⟩ := hout
  have hP : (2*X+p+1 : Polynomial ℕ).natDegree ≤ s := by
    exact natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le
      ((degree_scale 2 (show (X : Polynomial ℕ).natDegree≤1 by simp)).trans hs) hp) (by simp)
  have hfold : Typed (fold (mapStepRealizer F)) (1+e*s) := by
    apply typed_fold (e:=e) (s:=s) (typed_mapStep hF he) (2*X+p+1) hP he hs
    rintro bs ⟨a,cs⟩ pre post hsplit
    let S := weight (bs,(a,cs))
    have hpre := weight_prefix hsplit
    have hm : weight (a,pre) ≤ S := by dsimp [S]; simp only [weight_prod]; omega
    have hmap := (hpb (a,pre)).trans (polynomial_eval_monotone p hm)
    have happ := weight_append (pre.map fun b => f (a,b)).reverse cs
    rw [weight_reverse] at happ
    rw [mapStep_fold,weight_prod]
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
    change _ ≤ 2*S+p.eval S+1
    dsimp [S] at *
    simp only [weight_prod] at *
    omega
  have hinit : Typed (pair (second (A:=A) (B:=List B)) (pair first (constant ([] : List C)))) 1 :=
    typed_pair_same typed_second (typed_pair_same typed_first (typed_constant []) (by decide)) (by decide)
  have hinitout : AffineOutput (fun z : A×List B => (z.2,(z.1,([] : List C)))) := by
    refine ⟨1,2,?_⟩
    rintro ⟨a,bs⟩
    simp only [weight_prod,weight_nil,one_mul]
    omega
  have hbody : Typed (composition (pair (second (A:=A) (B:=List B))
      (pair first (constant ([] : List C)))) (fold (mapStepRealizer F))) (1+e*s) := by
    exact typed_weaken (typed_comp_affine hinit hfold hinitout) (by omega)
  have hbodyout : OutputBound (fun z : A×List B =>
      z.2.foldl (fun acc b => mapStep f (b,acc)) (z.1,([] : List C))) s := by
    refine ⟨X+p,natDegree_add_le_of_degree_le (by simpa using hs) hp,fun z => ?_⟩
    have hm := hpb z
    change weight (z.2.map (fun b => f (z.1,b))) ≤ p.eval (weight z) at hm
    change weight (z.2.foldl (fun acc b => mapStep f (b,acc)) (z.1,([] : List C))) ≤ _
    rw [mapStep_fold]
    simp only [List.append_nil,weight_prod,weight_reverse,eval_add,eval_X]
    have hz : weight z = 1+weight z.1+weight z.2 := weight_prod z.1 z.2
    omega
  have hend : Typed (composition (second (A:=A) (B:=List C)) reverse) 2 :=
    Math115.PrinterRuntimeNext.typed_comp_pos typed_second typed_reverse (by decide)
  unfold mapWith
  apply typed_congr
  exact typed_comp_output hbody hend hbodyout

lemma mapWith_affine_output {f : A×B → C} (hf : AffineOutput f) :
    OutputBound (fun z : A×List B => z.2.map (fun b => f (z.1,b))) 2 := by
  obtain ⟨a,b,hab⟩ := hf
  let R : Polynomial ℕ := X*(Polynomial.C a*(1+2*X)+Polynomial.C b+1)+1
  have hR : R.natDegree ≤ 2 := by
    have ha : (1+2*X : Polynomial ℕ).natDegree≤1 := by simpa [add_comm] using degree_affine 2 1
    have hi : (Polynomial.C a*(1+2*X)+Polynomial.C b+1 : Polynomial ℕ).natDegree≤1 :=
      natDegree_add_le_of_degree_le (natDegree_add_le_of_degree_le (degree_scale a ha) (by simp)) (by simp)
    exact natDegree_add_le_of_degree_le (degree_mul (by simp) hi) (by simp)
  refine ⟨R,hR,fun z => ?_⟩
  let S := weight z
  have hz : S = 1+weight z.1+weight z.2 := weight_prod z.1 z.2
  have hlen : z.2.length ≤ S := (list_length_le_weight z.2).trans (by dsimp [S]; rw [weight_prod]; omega)
  have hm := weight_map_bound (f:=fun c => f (z.1,c)) (as:=z.2) (N:=a*(1+2*S)+b) (by
    intro c hc
    have hc' := weight_mem hc
    have harg : weight (z.1,c) ≤ 1+2*S := by dsimp [S]; simp only [weight_prod]; omega
    exact (hab (z.1,c)).trans (Nat.add_le_add_right (Nat.mul_le_mul_left a harg) b))
  simp only [R,eval_add,eval_mul,eval_C,eval_ofNat,eval_X,eval_one]
  change _ ≤ S*(a*(1+2*S)+b+1)+1
  exact hm.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hlen) 1)

/-- Affine per-element output, with arbitrary repeated shared parameter, yields
an at-most quadratic accumulator independent of the charged work degree e. -/
theorem typed_mapWith_affine {f : A×B → C} {F : Realizer f} {e : ℕ}
    (hF : Typed F e) (he : 1 ≤ e) (hf : AffineOutput f) :
    Typed (mapWith F) (max (1+2*e) 4) := by
  simpa [Nat.mul_comm] using typed_mapWith_output hF he (by decide) (mapWith_affine_output hf)

/-- If the total mapped output is independently affine, mapWith retains the
usual e+1 list traversal bound. This is a hypothesis about outputs, not work. -/
theorem typed_mapWith_linear_output {f : A×B → C} {F : Realizer f} {e : ℕ}
    (hF : Typed F e) (he : 1 ≤ e)
    (hout : AffineOutput (fun z : A×List B => z.2.map (fun b => f (z.1,b)))) :
    Typed (mapWith F) (e+1) := by
  obtain ⟨a,b,hab⟩ := hout
  have hp : OutputBound (fun z : A×List B => z.2.map (fun b => f (z.1,b))) 1 :=
    ⟨Polynomial.C a*X+Polynomial.C b,degree_affine a b,fun z => by simpa using hab z⟩
  exact typed_weaken (typed_mapWith_output hF he (by decide) hp) (by omega)
end
end Math115.AffineMapWithNext
