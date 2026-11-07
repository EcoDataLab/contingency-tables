import AffineMapWith.Degree
import ResearchBounds.DrawControlDegree
namespace Math115.RepairRuntimeNext
open OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds Math115.PrinterRuntimeNext Math115.AffineMapWithNext
variable {A B C : Type} [Codec A] [Codec B] [Codec C]
noncomputable section
lemma output_affine {f : A→B} (hf : AffineOutput f) : OutputBound f 1 := by
  obtain ⟨a,b,hab⟩ := hf
  exact ⟨Polynomial.C a*X+Polynomial.C b,degree_affine a b,fun z => by simpa using hab z⟩
lemma output_pair {f : A→B} {g : A→C} {e t : ℕ}
    (hf : OutputBound f e) (hg : OutputBound g t) :
    OutputBound (fun a => (f a,g a)) (max e t) := by
  obtain ⟨p,hp,hpb⟩ := hf
  obtain ⟨q,hq,hqb⟩ := hg
  refine ⟨p+q+1,natDegree_add_le_of_degree_le (degree_add hp hq) (by simp),fun a => ?_⟩
  have h1 := hpb a
  have h2 := hqb a
  simp only [weight_prod,eval_add,eval_one]
  omega
lemma output_composition {f : A→B} {g : B→C} {e t : ℕ}
    (hf : OutputBound f e) (hg : OutputBound g t) : OutputBound (g ∘ f) (t*e) := by
  obtain ⟨p,hp,hpb⟩ := hf
  obtain ⟨q,hq,hqb⟩ := hg
  exact ⟨q.comp p,degree_comp hq hp,fun a => by
    exact (hqb (f a)).trans (by simpa using polynomial_eval_monotone q (hpb a))⟩
lemma mapWith_poly_output {f : A×B→C} {d : ℕ} (hf : OutputBound f d) :
    OutputBound (fun z : A×List B => z.2.map (fun b=>f (z.1,b))) (d+1) := by
  obtain ⟨p,hp,hpb⟩ := hf
  let R : Polynomial ℕ := X*(p.comp (1+2*X)+1)+1
  have hR : R.natDegree≤d+1 := by
    have hi : (1+2*X : Polynomial ℕ).natDegree≤1 := by simpa [add_comm] using degree_affine 2 1
    have ht : (p.comp (1+2*X)+1).natDegree≤d :=
      natDegree_add_le_of_degree_le (by simpa using degree_comp hp hi) (by simp)
    exact natDegree_add_le_of_degree_le (by simpa [Nat.add_comm] using degree_mul (by simp) ht) (by simp)
  refine ⟨R,hR,?_⟩
  rintro ⟨a,bs⟩
  let S := weight (a,bs)
  have hl : bs.length≤S := (list_length_le_weight bs).trans (by dsimp [S]; rw [weight_prod]; omega)
  have hm := weight_map_bound (f:=fun b => f (a,b)) (as:=bs) (N:=p.eval (1+2*S)) (by
    intro b hb
    have hw := weight_mem hb
    exact (hpb (a,b)).trans (polynomial_eval_monotone p (by dsimp [S]; simp only [weight_prod]; omega)))
  simp only [R,eval_add,eval_mul,eval_X,eval_one,eval_comp,eval_ofNat]
  exact hm.trans (Nat.add_le_add_right (Nat.mul_le_mul_right _ hl) 1)
lemma typed_mapWith_poly_output {f : A×B→C} {F : Realizer f} {e d : ℕ}
    (hF : Typed F e) (he : 1≤e) (hf : OutputBound f d) :
    Typed (mapWith F) (max (1+e*(d+1)) (2*(d+1))) :=
  typed_mapWith_output hF he (by omega) (mapWith_poly_output hf)
/-- Exact filterWith tags every element, filters the tags and projects them.
Boolean output has fixed weight, so its shared-parameter mapper output is linear. -/
lemma typed_filterWith_output {f : A×B→Bool} {F : Realizer f} {e : ℕ}
    (hF : Typed F e) (he : 1≤e) : Typed (filterWith F) (max (e+1) 4) := by
  have htag : Typed (pair (second (A:=A) (B:=B)) F) e :=
    typed_pair_same (typed_weaken typed_second he) hF he
  have hout : AffineOutput (fun z : A×List B => z.2.map (fun b => (b,f (z.1,b)))) := by
    refine ⟨6,0,?_⟩
    rintro ⟨a,bs⟩
    have hm := map_affine_weight (f:=fun b : B => (b,f (a,b))) 1 4 (fun b : B => by
      have hb := weight_bool (f (a,b))
      rw [weight_prod]
      omega) bs
    have hbs := weight_snd (a,bs)
    simp only [add_zero]
    exact hm.trans (Nat.mul_le_mul_left 6 hbs)
  have hmap : Typed (mapWith (pair (second (A:=A) (B:=B)) F)) (e+1) :=
    typed_mapWith_linear_output htag he hout
  have hfilter : Typed (filter (second (A:=B) (B:=Bool))) 4 :=
    Math115.DrawDegree.typed_filter typed_second (by decide)
  have hbody : Typed (composition (mapWith (pair (second (A:=A) (B:=B)) F))
      (filter second)) (max (e+1) 4) := typed_comp_affine hmap hfilter hout
  have hbodyout : AffineOutput (fun z : A×List B =>
      (z.2.map (fun b => (b,f (z.1,b)))).filter (fun t => t.2)) := by
    obtain ⟨a,b,hab⟩ := hout
    exact ⟨a,b,fun z => (weight_sublist List.filter_sublist).trans (hab z)⟩
  have hproject : Typed (TreeTyped.map (first (A:=B) (B:=Bool))) 2 :=
    typed_map_affine typed_first (by decide)
      ⟨1,0,fun z => by simpa only [one_mul,add_zero] using weight_fst z⟩
  unfold filterWith
  apply typed_congr
  exact typed_weaken (typed_comp_affine hbody hproject hbodyout) (by omega)

end
end Math115.RepairRuntimeNext
