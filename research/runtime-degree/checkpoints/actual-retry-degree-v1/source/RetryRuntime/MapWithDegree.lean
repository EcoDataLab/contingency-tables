import RetryRuntime.RangeDegree
import PrinterRuntime.LinearCollections
namespace Math115.RetryRuntimeNext
open OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds Math115.PrinterRuntimeNext
variable {A B C : Type} [Codec A] [Codec B] [Codec C]
noncomputable section
lemma typed_mapStep {f : A×B→C} {F : Realizer f} {e : ℕ}
    (hF : Typed F e) (he : 1≤e) : Typed (mapStepRealizer F) e := by
  unfold mapStepRealizer
  have harg : Typed (pair (composition (second (A:=B) (B:=A×List C)) first) first) 1 :=
    typed_pair_same (Math115.PrinterRuntimeNext.typed_comp_pos typed_second typed_first (by decide)) typed_first (by decide)
  have hval : Typed (composition (pair (composition (second (A:=B) (B:=A×List C)) first) first) F) e := by
    simpa only [Nat.mul_one] using Math115.PrinterRuntimeNext.typed_comp_pos harg hF he
  have hpair : Typed (pair
      (composition (pair (composition (second (A:=B) (B:=A×List C)) first) first) F)
      (composition second second)) e :=
    typed_pair_same hval
      (typed_weaken (Math115.PrinterRuntimeNext.typed_comp_pos typed_second typed_second (by decide)) he) he
  have hcons : Typed (composition (pair
      (composition (pair (composition (second (A:=B) (B:=A×List C)) first) first) F)
      (composition second second)) listCons) e := by
    simpa only [Nat.one_mul] using Math115.PrinterRuntimeNext.typed_comp_pos hpair typed_listCons_arithmetic (by decide)
  exact typed_pair_same
    (typed_weaken (Math115.PrinterRuntimeNext.typed_comp_pos typed_second typed_first (by decide)) he) hcons he

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
    simpa only [Nat.mul_one] using Math115.PrinterRuntimeNext.typed_comp_pos hinit hfold (by omega)
  exact Math115.PrinterRuntimeNext.typed_comp_pos hbody
    (Math115.PrinterRuntimeNext.typed_comp_pos typed_second typed_reverse (by decide)) (by decide)

end
end Math115.RetryRuntimeNext
