/- Private checkpoint12 tightened scalar output candidate v2. Not compiled.
No realizer or codec is replaced. LinearOutput is an independent semantic size
certificate; Circuit combines that with exact-realizer execution plus output. -/
import CountBounds.ParserDegree

namespace Math115.ScalarCircuitDegreeV2
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped
open Math115.DegreeBounds Math115.ScalarOutputDegree Math115.WordCountSeedDegrees
open Math115.ListRepeatDegreeV1 Polynomial DensePrograms
open OAI.ContingencyTables.ProfilePrograms

noncomputable section
variable {A B D : Type} [Codec A] [Codec B] [Codec D]

def LinearOutput (f : A→B) : Prop :=
  ∃ a b : ℕ, ∀ x,weight (f x)≤a*weight x+b

def Circuit {f : A→B} (F : Realizer f) (e : ℕ) : Prop :=
  Typed F e ∧ LinearOutput f

lemma linear_identity : LinearOutput (id : A→A) := ⟨1,0,fun x=>by simp⟩
lemma linear_first : LinearOutput (Prod.fst : A×B→A) := by
  refine ⟨1,0,fun ⟨a,b⟩=>?_⟩
  simp only [weight_prod,one_mul,add_zero]
  omega
lemma linear_second : LinearOutput (Prod.snd : A×B→B) := by
  refine ⟨1,0,fun ⟨a,b⟩=>?_⟩
  simp only [weight_prod,one_mul,add_zero]
  omega
lemma linear_constant (b : B) : LinearOutput (fun _ : A=>b) :=
  ⟨0,weight b,fun x=>by simp⟩
lemma linear_pair {f : A→B} {g : A→D} (hf : LinearOutput f) (hg : LinearOutput g) :
    LinearOutput (fun x=>(f x,g x)) := by
  obtain ⟨a,b,hf⟩ := hf
  obtain ⟨c,d,hg⟩ := hg
  refine ⟨a+c,b+d+1,fun x=>?_⟩
  have h1 := hf x
  have h2 := hg x
  rw [weight_prod]
  nlinarith
lemma linear_composition {f : A→B} {g : B→D}
    (hf : LinearOutput f) (hg : LinearOutput g) : LinearOutput (g ∘ f) := by
  obtain ⟨a,b,hf⟩ := hf
  obtain ⟨c,d,hg⟩ := hg
  refine ⟨c*a,c*b+d,fun x=>?_⟩
  have h1 := hg (f x)
  have h2 := Nat.mul_le_mul_left c (hf x)
  change weight (g (f x))≤_
  nlinarith

lemma typed_composition_linear {f : A→B} {g : B→D}
    {F : Realizer f} {G : Realizer g} {e t : ℕ}
    (hF : Typed F e) (hG : Typed G t) (hf : LinearOutput f) :
    Typed (composition F G) (max e t) := by
  obtain ⟨a,b,hf⟩ := hf
  simpa only [Nat.mul_one] using typed_composition_from_output_size hF hG
    (C a*X+C b) (degree_affine a b) (by
      intro x
      simpa only [eval_add,eval_mul,eval_C,eval_X] using hf x)

lemma circuit_identity : Circuit (identity (A:=A)) 1 := ⟨typed_identity,linear_identity⟩
lemma circuit_first : Circuit (first (A:=A) (B:=B)) 1 := ⟨typed_first,linear_first⟩
lemma circuit_second : Circuit (second (A:=A) (B:=B)) 1 := ⟨typed_second,linear_second⟩
lemma circuit_constant (b : B) : Circuit (constant (A:=A) b) 1 :=
  ⟨typed_constant b,linear_constant b⟩
lemma circuit_composition {f : A→B} {g : B→D}
    {F : Realizer f} {G : Realizer g} {e t : ℕ}
    (hF : Circuit F e) (hG : Circuit G t) :
    Circuit (composition F G) (max e t) :=
  ⟨typed_composition_linear hF.1 hG.1 hF.2,linear_composition hF.2 hG.2⟩
lemma circuit_pair {f : A→B} {g : A→D}
    {F : Realizer f} {G : Realizer g} {e t : ℕ}
    (hF : Circuit F e) (hG : Circuit G t) :
    Circuit (pair F G) (max (max e t) 1) :=
  ⟨typed_pair hF.1 hG.1,linear_pair hF.2 hG.2⟩
lemma circuit_congr {f g : A→B} {F : Realizer f} {e : ℕ}
    (h : ∀ x,f x=g x) (hF : Circuit F e) : Circuit (F.congr h) e := by
  refine ⟨typed_congr h hF.1,?_⟩
  obtain ⟨a,b,hout⟩ := hF.2
  exact ⟨a,b,fun x=>by simpa only [←h x] using hout x⟩
lemma circuit_mono {f : A→B} {F : Realizer f} {e t : ℕ}
    (hF : Circuit F e) (het : e≤t) : Circuit F t := ⟨typed_mono hF.1 het,hF.2⟩

lemma circuit_composition_same {f : A→B} {g : B→D}
    {F : Realizer f} {G : Realizer g} {e : ℕ}
    (hF : Circuit F e) (hG : Circuit G e) : Circuit (composition F G) e :=
  by simpa only [max_self] using circuit_composition hF hG
lemma circuit_pair_same {f : A→B} {g : A→D}
    {F : Realizer f} {G : Realizer g} {e : ℕ}
    (he : 1≤e) (hF : Circuit F e) (hG : Circuit G e) : Circuit (pair F G) e :=
  by simpa only [max_self,Nat.max_eq_left he] using circuit_pair hF hG

lemma circuit_add : Circuit add 1 := by
  refine ⟨typed_add,4,1,fun ⟨a,b⟩=>?_⟩
  change weight (a+b) ≤ 4*weight (a,b)+1
  have h := weight_add a b
  rw [weight_prod]
  omega
lemma circuit_multiply : Circuit multiply 6 := by
  refine ⟨typed_multiply,4,1,fun ⟨a,b⟩=>?_⟩
  change weight (a*b) ≤ 4*weight (a,b)+1
  have h := weight_mul_output a b
  rw [weight_prod]
  omega
lemma circuit_fixedPower (k : ℕ) :
    Circuit (Math115.LatticeScheduleProgram.fixedPowerRealizer k) 6 :=
  ⟨typed_actual_fixedPower k,4*k,5,fun a=>weight_fixed_power_output a k⟩
lemma circuit_listLength {E : Type} [Codec E] : Circuit (listLength (A:=E)) 2 := by
  refine ⟨typed_listLength_seed,4,1,fun as=>?_⟩
  have h := weight_nat_numeric as.length
  have hl := list_length_le_weight as
  omega
lemma circuit_listSum : Circuit listSum 3 := by
  refine ⟨typed_listSum_seed,4,1,fun as=>?_⟩
  have h := weight_nat_le as.sum
  -- Adapted locally from pinned IntegerMatrixPrograms.sum_size_le_weight
  -- (IntegerMatrixProgram.lean:165-173), using the existing arithmetic helpers.
  have hs : as.sum.size ≤ weight as := by
    clear h
    induction as with
    | nil => simp
    | cons a as ih =>
      have ha := size_le_weight a
      have hsum := nat_size_add a as.sum
      rw [List.sum_cons,weight_cons]
      have hm : max a.size as.sum.size ≤ weight a+weight as := max_le (by omega) (by omega)
      omega
  omega
lemma circuit_log : Circuit ceilLogTwoRealizer 2 := by
  refine ⟨typed_ceilLogTwo_seed,4,1,fun n=>?_⟩
  have h := weight_nat_numeric (Nat.clog 2 n)
  have hs := (Nat.size_le_size (Nat.sub_le n 1)).trans (size_le_weight n)
  rw [clog_two_eq_size_pred] at h ⊢
  omega

lemma head_output_weight_zero (ns : List ℕ) : weight (ns.headD 0)≤weight ns+1 := by
  cases ns with
  | nil => decide
  | cons n ns =>
    simp only [List.headD_cons,weight_cons]
    omega

lemma marginLists_linear : LinearOutput GreedyFeasibleTable.marginLists := by
  refine ⟨2,1,fun ns=>?_⟩
  have hrest : ns.tail.tail.Sublist ns :=
    (List.tail_sublist ns.tail).trans (List.tail_sublist ns)
  have hr := weight_sublist ((List.take_sublist (ns.headD 0) ns.tail.tail).trans hrest)
  have hc := weight_sublist ((List.take_sublist (ns.tail.headD 0)
    (ns.tail.tail.drop (ns.headD 0))).trans
    ((List.drop_sublist (ns.headD 0) ns.tail.tail).trans hrest))
  change weight (ns.tail.tail.take (ns.headD 0),
    (ns.tail.tail.drop (ns.headD 0)).take (ns.tail.headD 0))≤_
  rw [weight_prod]
  omega
lemma samplingPrecision_linear : LinearOutput ProfilePrograms.samplingPrecision := by
  refine ⟨1,1,fun ns=>?_⟩
  have h := head_output_weight_zero (ns.drop (2+ns.headD 0+ns.tail.headD 0))
  have hs := weight_sublist (List.drop_sublist (2+ns.headD 0+ns.tail.headD 0) ns)
  change weight ((ns.drop (2+ns.headD 0+ns.tail.headD 0)).headD 0)≤_
  omega
lemma samplingInput_linear : LinearOutput ProfilePrograms.samplingInput :=
  linear_pair marginLists_linear samplingPrecision_linear
lemma parse_linear : LinearOutput OAI.MatchingFPRAS.LiteralParse.parse :=
  ⟨7,1,Math115.ParserDegreeV1.parse_output_weight⟩
lemma parsedSampling_linear : LinearOutput parsedSampling :=
  linear_composition parse_linear samplingInput_linear
lemma circuit_parsedSampling : Circuit parsedSamplingRealizer 16 :=
  ⟨Math115.ParserDegreeV1.typed_parsedSampling,parsedSampling_linear⟩

end
end Math115.ScalarCircuitDegreeV2
