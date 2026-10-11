/- PRIVATE SOURCE-ONLY SEED DEGREE DRAFT. NOT COMPILED.
Exact pinned realizers and encodings are retained. These proposed proofs close
three of ScheduleWordCountDegree.SeedBounds' five gates if accepted; catalogue
and parser certificates still remain. No count/full-runtime numeral is proved.
-/
import ResearchBounds.TreeArithmeticDegree
import Math115.LatticeScheduleProgram

namespace Math115.WordCountSeedDegrees
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped
open Math115.DegreeBounds Polynomial DensePrograms

noncomputable section

lemma typed_subtract_seed : Typed subtract 1 := by
  refine ⟨50*X+100, by simpa using degree_affine 50 100, fun ⟨a,b⟩=>?_⟩
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

lemma typed_predecessor_seed : Typed predecessor 1 :=
  typed_composition (typed_pair typed_identity (typed_constant 1)) typed_subtract_seed

lemma typed_listLength_seed {A : Type} [Codec A] :
    Typed (listLength (A:=A)) 2 := by
  unfold listLength
  apply typed_congr
  apply typed_composition (e := 1) (t := 2) (typed_pair typed_identity (typed_constant 0))
  apply typed_fold (s := 1)
    (typed_composition (typed_pair typed_second (typed_constant 1)) typed_add)
    (4*X+5)
    (show (4*X+5 : Polynomial ℕ).natDegree≤1 by simpa using degree_affine 4 5)
    (by omega) (by omega)
  intro as n pre post he
  have hf : pre.foldl (fun z (_ : A)=>z+1) n=n+pre.length := by
    clear he
    induction pre generalizing n with
    | nil => simp
    | cons a pre ih => simp only [List.foldl_cons,ih,List.length_cons]; omega
  change weight (pre.foldl (fun z (_ : A)=>z+1) n)≤_
  rw [hf]
  have h:=weight_nat_le (n+pre.length)
  have hs:=nat_size_add n pre.length
  have hl : pre.length.size≤pre.length := Nat.size_le.mpr Nat.lt_two_pow_self
  have hn:=size_le_weight n
  have hp:pre.length≤weight as := (list_length_le_weight pre).trans (weight_prefix he)
  have hm : max n.size pre.length.size≤weight as+weight n := max_le (by omega) (by omega)
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  omega

lemma typed_listSum_seed : Typed listSum 3 := by
  unfold listSum
  apply typed_congr
  apply typed_composition (e := 1) (t := 3) (typed_pair typed_identity (typed_constant 0))
  apply typed_fold (s := 2) typed_add (4*X+4*X*(X+1)+1)
  · have h1 : (X : Polynomial ℕ).natDegree≤1 := by simp
    have h2 : (X+1 : Polynomial ℕ).natDegree≤1 := by simpa using degree_affine 1 1
    have hm := degree_mul (degree_scale 4 h1) h2
    have hs := degree_add (degree_scale 4 h1) hm
    simpa using degree_add hs (show (1 : Polynomial ℕ).natDegree≤0 by simp)
  · omega
  · omega
  · intro as z pre post he
    let S:=weight (as,z)
    have hp : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans
      (by dsimp [S]; rw [weight_prod]; omega))
    have ha : ∀ a∈pre,a.size≤S := by
      intro a ha
      exact (size_le_weight a).trans ((weight_mem (as:=as) (by simp [he,ha])).trans
        (by dsimp [S]; rw [weight_prod]; omega))
    have hz : z.size≤S := (size_le_weight z).trans (by dsimp [S]; rw [weight_prod]; omega)
    have hb := nat_fold_size_bound (fun x : ℕ×ℕ=>x.1+x.2) 1 S
      (fun a b=>(nat_size_add a b).trans (by omega)) pre z ha
    have hw:=weight_nat_le (pre.foldl (fun z a=>a+z) z)
    have hm:=Nat.mul_le_mul_right (S+1) hp
    simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
    change _≤4*S+4*S*(S+1)+1
    nlinarith

lemma typed_digits_seed : Typed digits 1 := by
  refine ⟨X+1, by simpa using degree_affine 1 1, ?_⟩
  intro a
  change 1+weight a≤_
  simp only [eval_add,eval_X,eval_one]
  omega

lemma typed_bitSize_seed : Typed bitSize 2 := by
  unfold bitSize
  apply typed_congr
  exact typed_composition typed_digits_seed typed_listLength_seed

lemma typed_ceilLogTwo_seed : Typed ceilLogTwoRealizer 2 := by
  unfold ceilLogTwoRealizer
  apply typed_congr
  exact typed_composition typed_predecessor_seed typed_bitSize_seed

end
end Math115.WordCountSeedDegrees
