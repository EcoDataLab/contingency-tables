import InitialRuntime.GreedyDegree
import OAI.Combinatorics.MatchingCount.Complexity.TreeChoiceCosts
namespace Math115.RetryRuntimeNext
open OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds
noncomputable section
lemma typed_subtract_seed : Typed subtract 1 := Math115.InitialRuntimeNext.typed_subtract_actual
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

end
end Math115.RetryRuntimeNext
