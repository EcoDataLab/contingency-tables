import ResearchBounds.TreeArithmeticDegree
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialDivision
import OAI.Combinatorics.MatchingCount.Machines.TreeNaturalComb

namespace Math115.DivisionRuntimeNext
open OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds

-- The two exact arithmetic seeds are relocated verbatim from GreedyDegree
-- to avoid importing the unrelated greedy table program and its closure.
lemma typed_less_actual : Typed less 1 := by
  refine ⟨10*X+40,by simpa using degree_affine 10 40,fun ⟨a,b⟩ => ?_⟩
  have ha := size_le_weight a
  have hb := size_le_weight b
  have ho := weight_bool (decide (a < b))
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  change 2*weight a+3*(a.bits.length+b.bits.length)+31+weight (decide (a < b)) ≤ _
  rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len]
  omega

lemma typed_subtract_actual : Typed subtract 1 := by
  refine ⟨50*X+100,by simpa using degree_affine 50 100,fun ⟨a,b⟩ => ?_⟩
  have ha := size_le_weight a
  have hb := size_le_weight b
  have hc := weight_nat_small (Nat.sub_le a b)
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,weight_prod]
  change (2*weight a+3*(a.bits.length+b.bits.length)+31)+
    (if decide (a < b) then weight (a,b)+2 else
      2*weight a+9*(a.bits.length+b.bits.length)+4*weight (a-b)+32)+
      7*weight (a,b)+18+weight (a-b) ≤ _
  rw [Nat.size_eq_bits_len,Nat.size_eq_bits_len,weight_prod]
  split <;> omega

lemma typed_digitValue : Typed TreeTyped.digitValue 1 := by
  unfold TreeTyped.digitValue
  apply typed_congr
  exact typed_choose typed_identity (typed_constant 1) (typed_constant 0)

lemma typed_divStep : Typed TreeTyped.divStepRealizer 1 := by
  unfold TreeTyped.divStepRealizer
  apply typed_congr
  apply typed_pair (e:=1) (t:=1) (typed_composition typed_second typed_first)
  apply typed_choose (e:=1) (t:=1) (u:=1)
  · apply typed_composition (e:=1) (t:=1) _ typed_less_actual
    apply typed_pair (e:=1) (t:=1)
    · apply typed_composition (e:=1) (t:=1) _ typed_add
      exact typed_pair
        (typed_composition (typed_composition (typed_composition typed_second typed_second) typed_second) typed_double)
        (typed_composition typed_first typed_digitValue)
    · exact typed_composition typed_second typed_first
  · apply typed_pair (e:=1) (t:=1)
    · exact typed_composition (typed_composition (typed_composition typed_second typed_second) typed_first) typed_double
    · apply typed_composition (e:=1) (t:=1) _ typed_add
      exact typed_pair
        (typed_composition (typed_composition (typed_composition typed_second typed_second) typed_second) typed_double)
        (typed_composition typed_first typed_digitValue)
  · apply typed_pair (e:=1) (t:=1)
    · apply typed_composition (e:=1) (t:=1) _ typed_add
      exact typed_pair
        (typed_composition (typed_composition (typed_composition typed_second typed_second) typed_first) typed_double)
        (typed_constant 1)
    · apply typed_composition (e:=1) (t:=1) _ typed_subtract_actual
      apply typed_pair (e:=1) (t:=1)
      · apply typed_composition (e:=1) (t:=1) _ typed_add
        exact typed_pair
          (typed_composition (typed_composition (typed_composition typed_second typed_second) typed_second) typed_double)
          (typed_composition typed_first typed_digitValue)
      · exact typed_composition typed_second typed_first

/-- The exact binary-division fold has a linear encoding envelope even on
arbitrary starting divisor, quotient and remainder, including divisor zero. -/
lemma divFold_intermediate (bs : List Bool) (n q r : ℕ) (pre post : List Bool)
    (he : bs = pre ++ post) :
    weight (pre.foldl (fun z b => TreeTyped.divStep (b,z)) (n,q,r)) ≤
      (40*X+10 : Polynomial ℕ).eval (weight (bs,(n,q,r))) := by
  let S := weight (bs,(n,q,r))
  have hpre : pre.length ≤ S := (list_length_le_weight pre).trans
    ((weight_prefix he).trans (by dsimp [S]; simp only [weight_prod]; omega))
  have hq : q.size ≤ S := by have h := size_le_weight q; dsimp [S]; simp only [weight_prod]; omega
  have hr : r.size ≤ S := by have h := size_le_weight r; dsimp [S]; simp only [weight_prod]; omega
  have hn : weight n ≤ S := by dsimp [S]; simp only [weight_prod]; omega
  have hs := TreeTyped.divFold_sizes pre n q r
  have hqo := weight_nat_le (pre.foldl (fun z b => TreeTyped.divStep (b,z)) (n,q,r)).2.1
  have hro := weight_nat_le (pre.foldl (fun z b => TreeTyped.divStep (b,z)) (n,q,r)).2.2
  have hf := TreeTyped.divFold_first pre n q r
  rw [←Prod.eta (pre.foldl (fun z b => TreeTyped.divStep (b,z)) (n,q,r)),weight_prod,hf,
    ←Prod.eta (pre.foldl (fun z b => TreeTyped.divStep (b,z)) (n,q,r)).2,weight_prod]
  simp only [eval_add,eval_mul,eval_ofNat,eval_X]
  change _ ≤ 40*S+10
  omega

lemma typed_divFold : Typed (TreeTyped.fold TreeTyped.divStepRealizer) 2 := by
  apply typed_fold (e:=1) (s:=1) typed_divStep (40*X+10)
    (by simpa using degree_affine 40 10) (by decide) (by decide)
  rintro bs ⟨n,q,r⟩ pre post he
  exact divFold_intermediate bs n q r pre post he

lemma typed_divCore : Typed TreeTyped.divCore 4 := by
  unfold TreeTyped.divCore
  apply typed_composition (e:=4) _ typed_second
  apply typed_composition (e:=2) _ typed_divFold
  exact typed_pair
    (typed_composition (typed_composition typed_first typed_toBits) typed_reverse)
    (typed_pair typed_second (typed_pair (typed_constant 0) (typed_constant 0)))

/-- Charged work plus encoded quotient and remainder of the pinned division
realizer have degree at most four for every natural pair, including divisor 0. -/
theorem typed_division : Typed TreeTyped.division 4 := by
  unfold TreeTyped.division
  apply typed_congr
  exact typed_choose
    (typed_composition (typed_pair (typed_constant 0) typed_second) typed_less_actual)
    typed_divCore (typed_pair (typed_constant 0) typed_first)

/-- The exact quotient projection retains the same degree-four envelope. -/
theorem typed_quotient : Typed TreeTyped.quotient 4 := by
  unfold TreeTyped.quotient
  exact typed_composition typed_division typed_first

end Math115.DivisionRuntimeNext
