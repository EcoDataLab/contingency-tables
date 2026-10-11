/- PRIVATE SOURCE-ONLY CHECKPOINT12 CANDIDATE. NOT COMPILED.
   Exact pinned programs and codecs; charged execution plus output weight.
   Shared ListRepeatDegree is supplied by the count lane. -/
import ResearchBounds.WordCountSeedDegrees
import ResearchBounds.FreshBitDegreeBounds
import CountBounds.ListRepeatDegree
import OAI.Combinatorics.ContingencyTables.Sampling.SmallCellCatalogProgram

namespace Math115.CatalogueDegreeV1
open OAI OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds Math115.WordCountSeedDegrees Math115.ListRepeatDegreeV1

noncomputable section

lemma typed_digitValue : Typed digitValue 1 := by
  unfold digitValue
  apply typed_congr
  exact typed_choose typed_identity (typed_constant 1) (typed_constant 0)

lemma typed_divStep : Typed divStepRealizer 1 := by
  unfold divStepRealizer
  apply typed_congr
  apply typed_pair (e:=1) (t:=1)
    (typed_composition typed_second typed_first)
  apply typed_choose (e:=1) (t:=1) (u:=1)
  · apply typed_composition (e:=1) _ typed_less
    apply typed_pair (e:=1) (t:=1)
    · apply typed_composition (e:=1) _ typed_add
      exact typed_pair
        (typed_composition (typed_composition (typed_composition typed_second typed_second) typed_second) typed_double)
        (typed_composition typed_first typed_digitValue)
    · exact typed_composition typed_second typed_first
  · apply typed_pair (e:=1) (t:=1)
    · exact typed_composition
        (typed_composition (typed_composition typed_second typed_second) typed_first) typed_double
    · apply typed_composition (e:=1) _ typed_add
      exact typed_pair
        (typed_composition (typed_composition (typed_composition typed_second typed_second) typed_second) typed_double)
        (typed_composition typed_first typed_digitValue)
  · apply typed_pair (e:=1) (t:=1)
    · apply typed_composition (e:=1) _ typed_add
      exact typed_pair
        (typed_composition (typed_composition (typed_composition typed_second typed_second) typed_first) typed_double)
        (typed_constant 1)
    · apply typed_composition (e:=1) _ typed_subtract_seed
      apply typed_pair (e:=1) (t:=1)
      · apply typed_composition (e:=1) _ typed_add
        exact typed_pair
          (typed_composition (typed_composition (typed_composition typed_second typed_second) typed_second) typed_double)
          (typed_composition typed_first typed_digitValue)
      · exact typed_composition typed_second typed_first

lemma typed_divFold : Typed (fold divStepRealizer) 2 := by
  apply typed_fold (s:=1) typed_divStep (40*X+10)
    (show (40*X+10 : Polynomial ℕ).natDegree≤1 by simpa using degree_affine 40 10)
    (by omega) (by omega)
  rintro bs ⟨n,q,r⟩ pre post he
  let S:=weight (bs,(n,q,r))
  have hpre : pre.length≤S := (list_length_le_weight pre).trans ((weight_prefix he).trans
    (by dsimp [S]; simp only [weight_prod]; omega))
  have hq : q.size≤S := by have h:=size_le_weight q; dsimp [S]; simp only [weight_prod]; omega
  have hr : r.size≤S := by have h:=size_le_weight r; dsimp [S]; simp only [weight_prod]; omega
  have hn : weight n≤S := by dsimp [S]; simp only [weight_prod]; omega
  have hs:=divFold_sizes pre n q r
  have hqo:=weight_nat_le (pre.foldl (fun z b=>divStep (b,z)) (n,q,r)).2.1
  have hro:=weight_nat_le (pre.foldl (fun z b=>divStep (b,z)) (n,q,r)).2.2
  have hf:=divFold_first pre n q r
  rw [←Prod.eta (pre.foldl (fun z b=>divStep (b,z)) (n,q,r)),weight_prod,hf,
    ←Prod.eta (pre.foldl (fun z b=>divStep (b,z)) (n,q,r)).2,weight_prod]
  simp only [eval_add,eval_mul,eval_ofNat,eval_X]
  change _≤40*S+10
  omega

lemma typed_divCore : Typed divCore 4 := by
  unfold divCore
  apply typed_composition (e:=4) _ typed_second
  apply typed_composition (e:=2) _ typed_divFold
  exact typed_pair
    (typed_composition (typed_composition typed_first typed_toBits) typed_reverse)
    (typed_pair typed_second (typed_pair (typed_constant 0) (typed_constant 0)))

theorem typed_division : Typed division 4 := by
  unfold division
  apply typed_congr
  exact typed_choose
    (typed_composition (typed_pair (typed_constant 0) typed_second) typed_less)
    typed_divCore (typed_pair (typed_constant 0) typed_first)

theorem typed_quotient : Typed quotient 4 := by
  unfold quotient
  exact typed_composition typed_division typed_first

theorem typed_remainder : Typed remainder 4 := by
  unfold remainder
  exact typed_composition typed_division typed_second

theorem typed_getDFast {A : Type} [Codec A] (d : A) : Typed (getDFast d) 2 := by
  unfold getDFast
  apply typed_congr
  exact typed_composition typed_dropFast (typed_head d)

/-- Reuse the already compiled certificate for the identical pinned numeric
    range program; a binary-input-weight bound for range alone would be false. -/
theorem bounded_range_numeric : Bounded range id 3 :=
  Math115.DegreeBounds.range_numeric_degree

end
end Math115.CatalogueDegreeV1
