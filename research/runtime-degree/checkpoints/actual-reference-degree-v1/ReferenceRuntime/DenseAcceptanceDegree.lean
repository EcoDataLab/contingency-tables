import ReferenceRuntime.DenseWidthCoreDegree
import UnitRuntime.WordChoiceDegree
import UnitRuntime.ExchangeDegree

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds DensePrograms ProfilePrograms
set_option maxHeartbeats 1200000
noncomputable section

lemma typed_bitDenominator : Typed bitDenominatorRealizer 2 := by
  unfold bitDenominatorRealizer
  apply typed_congr
  apply typed_composition (e:=1) (t:=2) (typed_pair typed_identity (typed_constant 1))
  apply typed_fold (e:=1) (s:=1) (typed_composition typed_second typed_double)
    (12*X+1) (by simpa using degree_affine 12 1) (by decide) (by decide)
  intro bs n pre post he
  have hfold : ∀ z, (pre.foldl (fun a (_ : Bool) => 2*a) z).size ≤ z.size+pre.length*2 := by
    clear he
    induction pre with
    | nil => intro z; simp
    | cons b pre ih =>
      intro z
      have hh := nat_size_mul 2 z
      have ht := ih (2*z)
      have h2 : Nat.size 2 = 2 := by decide
      simp only [List.foldl_cons,List.length_cons]
      omega
  let S := weight (bs,n)
  have hn : n.size ≤ S := (size_le_weight n).trans (weight_snd (bs,n))
  have hp : pre.length ≤ S := (list_length_le_weight pre).trans ((weight_prefix he).trans (weight_fst (bs,n)))
  have hw := weight_nat_le (pre.foldl (fun a (_ : Bool) => 2*a) n)
  have hh := hfold n
  simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
  change weight (pre.foldl (fun a (_ : Bool) => 2*a) n) ≤ 12*S+1
  omega

/-- The exponent gap cannot request expansion beyond the actual supplied word:
the original program builds its denominator from a bounded word prefix. -/
theorem typed_dyadicWordAccept : Typed dyadicWordAcceptRealizer 32 := by
  unfold dyadicWordAcceptRealizer
  apply typed_congr
  exact typed_composition
    (typed_pair (typed_composition typed_first Math115.UnitRuntimeNext.typed_bitValue)
      (typed_composition
        (typed_composition
          (typed_pair typed_first
            (typed_composition
              (typed_pair (typed_composition typed_first Math115.WordCountSeedDegrees.typed_listLength_seed) typed_second)
              Math115.DivisionRuntimeNext.typed_subtract_actual)) Math115.ListRepeatDegreeV1.typed_takeFast)
        typed_bitDenominator)) Math115.DivisionRuntimeNext.typed_less_actual

lemma typed_axisListStep : Typed axisListStepRealizer 84 := by
  have hK : Typed (composition (composition (first (A:=(ℕ×List ℕ)×ℕ) (B:=Bool)) first) first) 1 :=
    typed_composition (typed_composition typed_first typed_first) typed_first
  have hX : Typed (composition (composition (first (A:=(ℕ×List ℕ)×ℕ) (B:=Bool)) first) second) 1 :=
    typed_composition (typed_composition typed_first typed_first) typed_second
  have hI : Typed (composition (first (A:=(ℕ×List ℕ)×ℕ) (B:=Bool)) second) 1 :=
    typed_composition typed_first typed_second
  have hL := typed_composition hX Math115.WordCountSeedDegrees.typed_listLength_seed
  have hV := typed_composition (typed_pair hX hI) (Math115.DrawRuntimeNext.typed_getDFast 0)
  have hup := typed_composition
    (typed_composition (typed_pair hX (typed_pair hI hL)) Math115.UnitRuntimeNext.typed_listExchange) typed_some
  have hdown := typed_composition
    (typed_composition (typed_pair hX (typed_pair hL hI)) Math115.UnitRuntimeNext.typed_listExchange) typed_some
  unfold axisListStepRealizer
  exact typed_congr _ (typed_choose
    (typed_composition (typed_pair hI hL) Math115.DivisionRuntimeNext.typed_less_actual)
    (typed_choose typed_second
      (typed_choose
        (typed_composition (typed_pair (typed_composition hV typed_successor) hK)
          Math115.DivisionRuntimeNext.typed_less_actual) hup (typed_constant none))
      (typed_choose
        (typed_composition (typed_pair (typed_constant 0) hV) Math115.DivisionRuntimeNext.typed_less_actual)
        hdown (typed_constant none))) (typed_constant none))

lemma typed_denseRemainder : Typed remainder 4 := by
  unfold remainder
  exact typed_composition Math115.DivisionRuntimeNext.typed_division typed_second

/-- Exact coordinate/side decoding and bounded proposal, including invalid
indices, boundary rejection, empty coordinate lists and arbitrary bit words. -/
theorem typed_axisWordStep : Typed axisWordStepRealizer 2016 := by
  unfold axisWordStepRealizer
  exact typed_composition
    (typed_pair
      (typed_pair typed_first
        (typed_composition
          (typed_pair (typed_composition typed_second Math115.UnitRuntimeNext.typed_bitValue) (typed_constant 2))
          Math115.DivisionRuntimeNext.typed_quotient))
      (typed_composition
        (typed_pair
          (typed_composition
            (typed_pair (typed_composition typed_second Math115.UnitRuntimeNext.typed_bitValue) (typed_constant 2))
            typed_denseRemainder) (typed_constant 1)) Math115.ListRepeatDegreeV1.typed_natEqual)) typed_axisListStep

#check typed_dyadicWordAccept
#print axioms typed_dyadicWordAccept
#check typed_axisWordStep
#print axioms typed_axisWordStep
end
end Math115.ReferenceRuntimeNext
