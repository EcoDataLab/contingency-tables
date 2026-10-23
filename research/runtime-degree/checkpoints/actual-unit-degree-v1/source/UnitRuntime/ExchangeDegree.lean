/- Numerical certificates for exact pinned unit-neighbor helpers.
All literal inputs, realizer costs and encoded output weights are charged. -/
import RetryRuntime.MapWithDegree
import ResearchBounds.DrawControlDegree
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileExchangeProgram

namespace Math115.UnitRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open ProfilePrograms Math115.DegreeBounds
open Math115.RetryRuntimeNext Math115.PrinterRuntimeNext
noncomputable section

lemma typed_exchangeEntry : Typed exchangeEntryRealizer 2 := by
  have hV : Typed (composition (first (A:=ExchangeInput) (B:=ℕ)) first) 1 :=
    typed_composition typed_first typed_first
  have hI : Typed (composition (composition (first (A:=ExchangeInput) (B:=ℕ)) second) first) 1 :=
    typed_composition (typed_composition typed_first typed_second) typed_first
  have hJ : Typed (composition (composition (first (A:=ExchangeInput) (B:=ℕ)) second) second) 1 :=
    typed_composition (typed_composition typed_first typed_second) typed_second
  have hi : Typed (choose (composition (pair (second (A:=ExchangeInput) (B:=ℕ))
      (composition (composition first second) first)) natEqual) (constant 1) (constant 0)) 1 := by
    exact Math115.DrawDegree.typed_choose
      (typed_composition (typed_pair typed_second hI) Math115.RetryRuntimeNext.typed_natEqual)
      (typed_constant 1) (typed_constant 0)
  have hj : Typed (choose (composition (pair (second (A:=ExchangeInput) (B:=ℕ))
      (composition (composition first second) second)) natEqual) (constant 1) (constant 0)) 1 := by
    exact Math115.DrawDegree.typed_choose
      (typed_composition (typed_pair typed_second hJ) Math115.RetryRuntimeNext.typed_natEqual)
      (typed_constant 1) (typed_constant 0)
  unfold exchangeEntryRealizer
  apply typed_congr
  exact typed_composition
    (typed_pair (typed_composition
      (typed_pair (typed_composition (typed_pair hV typed_second)
        (Math115.RetryRuntimeNext.typed_getDFast 0)) hi) typed_add) hj)
    Math115.RetryRuntimeNext.typed_subtract_seed

/-- Actual directed coordinate update visits the supplied profile exactly once.
Coordinate integers may be arbitrary and need not lie in the profile. -/
theorem typed_listExchange : Typed listExchangeRealizer 42 := by
  have hr : Typed (composition (composition (first (A:=List ℕ) (B:=ℕ×ℕ)) listLength) range) 3 := by
    apply Math115.RetryRuntimeNext.typed_boundedRange (d:=1)
      (typed_composition typed_first Math115.RetryRuntimeNext.typed_listLength_seed) X (by simp)
    intro z
    simp only [Function.comp_apply,eval_X]
    exact (list_length_le_weight z.1).trans (weight_fst z)
  unfold listExchangeRealizer
  exact typed_composition (typed_pair typed_identity hr)
    (Math115.RetryRuntimeNext.typed_mapWith typed_exchangeEntry (by decide))


/-- A literal coordinate update preserves polynomial binary output size even
with unrelated or out-of-range coordinate indices. -/
lemma listExchange_output_weight (z : ExchangeInput) :
    weight (listExchange z) ≤ 4*(weight z)^2+10*weight z+1 := by
  let S := weight z
  have hlen : z.1.length≤S := (list_length_le_weight z.1).trans (weight_fst z)
  have hitem : ∀ a∈List.range z.1.length, weight (exchangeEntry (z,a))≤4*S+9 := by
    intro a ha
    have hi : a<z.1.length := List.mem_range.mp ha
    have hget : z.1.getD a 0=z.1[a] := by
      simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
    have hm : z.1[a]∈z.1 := List.mem_iff_getElem.mpr ⟨a,hi,rfl⟩
    have hw : weight (z.1.getD a 0)≤S := by
      rw [hget]
      exact (weight_mem hm).trans (weight_fst z)
    have hentry : exchangeEntry (z,a)≤z.1.getD a 0+1 := by
      change z.1.getD a 0+(if a=z.2.1 then 1 else 0)-(if a=z.2.2 then 1 else 0)≤z.1.getD a 0+1
      split_ifs <;> omega
    have hn : (z.1.getD a 0).size≤S := (size_le_weight _).trans hw
    have hsize := Nat.size_le_size hentry
    have hadd := nat_size_add (z.1.getD a 0) 1
    have hone : Nat.size 1=1 := by decide
    have hmax : max (z.1.getD a 0).size (Nat.size 1)≤S+1 := by
      rw [hone]
      exact max_le (by omega) (by omega)
    have hout := weight_nat_le (exchangeEntry (z,a))
    omega
  have hmap := weight_map_bound (as:=List.range z.1.length)
    (f:=fun a=>exchangeEntry (z,a)) hitem
  simp only [List.length_range] at hmap
  change weight ((List.range z.1.length).map (fun a=>exchangeEntry (z,a)))≤_ at ⊢
  change _≤4*S^2+10*S+1
  nlinarith [Nat.mul_le_mul_right (4*S+10) hlen]

end
end Math115.UnitRuntimeNext
