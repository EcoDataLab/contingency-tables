/- Numerical certificates for exact pinned unit-neighbor helpers.
All literal inputs, realizer costs and encoded output weights are charged. -/
import RetryRuntime.MapWithDegree
import ResearchBounds.DrawControlDegree
import OAI.Combinatorics.ContingencyTables.Machines.ListWordProgram

namespace Math115.UnitRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open ProfilePrograms Math115.DegreeBounds
open Math115.RetryRuntimeNext Math115.PrinterRuntimeNext
noncomputable section

lemma typed_some {A : Type} [Codec A] [Inhabited A] : Typed (TreeTyped.some (A:=A)) 1 := by
  unfold TreeTyped.some
  apply Math115.DrawDegree.typed_recode
  exact typed_pair_same (typed_constant true) typed_identity (by decide)

lemma typed_bitValue : Typed bitValue 6 := by
  unfold bitValue
  apply typed_congr
  exact typed_composition
    (typed_composition
      (typed_pair Math115.DegreeBounds.typed_reverse (typed_constant (1,0)))
      typed_mulFold) typed_second

/-- Literal optional lookup scans the supplied list and charges the binary index.
Out-of-range indices return none, including on an empty list. -/
lemma typed_getOptionFast {A : Type} [Codec A] [Inhabited A] :
    Typed (getOptionFast (A:=A)) 2 := by
  unfold getOptionFast
  apply typed_congr
  exact typed_weaken (Math115.DrawDegree.typed_choose
    (typed_composition (typed_pair typed_second
      (typed_composition typed_first Math115.RetryRuntimeNext.typed_listLength_seed))
      Math115.RetryRuntimeNext.typed_less)
    (typed_composition (Math115.RetryRuntimeNext.typed_getDFast default) typed_some)
    (typed_constant none)) (by decide)

/-- Exact list-word decoder, including empty, short and surplus words. -/
theorem typed_listWordChoice {A : Type} [Codec A] [Inhabited A] :
    Typed (listWordChoiceRealizer (A:=A)) 12 := by
  unfold listWordChoiceRealizer
  exact typed_composition (typed_pair typed_first
    (typed_composition typed_second typed_bitValue)) typed_getOptionFast

/-- Optional results retain only a member of the supplied list or the fixed
codec default; decoding a huge binary index cannot produce a huge result. -/
lemma listWordChoice_output_weight {A : Type} [Codec A] [Inhabited A]
    (z : List A×List Bool) :
    weight (listWordChoice z) ≤ weight z.1 + weight (default : A) + 4 := by
  cases h : listWordChoice z with
  | none =>
    change weight (false, (default : A)) ≤ _
    rw [weight_prod]
    have hb := weight_bool false
    omega
  | some a =>
    have ha : a∈z.1 := by
      unfold listWordChoice at h
      obtain ⟨hi,ha⟩ := List.getElem?_eq_some_iff.mp h
      exact List.mem_iff_getElem.mpr ⟨_,hi,ha⟩
    have hw := weight_mem ha
    change weight (true,a) ≤ _
    rw [weight_prod]
    have hb := weight_bool true
    omega


end
end Math115.UnitRuntimeNext
