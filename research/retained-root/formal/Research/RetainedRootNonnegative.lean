import Research.RetainedRootPhysical

namespace OAI.ContingencyTables.IntegerWeightedTransport

open scoped BigOperators Classical Topology
open FactorialSignatures BalancedFamily BalancedBox BalancedEnumeration IntegerMarginal Filter

lemma retainedRootCoefficient_tendsto {K : Type*} {l : Filter K}
    (B : K → Matrix Bool Bool ℝ) (A : Matrix Bool Bool ℝ) (s t : K → ℝ) (a b : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hB : ∀ i j, Tendsto (fun k => B k i j) l (nhds (A i j)))
    (hs : Tendsto s l (nhds a)) (ht : Tendsto t l (nhds b)) :
    Tendsto (fun k => retainedRootCoefficient (B k) (s k) (t k)) l
      (nhds (retainedRootCoefficient A a b)) := by
  have h1 : Tendsto (fun _ : K => (1:ℝ)) l (nhds 1) := tendsto_const_nhds
  exact ((((h1.div hs ha).add (h1.div ht hb)).sub
    ((hB false false).div (hs.pow 2) (pow_ne_zero 2 ha))).add
    (((hB false true).const_mul 2).div (hs.mul ht) (mul_ne_zero ha hb))).sub
    ((hB true true).div (ht.pow 2) (pow_ne_zero 2 hb))

/-- Hard-zero weights preserve nonnegativity of the retained root coefficient
under exactly the same finite approximation hypotheses as local transport. -/
theorem retainedRootCoefficient_nonnegative_limit {K : Type*} {l : Filter K}
    [l.NeBot] (Ms : List ℕ)
    (F : K → (Coordinates Bool Ms → ℕ) → ℝ) (f : (Coordinates Bool Ms → ℕ) → ℝ)
    (hlim : ∀ x, Tendsto (fun t => F t x) l (nhds (f x)))
    (m z : Bool → ℕ) (R : ℕ) (hlower : ∀ U ∈ Ms, 2 ≤ U)
    (hsoft : ∀ᶠ t in l, (∀ x, 0 ≤ F t x) ∧
      PositiveSlice (F t) (bounds m Ms) (R+Ms.sum) ∧
      RemovalSlice (F t) (bounds m Ms) (R+Ms.sum))
    (hz : InBox m z) (htotal : (∑ i, z i)=R+1)
    (hs : 0 < oneHole (eliminate Ms f) z false)
    (ht : 0 < oneHole (eliminate Ms f) z true) :
    0 ≤ retainedRootCoefficient (integerRemovalMatrix (correctionKernel Ms f) z)
      (oneHole (eliminate Ms f) z false) (oneHole (eliminate Ms f) z true) := by
  have hmarg := eliminate_tendsto Ms F f hlim
  have hsm := oneHole_tendsto _ _ hmarg z false
  have htm := oneHole_tendsto _ _ hmarg z true
  have hB (i j : Bool) := removal_tendsto _ _ (correctionKernel_tendsto Ms F f hlim) z i j
  have hc := retainedRootCoefficient_tendsto _ _ _ _ _ _ (ne_of_gt hs) (ne_of_gt ht)
    hB hsm htm
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hc
  have hspos : ∀ᶠ t in l, 0 < oneHole (eliminate Ms (F t)) z false :=
    hsm.eventually (lt_mem_nhds hs)
  have htpos : ∀ᶠ t in l, 0 < oneHole (eliminate Ms (F t)) z true :=
    htm.eventually (lt_mem_nhds ht)
  filter_upwards [hsoft,hspos,htpos] with t hf hsp htp
  exact retainedRootCoefficient_nonnegative Ms (F t) m z R hlower
    hf.1 hf.2.1 hf.2.2 hz htotal hsp htp

end OAI.ContingencyTables.IntegerWeightedTransport

#print axioms OAI.ContingencyTables.IntegerWeightedTransport.retainedRootCoefficient_nonnegative_limit
