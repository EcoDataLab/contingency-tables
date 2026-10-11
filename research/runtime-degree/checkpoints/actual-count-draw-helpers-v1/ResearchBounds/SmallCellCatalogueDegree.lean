/- PRIVATE SOURCE-ONLY CHECKPOINT12 CANDIDATE. NOT COMPILED.
   Numerical certificate for the literal smallCellCatalogRealizer. No changed
   program, codec or witness. Generic count/draw helper candidates are imports.
   The bound is conservative; no minimal runtime exponent is asserted. -/
import ResearchBounds.CatalogueLeafDegrees
import ResearchBounds.DrawControlDegree
import ResearchBounds.ScalarOutputSizeDegree

namespace Math115.CatalogueDegreeV1
open OAI OAI.ContingencyTables OAI.ContingencyTables.ProfilePrograms
open OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds Math115.WordCountSeedDegrees Math115.ListRepeatDegreeV1

noncomputable section

lemma typed_boundedRange {A : Type} [Codec A] {f : A→ℕ} {F : Realizer f}
    {e d : ℕ} (hF : Typed F e) (p : Polynomial ℕ) (hp : p.natDegree≤d)
    (hn : ∀ a,f a≤p.eval (weight a)) :
    Typed (composition F range) (max e (3*d)) := by
  obtain ⟨q,hq,hqb⟩ := hF
  obtain ⟨r,hr,hrb⟩ := bounded_range_numeric
  refine ⟨q+r.comp p,degree_add hq (degree_comp hr hp),fun a=>?_⟩
  have h1:=hqb a
  have h2:=hrb (f a)
  have h3:=polynomial_eval_monotone r (hn a)
  simp only [eval_add,eval_comp]
  change F.cost a+range.cost (f a)+weight (List.range (f a))≤_
  dsimp only [id] at h2
  dsimp only at h3
  omega

theorem typed_pairAt : Typed pairAtRealizer 4 := by
  unfold pairAtRealizer
  exact typed_composition (typed_pair typed_second typed_first)
    (typed_pair typed_quotient typed_remainder)

theorem typed_cellPairCodes : Typed cellPairCodes 12 := by
  unfold cellPairCodes
  apply typed_boundedRange (e:=12) (d:=2)
    (typed_composition
      (typed_pair (typed_composition typed_first typed_listLength_seed)
        (typed_composition typed_second typed_listLength_seed)) typed_multiply)
    (X^2) (by simp)
  intro z
  have hr : z.1.length≤weight z :=
    (list_length_le_weight z.1).trans (by rw [weight_prod]; omega)
  have hc : z.2.length≤weight z :=
    (list_length_le_weight z.2).trans (by rw [weight_prod]; omega)
  simpa only [Function.comp_apply,eval_pow,eval_mul,eval_X,pow_two]
    using Nat.mul_le_mul hr hc

theorem typed_cellPairs : Typed cellPairsRealizer 504 := by
  unfold cellPairsRealizer
  exact typed_composition
    (typed_pair (typed_composition typed_second typed_listLength_seed) typed_cellPairCodes)
    (Math115.DrawDegree.typed_mapWith typed_pairAt (by omega))

theorem typed_smallCellTest : Typed smallCellTestRealizer 2 := by
  unfold smallCellTestRealizer
  apply typed_congr
  apply typed_choose (e:=2) (t:=1) (u:=2)
  · apply typed_composition (e:=2) _ typed_less
    apply typed_pair (e:=2) (t:=1)
    · exact typed_composition
        (typed_pair
          (typed_composition (typed_composition typed_first typed_first) typed_first)
          (typed_composition typed_second typed_first))
        (typed_getDFast 0)
    · exact typed_composition typed_first typed_second
  · exact typed_constant true
  · apply typed_composition (e:=2) _ typed_less
    apply typed_pair (e:=2) (t:=1)
    · exact typed_composition
        (typed_pair
          (typed_composition (typed_composition typed_first typed_first) typed_second)
          (typed_composition typed_second typed_second))
        (typed_getDFast 0)
    · exact typed_composition typed_first typed_second

/-- Cell-pair indices are bounded by the numeric margin-list lengths. This
    semantic output-size estimate does not change the executable program. -/
lemma weight_cellPairs_output (z : List ℕ×List ℕ) :
    weight (cellPairs z) ≤ 8*(weight z)^3+4*(weight z)^2+1 := by
  let S:=weight z
  have hr : z.1.length≤S :=
    (list_length_le_weight z.1).trans (by dsimp [S]; rw [weight_prod]; omega)
  have hc : z.2.length≤S :=
    (list_length_le_weight z.2).trans (by dsimp [S]; rw [weight_prod]; omega)
  have hitem : ∀ a∈cellPairs z,weight a≤8*S+3 := by
    intro a ha
    have hmem := (mem_cellPairs z.1 z.2 a.1 a.2).mp
      (by simpa only [Prod.eta] using ha)
    have hwa:=weight_nat_numeric a.1
    have hwb:=weight_nat_numeric a.2
    rw [←Prod.eta a,weight_prod]
    omega
  have hw:=weight_map_bound (as:=cellPairs z) (f:=id) (N:=8*S+3) hitem
  simp only [List.map_id] at hw
  have hlen : (cellPairs z).length≤S^2 := by
    simpa only [cellPairs,List.length_map,List.length_range,pow_two]
      using Nat.mul_le_mul hr hc
  have hm:=Nat.mul_le_mul_right (8*S+4) hlen
  change weight (cellPairs z)≤8*S^3+4*S^2+1
  nlinarith

/-- Cost and output encoding weight of the literal upstream catalogue realizer.
    Source-only until the root's authenticated compiler and named audit accept it. -/
theorem typed_smallCellCatalog : Typed smallCellCatalogRealizer 1008 := by
  unfold smallCellCatalogRealizer
  apply Math115.ScalarOutputDegree.typed_composition_from_output_size
    (e:=504) (t:=336) (s:=3)
    (typed_pair typed_identity (typed_composition typed_first typed_cellPairs))
    (Math115.DrawDegree.typed_filterWith typed_smallCellTest (by omega))
    (8*X^3+4*X^2+X+2)
  · have h1 := degree_scale 8 (show (X^3 : Polynomial ℕ).natDegree≤3 by simp)
    have h2 := degree_scale 4 (show (X^2 : Polynomial ℕ).natDegree≤2 by simp)
    have h3 := degree_add (degree_add h1 h2) (show (X : Polynomial ℕ).natDegree≤1 by simp)
    simpa using degree_add h3 (show (2 : Polynomial ℕ).natDegree≤0 by simp)
  · intro z
    have hcell := weight_cellPairs_output z.1
    have hfirst : weight z.1≤weight z := OAI.MatchingFPRAS.TreeTyped.weight_fst z
    have hbig : weight (cellPairs z.1)≤8*(weight z)^3+4*(weight z)^2+1 := by
      apply hcell.trans
      gcongr <;> exact hfirst
    simp only [Function.comp_apply,id_eq,weight_prod,eval_add,eval_mul,eval_ofNat,
      eval_X,eval_pow]
    omega

end
end Math115.CatalogueDegreeV1
