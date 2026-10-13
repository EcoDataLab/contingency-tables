/- Exact exchange enumeration with semantic output-size composition.
No alternate execution program or unproved work assumption is used. -/
import UnitRuntime.NeighborHelpers

namespace Math115.UnitRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open ProfilePrograms Math115.DegreeBounds Math115.ScalarOutputDegree
open Math115.RetryRuntimeNext Math115.PrinterRuntimeNext
noncomputable section

lemma flattenViews_output_weight (v : List ℕ×List ℕ) :
    weight (flattenViews v)≤weight v := by
  have h := weight_append v.1 v.2
  unfold flattenViews
  rw [weight_prod]
  omega

lemma exchangeInput_output_weight (z : (List ℕ×List ℕ)×(ℕ×ℕ)) :
    weight (flattenViews z.1,z.2)≤weight z := by
  have h := flattenViews_output_weight z.1
  rw [weight_prod,weight_prod]
  omega

lemma typed_codeExchange_refined : Typed codeExchangeRealizer 42 := by
  have hinput : Typed (pair
      (composition (first (A:=List ℕ×List ℕ) (B:=ℕ×ℕ)) flattenViewsRealizer) second) 2 :=
    typed_pair (typed_composition typed_first typed_flattenViews) typed_second
  have hlist : Typed (composition (pair (composition first flattenViewsRealizer) second)
      listExchangeRealizer) 42 := by
    exact typed_composition_from_output_size (s:=1) hinput typed_listExchange X (by simp)
      (fun z=>by simpa only [Function.comp_apply,eval_X] using exchangeInput_output_weight z)
  have hprep : Typed (pair
      (composition (composition (first (A:=List ℕ×List ℕ) (B:=ℕ×ℕ)) first) listLength)
      (composition (pair (composition first flattenViewsRealizer) second) listExchangeRealizer)) 42 :=
    typed_pair (typed_composition (typed_composition typed_first typed_first)
      Math115.RetryRuntimeNext.typed_listLength_seed) hlist
  unfold codeExchangeRealizer
  apply typed_composition_from_output_size (s:=2) hprep typed_splitViews (4*X^2+14*X+3)
  · have h2 : (4*X^2 : Polynomial ℕ).natDegree≤2 := by
      simpa using degree_scale 4 (show (X^2 : Polynomial ℕ).natDegree≤2 by simp)
    have h1 : (14*X : Polynomial ℕ).natDegree≤1 := by
      simpa using degree_scale 14 (show (X : Polynomial ℕ).natDegree≤1 by simp)
    exact (degree_add (degree_add h2 h1) (show (3 : Polynomial ℕ).natDegree≤0 by simp)).trans (by decide)
  · intro z
    have hinput := exchangeInput_output_weight z
    have hout := listExchange_output_weight (flattenViews z.1,z.2)
    have hlength : z.1.1.length≤weight z :=
      (list_length_le_weight z.1.1).trans ((weight_fst z.1).trans (weight_fst z))
    have hwlength := Math115.RetryRuntimeNext.weight_nat_numeric z.1.1.length
    have hlarge : weight (listExchange (flattenViews z.1,z.2))≤4*(weight z)^2+10*weight z+1 := by
      apply hout.trans
      gcongr <;> exact hinput
    simp only [Function.comp_apply,eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,weight_prod]
    omega

private def pairsEnvelope : Polynomial ℕ := 8*(1+2*X)^3+4*(1+2*X)^2+X+2
private lemma pairsEnvelope_degree : pairsEnvelope.natDegree≤3 := by
  have hbase : (1+2*X : Polynomial ℕ).natDegree≤1 := by simpa [add_comm] using degree_affine 2 1
  have h3 : (8*(1+2*X)^3 : Polynomial ℕ).natDegree≤3 := by
    simpa using degree_scale 8 (natDegree_pow_le_of_le 3 hbase)
  have h2 : (4*(1+2*X)^2 : Polynomial ℕ).natDegree≤2 := by
    simpa using degree_scale 4 (natDegree_pow_le_of_le 2 hbase)
  unfold pairsEnvelope
  exact (degree_add (degree_add (degree_add h3 h2)
    (show (X : Polynomial ℕ).natDegree≤1 by simp)) (show (2 : Polynomial ℕ).natDegree≤0 by simp)).trans (by decide)

private lemma pairsEnvelope_output (xs : List ℕ) :
    weight (xs,cellPairs (xs,xs))≤pairsEnvelope.eval (weight xs) := by
  have hcell := Math115.CatalogueDegreeV1.weight_cellPairs_output (xs,xs)
  simp only [weight_prod] at hcell ⊢
  simp only [pairsEnvelope,eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
  nlinarith

lemma typed_positiveExchangeIndices_refined : Typed positiveExchangeIndicesRealizer 1008 := by
  have hprep : Typed (pair (identity (A:=List ℕ))
      (composition (pair identity identity) cellPairsRealizer)) 504 :=
    typed_pair typed_identity
      (typed_composition (typed_pair typed_identity typed_identity) Math115.CatalogueDegreeV1.typed_cellPairs)
  unfold positiveExchangeIndicesRealizer
  exact typed_composition_from_output_size (s:=3) hprep
    (Math115.DrawDegree.typed_filterWith typed_positiveExchangeTest (by decide))
    pairsEnvelope pairsEnvelope_degree (by
      intro xs
      simpa only [Function.comp_apply,id_eq] using pairsEnvelope_output xs)

private lemma positiveExchangeIndices_output (xs : List ℕ) :
    weight (positiveExchangeIndices xs)≤pairsEnvelope.eval (weight xs) := by
  have hsub : (positiveExchangeIndices xs).Sublist (cellPairs (xs,xs)) := List.filter_sublist
  exact (weight_sublist hsub).trans
    ((weight_snd (xs,cellPairs (xs,xs))).trans (pairsEnvelope_output xs))

/-- The exact exchange branch has a numerical degree bound of 10842.
The independent size polynomial charges the list of all coordinate pairs and
all constructed output views; arbitrary malformed views are still covered. -/
theorem typed_codeExchangeList_refined : Typed codeExchangeListRealizer 10842 := by
  have hindices : Typed (composition flattenViewsRealizer positiveExchangeIndicesRealizer) 1008 :=
    typed_composition_from_output_size (s:=1) typed_flattenViews typed_positiveExchangeIndices_refined
      X (by simp) (fun v=>by simpa only [eval_X] using flattenViews_output_weight v)
  have hprep : Typed (pair (identity (A:=List ℕ×List ℕ))
      (composition flattenViewsRealizer positiveExchangeIndicesRealizer)) 1008 :=
    typed_pair typed_identity hindices
  unfold codeExchangeListRealizer
  apply typed_composition_from_output_size (s:=3) hprep
    (Math115.RetryRuntimeNext.typed_mapWith typed_codeExchange_refined (by decide))
    (pairsEnvelope+X+1)
  · exact (degree_add (degree_add pairsEnvelope_degree
      (show (X : Polynomial ℕ).natDegree≤1 by simp)) (show (1 : Polynomial ℕ).natDegree≤0 by simp)).trans (by decide)
  · intro v
    have houtput := positiveExchangeIndices_output (flattenViews v)
    have hmono := polynomial_eval_monotone pairsEnvelope (flattenViews_output_weight v)
    simp only [Function.comp_apply,id_eq,weight_prod,eval_add,eval_X,eval_one]
    omega

end
end Math115.UnitRuntimeNext
