import PrinterRuntime.LinearCollections
import OAI.Combinatorics.ContingencyTables.Sampling.GreedyPublicProgram

namespace Math115.InitialRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds
noncomputable section

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

lemma typed_minimum_actual : Typed minimum 1 := by
  unfold minimum
  apply typed_congr
  exact typed_choose typed_less_actual typed_first typed_second

lemma typed_rowCell_actual : Typed GreedyFeasibleTable.rowCellRealizer 1 := by
  have hA : Typed (composition (second (A:=ℕ) (B:=GreedyFeasibleTable.RowAccumulator)) first) 1 :=
    typed_composition typed_second typed_first
  have hC : Typed (first (A:=ℕ) (B:=GreedyFeasibleTable.RowAccumulator)) 1 := typed_first
  have hQ := typed_composition (typed_pair hA hC) typed_minimum_actual
  have hX : Typed (composition (composition (second (A:=ℕ) (B:=GreedyFeasibleTable.RowAccumulator)) second) first) 1 :=
    typed_composition (typed_composition typed_second typed_second) typed_first
  have hY : Typed (composition (composition (second (A:=ℕ) (B:=GreedyFeasibleTable.RowAccumulator)) second) second) 1 :=
    typed_composition (typed_composition typed_second typed_second) typed_second
  unfold GreedyFeasibleTable.rowCellRealizer
  apply typed_congr
  exact (typed_pair
    (typed_composition (typed_pair hA hQ) typed_subtract_actual)
    (typed_pair (typed_composition (typed_pair hQ hX) typed_listCons_arithmetic)
      (typed_composition (typed_pair
        (typed_composition (typed_pair hC hQ) typed_subtract_actual) hY) typed_listCons_arithmetic)))

/-- Every literal row pass, including arbitrary accumulator contents, has a
linear intermediate encoding envelope. No sum feasibility premise is used. -/
lemma rowFold_intermediate (cs : List ℕ) (a : ℕ) (xs ys : List ℕ) (pre post : List ℕ)
    (he : cs=pre++post) :
    weight (pre.foldl (fun z c => GreedyFeasibleTable.rowCell (c,z)) (a,(xs,ys))) ≤
      (12*X+10 : Polynomial ℕ).eval (weight (cs,(a,(xs,ys)))) := by
  have ht := GreedyFeasibleTable.listSplitRow_bounds a pre
  have ha := weight_nat_small ht.1
  have hpre := weight_prefix he
  have hx := weight_append (GreedyFeasibleTable.listSplitRow a pre).2.1.reverse xs
  have hy := weight_append (GreedyFeasibleTable.listSplitRow a pre).2.2.reverse ys
  rw [weight_reverse] at hx hy
  rw [GreedyFeasibleTable.fold_rowCell]
  simp only [weight_prod,eval_add,eval_mul,eval_ofNat,eval_X]
  omega

lemma typed_rowFold_actual : Typed (fold GreedyFeasibleTable.rowCellRealizer) 2 := by
  apply typed_fold (e:=1) (s:=1) typed_rowCell_actual (12*X+10)
    (by simpa using degree_affine 12 10) (by decide) (by decide)
  rintro cs ⟨a,xs,ys⟩ pre post he
  exact rowFold_intermediate cs a xs ys pre post he

lemma typed_rowSplit_actual : Typed GreedyFeasibleTable.rowSplitRealizer 4 := by
  unfold GreedyFeasibleTable.rowSplitRealizer
  dsimp only
  apply typed_congr
  apply typed_composition (e:=2) (t:=2)
  · exact typed_composition
      (typed_pair typed_second (typed_pair typed_first (typed_constant ([],[])))) typed_rowFold_actual
  · exact typed_pair typed_first (typed_pair
      (typed_composition (typed_composition typed_second typed_first) typed_reverse)
      (typed_composition (typed_composition typed_second typed_second) typed_reverse))

lemma typed_tableRow_actual : Typed GreedyFeasibleTable.tableRowRealizer 4 := by
  have hrow : Typed (composition (pair (first (A:=ℕ) (B:=GreedyFeasibleTable.TableAccumulator))
      (composition second first)) GreedyFeasibleTable.rowSplitRealizer) 4 :=
    typed_composition (typed_pair typed_first (typed_composition typed_second typed_first)) typed_rowSplit_actual
  have hrows : Typed (composition (second (A:=ℕ) (B:=GreedyFeasibleTable.TableAccumulator)) second) 1 :=
    typed_composition typed_second typed_second
  unfold GreedyFeasibleTable.tableRowRealizer
  apply typed_congr
  exact (typed_pair
    (typed_composition (typed_composition hrow typed_second) typed_second)
    (typed_composition (typed_pair
      (typed_composition (typed_composition hrow typed_second) typed_first) hrows) typed_listCons_arithmetic))

lemma listLE_trans {as bs cs : List ℕ}
    (hab : List.Forall₂ (· ≤ ·) as bs) (hbc : List.Forall₂ (· ≤ ·) bs cs) :
    List.Forall₂ (· ≤ ·) as cs := by
  induction hab generalizing cs with
  | nil => cases hbc; exact .nil
  | cons hab htail ih =>
    cases hbc with
    | cons hbc hrest => exact .cons (hab.trans hbc) (ih hrest)

lemma weight_listLE {as bs : List ℕ} (h : List.Forall₂ (· ≤ ·) as bs) : weight as ≤ 4*weight bs := by
  induction h with
  | nil => simp
  | cons hab htail ih =>
    have hn := weight_nat_small hab
    simp only [weight_cons]
    omega

lemma tableFold_bounds (rs cs base : List ℕ) (rows : List (List ℕ))
    (hc : List.Forall₂ (· ≤ ·) cs base) :
    List.Forall₂ (· ≤ ·) (rs.foldl (fun z a => GreedyFeasibleTable.tableRow (a,z)) (cs,rows)).1 base ∧
    weight (rs.foldl (fun z a => GreedyFeasibleTable.tableRow (a,z)) (cs,rows)).2 ≤
      rs.length*(4*weight base+1)+weight rows := by
  induction rs generalizing cs rows with
  | nil => exact ⟨hc,by simp⟩
  | cons a rs ih =>
    have hr := GreedyFeasibleTable.listSplitRow_le a cs
    have hout := weight_listLE (listLE_trans hr.1 hc)
    have ht := ih (GreedyFeasibleTable.listSplitRow a cs).2.2
      ((GreedyFeasibleTable.listSplitRow a cs).2.1::rows) (listLE_trans hr.2 hc)
    refine ⟨ht.1,?_⟩
    change weight (rs.foldl (fun z a => GreedyFeasibleTable.tableRow (a,z))
      ((GreedyFeasibleTable.listSplitRow a cs).2.2,(GreedyFeasibleTable.listSplitRow a cs).2.1::rows)).2 ≤ _
    simp only [List.length_cons,weight_cons] at ht ⊢
    nlinarith [ht.2]

/-- Original dimension folds retain binary sizes of all produced cells.
The bound includes arbitrary preexisting rows and mismatched margin totals. -/
lemma tableFold_intermediate (rs cs : List ℕ) (rows : List (List ℕ)) (pre post : List ℕ)
    (he : rs=pre++post) :
    weight (pre.foldl (fun z a => GreedyFeasibleTable.tableRow (a,z)) (cs,rows)) ≤
      (12*(X+1)^2 : Polynomial ℕ).eval (weight (rs,(cs,rows))) := by
  have hc : List.Forall₂ (· ≤ ·) cs cs := by
    induction cs with
    | nil => exact .nil
    | cons c cs ih => exact .cons le_rfl ih
  have ht := tableFold_bounds pre cs cs rows hc
  have hw := weight_listLE ht.1
  have hp := (list_length_le_weight pre).trans (weight_prefix he)
  let S := weight (rs,(cs,rows))
  have hrs : weight rs ≤ S := by dsimp [S]; simp only [weight_prod]; omega
  have hcs : weight cs ≤ S := by dsimp [S]; simp only [weight_prod]; omega
  have hrows : weight rows ≤ S := by dsimp [S]; simp only [weight_prod]; omega
  have hpre : pre.length ≤ S := hp.trans hrs
  change weight (pre.foldl (fun z a => GreedyFeasibleTable.tableRow (a,z)) (cs,rows)) ≤ _
  rw [←Prod.eta (pre.foldl (fun z a => GreedyFeasibleTable.tableRow (a,z)) (cs,rows)),weight_prod]
  simp only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one]
  change _ ≤ 12*(S+1)^2
  have hm := Nat.mul_le_mul hpre (show 4*weight cs+1 ≤ 4*S+1 by omega)
  nlinarith [ht.2]

lemma typed_tableFold_actual : Typed (fold GreedyFeasibleTable.tableRowRealizer) 9 := by
  apply typed_fold (e:=4) (s:=2) typed_tableRow_actual (12*(X+1)^2)
    (by
      have ha : (X+1 : Polynomial ℕ).natDegree ≤ 1 := by simpa using degree_affine 1 1
      simpa [pow_two] using degree_scale 12 (degree_mul ha ha)) (by decide) (by decide)
  rintro rs ⟨cs,rows⟩ pre post he
  exact tableFold_intermediate rs cs rows pre post he

/-- Actual greedy table program, including all intermediate encoded
accumulators, final reversal and final output, for EVERY literal input. -/
theorem typed_actual_greedyTable : Typed GreedyFeasibleTable.tableRealizer 18 := by
  unfold GreedyFeasibleTable.tableRealizer
  dsimp only
  apply typed_congr
  apply typed_composition (e:=9) (t:=2) _ typed_reverse
  apply typed_composition (e:=9) _ typed_second
  apply typed_composition (e:=1) _ typed_tableFold_actual
  exact typed_pair typed_first (typed_pair typed_second (typed_constant []))

/-- A separate semantic output bound keeps the literal greedy matrix encoding
quadratic in input bit weight, independently of its execution witness. -/
lemma greedyTable_weight_output (z : List ℕ × List ℕ) :
    weight (GreedyFeasibleTable.listMatrix z.1 z.2) ≤ 12*(weight z+1)^2 := by
  have hc : List.Forall₂ (· ≤ ·) z.2 z.2 := by
    induction z.2 with
    | nil => exact .nil
    | cons c cs ih => exact .cons le_rfl ih
  have ht := (tableFold_bounds z.1 z.2 z.2 [] hc).2
  rw [GreedyFeasibleTable.fold_tableRow,List.append_nil,weight_reverse,weight_nil] at ht
  have hr : z.1.length ≤ weight z :=
    (list_length_le_weight z.1).trans (by rw [weight_prod]; omega)
  have hw : weight z.2 ≤ weight z := by rw [weight_prod]; omega
  have hm := Nat.mul_le_mul hr (show 4*weight z.2+1 ≤ 4*weight z+1 by omega)
  nlinarith

lemma weight_getD_bound {A : Type} [Codec A] (xs : List A) (n : ℕ) (d : A) :
    weight (xs.getD n d) ≤ weight xs+weight d := by
  induction xs generalizing n with
  | nil => simp
  | cons a xs ih =>
    cases n with
    | zero => simp only [List.getD_cons_zero,weight_cons]; omega
    | succ n =>
      have hh := ih n
      simpa only [List.getD_cons_succ,weight_cons] using hh.trans
        (by omega : weight xs+weight d ≤ 1+weight a+weight xs+weight d)

end
end Math115.InitialRuntimeNext
