/-
SPDX-License-Identifier: Apache-2.0

Exact elementary completion translations and physical move bridges for the
pinned OpenAI #115 definitions. See docs/completion-adjustment-formalization.md.
-/

import Mathlib.Tactic.ByContra
import Mathlib.Tactic.Convert
import Mathlib.Tactic.Push
import Mathlib.Tactic.SplitIfs
import OAI.Combinatorics.ContingencyTables.Transport.SignedMarginTranslation
import OAI.Combinatorics.ContingencyTables.Transport.ReferenceCompletionBlock
import OAI.Combinatorics.ContingencyTables.Sampling.PhysicalRepairMargins
import OAI.Combinatorics.ContingencyTables.Sampling.RepairPrefixes

/-! Exact elementary completion translations, using the source `star` map. -/
namespace Math115.CompletionAdjustment

open scoped BigOperators Classical
open OAI.ContingencyTables
open OAI.ContingencyTables.CompletionTranslation

variable {I J : Type*} [Fintype I] [Fintype J]

/-- A signed unit, including a possible reference index. -/
noncomputable def unit {K : Type*} (a k : K) : ℤ := if k = a then 1 else 0

/-- One integer matrix unit. -/
noncomputable def cell (a : Option I) (b : Option J)
    (i : Option I) (j : Option J) : ℤ := unit (a,b) (i,j)

omit [Fintype I] in
lemma star_zero : star (fun _ : Option I => 0) (fun _ : Option J => 0) =
    fun _ _ => 0 := by
  funext i j
  cases i <;> cases j <;> simp [CompletionTranslation.star]

omit [Fintype I] in
lemma star_row_transfer (a b : Option I) :
    star (fun i => unit a i - unit b i) (fun _ : Option J => 0) =
      fun i j => cell a none i j - cell b none i j := by
  funext i j
  cases i <;> cases j <;> simp [CompletionTranslation.star, cell, unit] <;> split_ifs <;> rfl

omit [Fintype I] in
lemma star_column_transfer (a b : Option J) :
    star (fun _ : Option I => 0) (fun j => unit a j - unit b j) =
      fun i j => cell none a i j - cell none b i j := by
  funext i j
  cases a <;> cases b <;> cases i <;> cases j <;>
    simp [CompletionTranslation.star, cell, unit, Finset.sum_sub_distrib]

omit [Fintype I] in
lemma star_paired_increase (a : Option I) (b : Option J) :
    star (unit a) (unit b) = fun i j =>
      cell a none i j + cell none b i j - cell none none i j := by
  funext i j
  cases a <;> cases b <;> cases i <;> cases j <;>
    simp [CompletionTranslation.star, cell, unit]

omit [Fintype I] in
lemma star_paired_decrease (a : Option I) (b : Option J) :
    star (fun i => -unit a i) (fun j => -unit b j) = fun i j =>
      -(cell a none i j + cell none b i j - cell none none i j) := by
  rw [OAI.ContingencyTables.CompletionTranslation.star_neg, star_paired_increase]

noncomputable def support (D : Option I → Option J → ℤ) : Finset (Option I × Option J) :=
  Finset.univ.filter (fun p => D p.1 p.2 ≠ 0)

noncomputable def negative (D : Option I → Option J → ℤ) : Finset (Option I × Option J) :=
  Finset.univ.filter (fun p => D p.1 p.2 < 0)

/-- The bounds count coincident matrix positions only once. -/
structure Bounds (D : Option I → Option J → ℤ) : Prop where
  entry : ∀ i j, |D i j| ≤ 1
  support_card : (support D).card ≤ 3
  negative_card : (negative D).card ≤ 2
  one_orientation : (negative D).card ≤ 1 ∨ (negative (fun i j => -D i j)).card ≤ 1

omit [Fintype I] [Fintype J] in
private lemma card_le_three_of_subset {s : Finset (Option I × Option J)}
    (a b c : Option I × Option J) (h : s ⊆ {a,b,c}) : s.card ≤ 3 := by
  exact (Finset.card_le_card h).trans (by
    exact (Finset.card_insert_le _ _).trans (by
      have := Finset.card_insert_le b {c}
      simpa using Nat.add_le_add_right this 1))

omit [Fintype I] [Fintype J] in
private lemma card_le_two_of_subset {s : Finset (Option I × Option J)}
    (a b : Option I × Option J) (h : s ⊆ {a,b}) : s.card ≤ 2 := by
  exact (Finset.card_le_card h).trans (by
    simpa using Finset.card_insert_le a {b})

omit [Fintype I] [Fintype J] in
private lemma card_le_one_of_subset {s : Finset (Option I × Option J)}
    (a : Option I × Option J) (h : s ⊆ {a}) : s.card ≤ 1 := by
  simpa using Finset.card_le_card h

lemma zero_bounds : Bounds (fun _ : Option I => fun _ : Option J => (0 : ℤ)) := by
  constructor <;> simp [support, negative]

lemma transfer_bounds (a b : Option I × Option J) :
    Bounds (fun i j => unit a (i,j) - unit b (i,j)) := by
  constructor
  · intro i j
    simp only [unit]
    split_ifs <;> norm_num
  · apply le_trans (card_le_two_of_subset a b ?_) (by omega)
    intro p hp
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_contra hn
    have hpa : p ≠ a := fun h => hn (by simp [h])
    have hpb : p ≠ b := fun h => hn (by simp [h])
    exact hp (by simp [unit, hpa, hpb])
  · apply le_trans (card_le_one_of_subset b ?_) (by omega)
    intro p hp
    simp only [negative, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_contra hn
    have hpb : p ≠ b := by simpa using hn
    simp only [unit, ite_eq_right hpb, sub_zero] at hp
    split_ifs at hp <;> omega
  · left
    apply card_le_one_of_subset b
    intro p hp
    simp only [negative, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_contra hn
    have hpb : p ≠ b := by simpa using hn
    simp only [unit, ite_eq_right hpb, sub_zero] at hp
    split_ifs at hp <;> omega

lemma paired_bounds (a : Option I) (b : Option J) :
    Bounds (fun i j => cell a none i j + cell none b i j - cell none none i j) := by
  constructor
  · intro i j
    cases a <;> cases b <;> cases i <;> cases j <;>
      simp [cell, unit] <;> split_ifs <;> norm_num
  · apply card_le_three_of_subset (a,none) (none,b) (none,none)
    intro p hp
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_contra hn
    have h₁ : p ≠ (a,none) := fun h => hn (by simp [h])
    have h₂ : p ≠ (none,b) := fun h => hn (by simp [h])
    have h₃ : p ≠ (none,none) := fun h => hn (by simp [h])
    exact hp (by simp [cell, unit, h₁, h₂, h₃])
  · apply le_trans (card_le_one_of_subset (none,none) ?_) (by omega)
    intro p hp
    simp only [negative, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_contra hn
    have h₃ : p ≠ (none,none) := by simpa using hn
    simp only [cell, unit, ite_eq_right h₃, sub_zero] at hp
    split_ifs at hp <;> omega
  · left
    apply card_le_one_of_subset (none,none)
    intro p hp
    simp only [negative, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_contra hn
    have h₃ : p ≠ (none,none) := by simpa using hn
    simp only [cell, unit, ite_eq_right h₃, sub_zero] at hp
    split_ifs at hp <;> omega

lemma paired_negative_bounds (a : Option I) (b : Option J) :
    Bounds (fun i j => -(cell a none i j + cell none b i j - cell none none i j)) := by
  have h := paired_bounds a b
  constructor
  · intro i j
    simpa only [abs_neg] using h.entry i j
  · simpa only [support, neg_ne_zero] using h.support_card
  · apply card_le_two_of_subset (a,none) (none,b)
    intro p hp
    simp only [negative, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_contra hn
    have h₁ : p ≠ (a,none) := fun he => hn (by simp [he])
    have h₂ : p ≠ (none,b) := fun he => hn (by simp [he])
    simp only [cell, unit, ite_eq_right h₁, ite_eq_right h₂] at hp
    split_ifs at hp <;> omega
  · right
    simp only [neg_neg]
    apply card_le_one_of_subset (none,none)
    intro p hp
    simp only [negative, Finset.mem_filter, Finset.mem_univ, true_and] at hp
    by_contra hmem
    have h₃ : p ≠ (none,none) := by simpa using hmem
    simp only [cell, unit, ite_eq_right h₃, sub_zero] at hp
    split_ifs at hp <;> omega

/-- The exhaustive signed-margin families of an elementary edge. -/
inductive ElementaryMargins {K T : Type*} : (K → ℤ) → (T → ℤ) → Prop
  | zero : ElementaryMargins (fun _ => 0) (fun _ => 0)
  | row (a b : K) : ElementaryMargins (fun i => unit a i - unit b i) (fun _ => 0)
  | column (a b : T) : ElementaryMargins (fun _ => 0) (fun j => unit a j - unit b j)
  | increase (a : K) (b : T) : ElementaryMargins (unit a) (unit b)
  | decrease (a : K) (b : T) : ElementaryMargins (fun i => -unit a i) (fun j => -unit b j)

/-- Exact norm and support bounds for the actual source reference-star map. -/
theorem elementary_star_bounds {R : Option I → ℤ} {P : Option J → ℤ}
    (h : ElementaryMargins R P) : Bounds (star R P) := by
  cases h with
  | zero => simpa only [star_zero] using zero_bounds (I := I) (J := J)
  | row a b =>
    rw [star_row_transfer]
    exact transfer_bounds (a,none) (b,none)
  | column a b =>
    rw [star_column_transfer]
    exact transfer_bounds (none,a) (none,b)
  | increase a b => simpa only [star_paired_increase] using paired_bounds a b
  | decrease a b => simpa only [star_paired_decrease] using paired_negative_bounds a b

end Math115.CompletionAdjustment

namespace Math115.CompletionAdjustment

open scoped BigOperators Classical
open OAI.ContingencyTables
open OAI.ContingencyTables.IntegerWeightedTransport
open OAI.ContingencyTables.FactorialSignatures

/-- The same two coordinates control every selected observable. The source's
`≤ 2` estimate loses the fact that the coefficients are Boolean. -/
lemma exchange_selected_sum_formula {C : Type*} [Fintype C] [DecidableEq C]
    (X Y : C → ℕ) (h : IntegerExchangeAdjacent X Y) :
    ∃ a b : C, ∀ p : C → Prop,
      (((∑ k, if p k then Y k else 0) : ℕ) : ℤ) -
        (((∑ k, if p k then X k else 0) : ℕ) : ℤ) =
        (if p a then 1 else 0) - (if p b then 1 else 0) := by
  obtain ⟨D,a,b,_,ha,hb,rfl,rfl⟩ := h
  refine ⟨a,b,?_⟩
  intro p
  have h₁ := linearObservable_removeOne (fun k => if p k then (1 : ℤ) else 0) D a ha
  have h₂ := linearObservable_removeOne (fun k => if p k then (1 : ℤ) else 0) D b hb
  have he : linearObservable (fun k => if p k then (1 : ℤ) else 0) (removeOne D b) -
      linearObservable (fun k => if p k then (1 : ℤ) else 0) (removeOne D a) =
      (if p a then (1 : ℤ) else 0) - (if p b then (1 : ℤ) else 0) := by
    rw [h₁,h₂]
    ring
  simpa only [linearObservable,ite_mul,one_mul,zero_mul,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_zero] using he

/-- A selected sum on an actual source unit-exchange edge changes by at most
one, independently of the number of selected coordinates. -/
theorem exchange_selected_sum_abs_le_one {C : Type*} [Fintype C] [DecidableEq C]
    (p : C → Prop) (X Y : C → ℕ) (h : IntegerExchangeAdjacent X Y) :
    |(((∑ k, if p k then Y k else 0) : ℕ) : ℤ) -
      (((∑ k, if p k then X k else 0) : ℕ) : ℤ)| ≤ 1 := by
  obtain ⟨a,b,he⟩ := exchange_selected_sum_formula X Y h
  rw [he p]
  split_ifs <;> norm_num

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

open OAI.ContingencyTables.SmallGraphProfiles
open OAI.ContingencyTables.PhysicalCompletionFibres
open OAI.ContingencyTables.FirstPaperProfiles
open OAI.ContingencyTables.FirstPaperPhysicalMarginal
open OAI.ContingencyTables.CompletionCounts
open OAI.ContingencyTables.PaddedCompletions
open OAI.ContingencyTables.SmallContextFibres
open OAI.ContingencyTables.SmallContextCoordinates

/-- Literal signed changes of both physical residual margins, with one shared
exchange witness. These are the four row/column-view cases, before restricting
to the feasible large rectangle. -/
theorem exchange_residual_formula (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (x y : PhysicalStates small B r c L)
    (hxcap : ∀ i j, small i j = false → (∑ k, residualRows small B r c L x k) ≤ B i j)
    (hycap : ∀ i j, small i j = false → (∑ k, residualRows small B r c L y k) ≤ B i j)
    (hxy : IntegerExchangeAdjacent (physicalProfile small B r c L x)
      (physicalProfile small B r c L y)) :
    ∃ a b : Cells small × Bool,
      (∀ i, (residualRows small B r c L y i : ℤ) - residualRows small B r c L x i =
        (if b.1.val.1 = i ∧ b.2 = false then 1 else 0) -
        (if a.1.val.1 = i ∧ a.2 = false then 1 else 0)) ∧
      (∀ j, (residualColumns small B r c L y j : ℤ) - residualColumns small B r c L x j =
        (if a.1.val.2 = j ∧ a.2 = true then 1 else 0) -
        (if b.1.val.2 = j ∧ b.2 = true then 1 else 0)) := by
  have hx := physical_original_residuals small B r c L x hxcap
  have hy := physical_original_residuals small B r c L y hycap
  obtain ⟨a,b,he⟩ := exchange_selected_sum_formula _ _ hxy
  refine ⟨a,b,?_,?_⟩
  · intro i
    have hm := he (fun k => k.1.val.1 = i ∧ k.2 = false)
    have hm' : (selectedRow small (physicalProfile small B r c L y) false i : ℤ) -
        (selectedRow small (physicalProfile small B r c L x) false i : ℤ) =
        (if a.1.val.1 = i ∧ a.2 = false then 1 else 0) -
        (if b.1.val.1 = i ∧ b.2 = false then 1 else 0) := by
      unfold selectedRow
      convert hm using 1
      all_goals
        congr 5 <;> first | exact Subsingleton.elim _ _ | (funext k; split_ifs <;> rfl)
    rw [selectedRow_eq_smallRow,selectedRow_eq_smallRow] at hm' 
    unfold residualRows
    rw [Nat.cast_add,Nat.cast_add,Nat.cast_sub (hy.1 i),Nat.cast_sub (hx.1 i)]
    linarith
  · intro j
    have hm := he (fun k => k.1.val.2 = j ∧ k.2 = true)
    have hm' : (selectedColumn small (physicalProfile small B r c L y) true j : ℤ) -
        (selectedColumn small (physicalProfile small B r c L x) true j : ℤ) =
        (if a.1.val.2 = j ∧ a.2 = true then 1 else 0) -
        (if b.1.val.2 = j ∧ b.2 = true then 1 else 0) := by
      unfold selectedColumn
      convert hm using 1
      all_goals
        congr 5 <;> first | exact Subsingleton.elim _ _ | (funext k; split_ifs <;> rfl)
    unfold residualColumns
    rw [Nat.cast_add,Nat.cast_add,Nat.cast_sub (hy.2 j),Nat.cast_sub (hx.2 j),
      smallColumn_cast_selected small B (physicalProfile small B r c L y)
        (naturalProfile_bounded y.val.val),
      smallColumn_cast_selected small B (physicalProfile small B r c L x)
        (naturalProfile_bounded x.val.val)]
    linarith

/-- The actual feasible physical exchange edges have one-unit residual changes;
this strengthens `exchange_residual_margins` without an extra premise. -/
theorem exchange_residual_margins_one (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (x y : PhysicalStates small B r c L)
    (hxcap : ∀ i j, small i j = false → (∑ k, residualRows small B r c L x k) ≤ B i j)
    (hycap : ∀ i j, small i j = false → (∑ k, residualRows small B r c L y k) ≤ B i j)
    (hxy : IntegerExchangeAdjacent (physicalProfile small B r c L x)
      (physicalProfile small B r c L y)) :
    (∀ i, |(residualRows small B r c L y i : ℤ) - residualRows small B r c L x i| ≤ 1) ∧
    (∀ j, |(residualColumns small B r c L y j : ℤ) - residualColumns small B r c L x j| ≤ 1) := by
  obtain ⟨a,b,hr,hc⟩ := exchange_residual_formula small B r c L x y hxcap hycap hxy
  constructor
  · intro i
    rw [hr i]
    split_ifs <;> norm_num
  · intro j
    rw [hc j]
    split_ifs <;> norm_num

omit [Fintype I] [Fintype J] in
/-- Repairing a row-major defect preserves every earlier entry and places the
special entry at `ell` in the same row, or `ell - 1` in a later row. -/
theorem row_major_repair_conditional {x q : I → J → ℕ} {s t : I × J} {ell : ℕ}
    (hd : IsDefect x q s t) (hst : RowMajorBefore s t)
    (hell : q s.1 s.2 = ell) :
    (∀ w, RowMajorBefore w s → repairMatrix x s t w.1 w.2 = x w.1 w.2) ∧
    repairMatrix x s t s.1 s.2 = (if t.1 = s.1 then ell else ell - 1) := by
  constructor
  · exact fun w hw => repairMatrix_prefix hd hst hw
  · have hs := hd.negative_entry
    rw [repairMatrix_special hd]
    split_ifs <;> omega

end Math115.CompletionAdjustment

namespace Math115.CompletionAdjustment

open scoped BigOperators Classical
open OAI.ContingencyTables
open OAI.ContingencyTables.SmallGraphProfiles
open OAI.ContingencyTables.PhysicalCompletionFibres
open OAI.ContingencyTables.FirstPaperProfiles
open OAI.ContingencyTables.FirstPaperPhysicalMarginal
open OAI.ContingencyTables.CompletionCounts
open OAI.ContingencyTables.PaddedCompletions
open OAI.ContingencyTables.SmallContextFibres
open OAI.ContingencyTables.SmallContextCoordinates

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

omit [Fintype I] [Fintype J] in
private lemma repair_large_entry_exact (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I × J)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (ht : small t.1 t.2 = true) (i : I) (j : J) :
    (if small i j then 0 else repairMatrix (smallView small z false) s t i j) =
      if i = t.1 ∧ j = s.2 ∧ small t.1 s.2 = false then 1 else 0 := by
  cases hs : small i j
  · rw [ite_eq_right Bool.false_ne_true,repair_large_value small B z s t hd ht i j hs]
    by_cases hij : i = t.1 ∧ j = s.2
    · rcases hij with ⟨rfl,rfl⟩
      simp [hs]
    · simp [hij,show ¬(i = t.1 ∧ j = s.2 ∧ small t.1 s.2 = false) from
        fun h => hij ⟨h.1,h.2.1⟩]
  · rw [ite_eq_left rfl]
    symm
    apply ite_eq_right
    rintro ⟨rfl,rfl,hf⟩
    rw [hs] at hf
    contradiction

omit [Fintype I] in
lemma repair_large_row_exact (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I × J)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (ht : small t.1 t.2 = true) (i : I) :
    largeRow small (repairMatrix (smallView small z false) s t) i =
      if small t.1 s.2 = false ∧ i = t.1 then 1 else 0 := by
  unfold largeRow
  simp_rw [repair_large_entry_exact small B z s t hd ht]
  by_cases hs : small t.1 s.2 = false <;> by_cases hi : i = t.1 <;> simp [hs,hi]

omit [Fintype J] in
lemma repair_large_column_exact (small : I → J → Bool) (B : I → J → ℕ)
    (z : SmallProfile small) (s t : I × J)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (ht : small t.1 t.2 = true) (j : J) :
    largeColumnView small (repairMatrix (smallView small z false) s t) j =
      if small t.1 s.2 = false ∧ j = s.2 then 1 else 0 := by
  unfold largeColumnView
  simp_rw [repair_large_entry_exact small B z s t hd ht]
  by_cases hs : small t.1 s.2 = false <;> by_cases hj : j = s.2 <;> simp [hs,hj]

/-- An actual physical repair changes no completion margin for a small
receiver. A large receiver adds exactly one to its row and column. -/
theorem repair_residual_formula (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (x y : PhysicalStates small B r c L)
    (hxcap : ∀ i j, small i j = false → (∑ k, residualRows small B r c L x k) ≤ B i j)
    (hycap : ∀ i j, small i j = false → (∑ k, residualRows small B r c L y k) ≤ B i j)
    (s t : I × J)
    (hd : IsDefect (smallView small (physicalProfile small B r c L x) false)
      (smallQ small B (physicalProfile small B r c L x)) s t)
    (ht : small t.1 t.2 = true)
    (hcap : ∀ a : Cells small, repairMatrix
      (smallView small (physicalProfile small B r c L x) false) s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2)
    (heq : physicalProfile small B r c L y = repairedProfile small B
      (physicalProfile small B r c L x) s t) :
    (∀ i, (residualRows small B r c L y i : ℤ) - residualRows small B r c L x i =
      if small t.1 s.2 = false ∧ i = t.1 then 1 else 0) ∧
    (∀ j, (residualColumns small B r c L y j : ℤ) - residualColumns small B r c L x j =
      if small t.1 s.2 = false ∧ j = s.2 then 1 else 0) := by
  have hx := physical_original_residuals small B r c L x hxcap
  have hy := physical_original_residuals small B r c L y hycap
  have hm := repairMatrix_margins hd
    (fun i => ∑ j, smallView small (physicalProfile small B r c L x) false i j)
    (fun j => ∑ i, smallQ small B (physicalProfile small B r c L x) i j)
    (fun _ => rfl) (fun _ => rfl)
  constructor
  · intro i
    have hs := row_small_large small
      (repairMatrix (smallView small (physicalProfile small B r c L x) false) s t) i
    rw [hm.1 i] at hs
    dsimp only at hs
    rw [←selectedRow_eq,selectedRow_eq_smallRow,
      repair_large_row_exact small B _ s t hd ht] at hs
    have he := congrArg (fun n : ℕ => (n : ℤ)) hs
    simp only [Nat.cast_add,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] at he
    unfold residualRows
    rw [Nat.cast_add,Nat.cast_add,Nat.cast_sub (hy.1 i),Nat.cast_sub (hx.1 i),
      heq,repaired_small_row]
    linarith
  · intro j
    have hs := column_small_large small
      (repairMatrix (smallView small (physicalProfile small B r c L x) false) s t) j
    rw [hm.2 j] at hs
    dsimp only at hs
    rw [smallQ_column_sum,
      repair_large_column_exact small B _ s t hd ht] at hs
    have he := congrArg (fun n : ℕ => (n : ℤ)) hs
    simp only [Nat.cast_add,Nat.cast_ite,Nat.cast_one,Nat.cast_zero] at he
    unfold residualColumns
    rw [Nat.cast_add,Nat.cast_add,Nat.cast_sub (hy.2 j),Nat.cast_sub (hx.2 j),
      heq,repaired_small_column small B _ s t hcap]
    linarith

end Math115.CompletionAdjustment

namespace Math115.CompletionAdjustment

open scoped BigOperators Classical

private lemma restrict_unit {K T : Type*} (f : Option K → T) (hf : Function.Injective f)
    (a : T) (hz : ∀ k, (¬ ∃ i, f i = k) → unit a k = 0) :
    ∃ a' : Option K, ∀ i, unit a (f i) = unit a' i := by
  have ha : ∃ i, f i = a := by
    by_contra ha
    have he := hz a ha
    simp [unit] at he
  obtain ⟨a',ha'⟩ := ha
  refine ⟨a',?_⟩
  intro i
  have he : f i = a ↔ i = a' := by
    rw [←ha']
    exact hf.eq_iff
  simp only [unit,he]
  split_ifs <;> rfl

private lemma restrict_transfer {K T : Type*} (f : Option K → T) (hf : Function.Injective f)
    (a b : T) (hz : ∀ k, (¬ ∃ i, f i = k) → unit a k - unit b k = 0) :
    ∃ a' b' : Option K, ∀ i, unit a (f i) - unit b (f i) = unit a' i - unit b' i := by
  by_cases hab : a = b
  · subst b
    exact ⟨none,none,fun _ => by simp⟩
  · have ha : ∃ i, f i = a := by
      by_contra ha
      have he := hz a ha
      simp [unit,hab] at he
    have hb : ∃ i, f i = b := by
      by_contra hb
      have he := hz b hb
      simp [unit,Ne.symm hab] at he
    obtain ⟨a',ha'⟩ := ha
    obtain ⟨b',hb'⟩ := hb
    refine ⟨a',b',?_⟩
    intro i
    have he₁ : f i = a ↔ i = a' := by rw [←ha']; exact hf.eq_iff
    have he₂ : f i = b ↔ i = b' := by rw [←hb']; exact hf.eq_iff
    simp only [unit,he₁,he₂]
    split_ifs <;> rfl

/-- Restriction preserves the elementary classification when the actual
margin change is zero off the included rectangle. The zero premise prevents
silently retaining only one end of a same-view transfer. -/
theorem elementary_restrict {K T I J : Type*} {R : K → ℤ} {P : T → ℤ}
    (h : ElementaryMargins R P) (f : Option I → K) (g : Option J → T)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hR : ∀ k, (¬ ∃ i, f i = k) → R k = 0)
    (hP : ∀ k, (¬ ∃ j, g j = k) → P k = 0) :
    ElementaryMargins (fun i => R (f i)) (fun j => P (g j)) := by
  cases h with
  | zero => exact ElementaryMargins.zero
  | row a b =>
    obtain ⟨a',b',he⟩ := restrict_transfer f hf a b hR
    simpa only [funext he] using (ElementaryMargins.row (T := Option J) a' b')
  | column a b =>
    obtain ⟨a',b',he⟩ := restrict_transfer g hg a b hP
    simpa only [funext he] using (ElementaryMargins.column (K := Option I) a' b')
  | increase a b =>
    obtain ⟨a',he₁⟩ := restrict_unit f hf a hR
    obtain ⟨b',he₂⟩ := restrict_unit g hg b hP
    simpa only [funext he₁,funext he₂] using (ElementaryMargins.increase a' b')
  | decrease a b =>
    obtain ⟨a',he₁⟩ := restrict_unit f hf a (fun k hk => by have ht := hR k hk; dsimp only at ht; omega)
    obtain ⟨b',he₂⟩ := restrict_unit g hg b (fun k hk => by have ht := hP k hk; dsimp only at ht; omega)
    convert ElementaryMargins.decrease a' b' using 1 <;> funext k
    · dsimp only
      rw [he₁]
    · dsimp only
      rw [he₂]

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

open OAI.ContingencyTables
open OAI.ContingencyTables.CompletionTranslation
open OAI.ContingencyTables.IntegerWeightedTransport
open OAI.ContingencyTables.SmallGraphProfiles
open OAI.ContingencyTables.PhysicalCompletionFibres
open OAI.ContingencyTables.FirstPaperProfiles
open OAI.ContingencyTables.FirstPaperPhysicalMarginal
open OAI.ContingencyTables.CompletionCounts
open OAI.ContingencyTables.PaddedCompletions
open OAI.ContingencyTables.SmallContextFibres
open OAI.ContingencyTables.SmallContextCoordinates

theorem exchange_residual_elementary (small : I → J → Bool) (B : I → J → ℕ)
    (r : I → ℕ) (c : J → ℕ) (L : ℕ)
    (x y : PhysicalStates small B r c L)
    (hxcap : ∀ i j, small i j = false → (∑ k, residualRows small B r c L x k) ≤ B i j)
    (hycap : ∀ i j, small i j = false → (∑ k, residualRows small B r c L y k) ≤ B i j)
    (hxy : IntegerExchangeAdjacent (physicalProfile small B r c L x)
      (physicalProfile small B r c L y)) :
    ElementaryMargins
      (fun i => (residualRows small B r c L y i : ℤ) - residualRows small B r c L x i)
      (fun j => (residualColumns small B r c L y j : ℤ) - residualColumns small B r c L x j) := by
  obtain ⟨a,b,hr,hc⟩ := exchange_residual_formula small B r c L x y hxcap hycap hxy
  have hr' := funext hr
  have hc' := funext hc
  rw [hr',hc']
  cases ha : a.2 <;> cases hb : b.2
  · convert ElementaryMargins.row (T := J) b.1.val.1 a.1.val.1 using 1 <;>
      funext k <;> simp [unit,eq_comm] <;> split_ifs <;> rfl
  · convert ElementaryMargins.decrease a.1.val.1 b.1.val.2 using 1 <;>
      funext k <;> simp [unit,eq_comm]
  · convert ElementaryMargins.increase b.1.val.1 a.1.val.2 using 1 <;>
      funext k <;> simp [unit,eq_comm]
  · convert ElementaryMargins.column (K := I) a.1.val.2 b.1.val.2 using 1 <;>
      funext k <;> simp [unit,eq_comm] <;> split_ifs <;> rfl

/-- Physical feasibility discharges the restriction's off-rectangle premise. -/
theorem physical_reference_elementary (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (B : I → J → ℕ) (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hxcap : ∀ i j, firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L x k) ≤ B i j)
    (hycap : ∀ i j, firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L y k) ≤ B i j)
    (he : ElementaryMargins
      (fun i => (residualRows (firstPaperSmall r c U) B r c L y i : ℤ) -
        residualRows (firstPaperSmall r c U) B r c L x i)
      (fun j => (residualColumns (firstPaperSmall r c U) B r c L y j : ℤ) -
        residualColumns (firstPaperSmall r c U) B r c L x j)) :
    ElementaryMargins
      (fun i => (referenceRows r c U L B i₀ y i : ℤ) - referenceRows r c U L B i₀ x i)
      (fun j => (referenceColumns r c U L B j₀ y j : ℤ) - referenceColumns r c U L B j₀ x j) := by
  apply elementary_restrict he
    (fun i => ((Equiv.optionSubtypeNe i₀) i).val)
    (fun j => ((Equiv.optionSubtypeNe j₀) j).val)
    (Subtype.val_injective.comp (Equiv.optionSubtypeNe i₀).injective)
    (Subtype.val_injective.comp (Equiv.optionSubtypeNe j₀).injective)
  · intro i hi
    have hout : ¬ U ≤ r i := by
      intro hl
      apply hi
      refine ⟨(Equiv.optionSubtypeNe i₀).symm ⟨i,hl⟩,?_⟩
      exact congrArg (fun k : LargeRows r U => k.val)
        ((Equiv.optionSubtypeNe i₀).apply_symm_apply ⟨i,hl⟩)
    rw [physical_residual_row_zero r c U L B y hycap i hout,
      physical_residual_row_zero r c U L B x hxcap i hout]
    simp
  · intro j hj
    have hout : ¬ U ≤ c j := by
      intro hl
      apply hj
      refine ⟨(Equiv.optionSubtypeNe j₀).symm ⟨j,hl⟩,?_⟩
      exact congrArg (fun k : LargeColumns c U => k.val)
        ((Equiv.optionSubtypeNe j₀).apply_symm_apply ⟨j,hl⟩)
    rw [physical_residual_column_zero r c U L B y hycap j hout,
      physical_residual_column_zero r c U L B x hxcap j hout]
    simp

/-- Complete actual-exchange bridge: one-unit entries, at most three support
cells, at most two negative cells, and an orientation with at most one. -/
theorem exchange_reference_adjustment_bounds (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (B : I → J → ℕ) (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hxcap : ∀ i j, firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L x k) ≤ B i j)
    (hycap : ∀ i j, firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L y k) ≤ B i j)
    (hxy : IntegerExchangeAdjacent (physicalProfile (firstPaperSmall r c U) B r c L x)
      (physicalProfile (firstPaperSmall r c U) B r c L y)) :
    Bounds (between (referenceRows r c U L B i₀ x) (referenceRows r c U L B i₀ y)
      (referenceColumns r c U L B j₀ x) (referenceColumns r c U L B j₀ y)) := by
  apply elementary_star_bounds
  exact physical_reference_elementary r c U L B i₀ j₀ x y hxcap hycap
    (exchange_residual_elementary _ B r c L x y hxcap hycap hxy)

end Math115.CompletionAdjustment

namespace Math115.CompletionAdjustment

open scoped BigOperators Classical
open OAI.ContingencyTables
open OAI.ContingencyTables.CompletionTranslation
open OAI.ContingencyTables.SmallGraphProfiles
open OAI.ContingencyTables.PhysicalCompletionFibres
open OAI.ContingencyTables.FirstPaperProfiles
open OAI.ContingencyTables.FirstPaperPhysicalMarginal
open OAI.ContingencyTables.CompletionCounts
open OAI.ContingencyTables.PaddedCompletions
open OAI.ContingencyTables.SmallContextFibres
open OAI.ContingencyTables.SmallContextCoordinates

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

/-- Complete actual-repair bridge, covering both small and large receivers.
The same four bounds also hold for inverse repairs by swapping endpoints. -/
theorem repair_reference_elementary (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (B : I → J → ℕ) (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hxcap : ∀ i j, firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L x k) ≤ B i j)
    (hycap : ∀ i j, firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L y k) ≤ B i j)
    (s t : I × J)
    (hd : IsDefect (smallView (firstPaperSmall r c U)
      (physicalProfile (firstPaperSmall r c U) B r c L x) false)
      (smallQ (firstPaperSmall r c U) B (physicalProfile (firstPaperSmall r c U) B r c L x)) s t)
    (ht : firstPaperSmall r c U t.1 t.2 = true)
    (hcap : ∀ a : Cells (firstPaperSmall r c U), repairMatrix
      (smallView (firstPaperSmall r c U) (physicalProfile (firstPaperSmall r c U) B r c L x) false)
      s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2)
    (heq : physicalProfile (firstPaperSmall r c U) B r c L y =
      repairedProfile (firstPaperSmall r c U) B (physicalProfile (firstPaperSmall r c U) B r c L x) s t) :
    ElementaryMargins
      (fun i => (referenceRows r c U L B i₀ y i : ℤ) - referenceRows r c U L B i₀ x i)
      (fun j => (referenceColumns r c U L B j₀ y j : ℤ) - referenceColumns r c U L B j₀ x j) := by
  apply physical_reference_elementary r c U L B i₀ j₀ x y hxcap hycap
  obtain ⟨hr,hc⟩ := repair_residual_formula _ B r c L x y hxcap hycap s t hd ht hcap heq
  rw [funext hr,funext hc]
  by_cases hv : firstPaperSmall r c U t.1 s.2 = false
  · convert ElementaryMargins.increase t.1 s.2 using 1 <;> funext k <;> simp [hv,unit]
  · simpa [hv] using (ElementaryMargins.zero (K := I) (T := J))

end Math115.CompletionAdjustment

namespace Math115.CompletionAdjustment

open scoped Classical
open OAI.ContingencyTables.CompletionTranslation

lemma ElementaryMargins.neg {K T : Type*} {R : K → ℤ} {P : T → ℤ}
    (h : ElementaryMargins R P) :
    ElementaryMargins (fun i => -R i) (fun j => -P j) := by
  cases h with
  | zero => simpa only [neg_zero] using (ElementaryMargins.zero (K := K) (T := T))
  | row a b =>
    convert ElementaryMargins.row (T := T) b a using 1
    · funext i; ring
    · funext j; simp
  | column a b =>
    convert ElementaryMargins.column (K := K) b a using 1
    · funext i; simp
    · funext j; ring
  | increase a b => exact ElementaryMargins.decrease a b
  | decrease a b => simpa only [neg_neg] using (ElementaryMargins.increase a b)

/-- Reversing an elementary move satisfies the same bounds, including the
two-negative-cell bound needed for directional proposal acceptance. -/
theorem elementary_star_reverse_bounds {I J : Type*} [Fintype I] [Fintype J]
    {R : Option I → ℤ} {P : Option J → ℤ} (h : ElementaryMargins R P) :
    Bounds (fun i j => -star R P i j) := by
  rw [←OAI.ContingencyTables.CompletionTranslation.star_neg]
  exact elementary_star_bounds h.neg

end Math115.CompletionAdjustment

namespace Math115.CompletionAdjustment

open scoped Classical

/-- For the one-unit translations, every rejection is exactly a zero in a
negative adjustment cell. No reference-cross union bound is required. -/
theorem translation_rejection_iff {I J : Type*} [Fintype I] [Fintype J]
    {D : Option I → Option J → ℤ} (hD : Bounds D)
    (X : Option I → Option J → ℕ) :
    (¬ ∀ i j, 0 ≤ (X i j : ℤ) + D i j) ↔
      ∃ p ∈ negative D, X p.1 p.2 = 0 := by
  constructor
  · intro hx
    push Not at hx
    obtain ⟨i,j,hij⟩ := hx
    have hb := (abs_le.mp (hD.entry i j)).1
    have hxnonneg : 0 ≤ (X i j : ℤ) := Int.natCast_nonneg _
    refine ⟨(i,j),?_,?_⟩
    · simp only [negative,Finset.mem_filter,Finset.mem_univ,true_and]
      omega
    · change X i j = 0
      omega
  · rintro ⟨p,hp,hzero⟩ hx
    have hi := hx p.1 p.2
    simp only [negative,Finset.mem_filter,Finset.mem_univ,true_and] at hp
    rw [hzero] at hi
    omega

end Math115.CompletionAdjustment

namespace Math115.CompletionAdjustment

open scoped BigOperators Classical
open OAI.ContingencyTables
open OAI.ContingencyTables.CompletionTranslation

/-- With one completion row, the reference adjustment is the literal
entrywise difference of the source and target tables. -/
theorem singleton_row_between {I J : Type*} [Fintype I] [Fintype J] [IsEmpty I]
    {R₀ R₁ : Option I → ℕ} {P₀ P₁ : Option J → ℕ}
    (X : Table R₀ P₀) (Y : Table R₁ P₁) (i : Option I) (j : Option J) :
    between R₀ R₁ P₀ P₁ i j = (Y.val i j : ℤ) - X.val i j := by
  cases i with
  | some i => exact isEmptyElim i
  | none =>
    have hd := between_columns R₀ R₁ P₀ P₁ (totals_equal X.property) (totals_equal Y.property) j
    have hx := X.property.2 j
    have hy := Y.property.2 j
    simp only [Fintype.sum_option] at hd hx hy
    simp at hd hx hy
    rw [hx,hy]
    exact hd

/-- The symmetric single-column case has no cancellation exceptions. -/
theorem singleton_column_between {I J : Type*} [Fintype I] [Fintype J] [IsEmpty J]
    {R₀ R₁ : Option I → ℕ} {P₀ P₁ : Option J → ℕ}
    (X : Table R₀ P₀) (Y : Table R₁ P₁) (i : Option I) (j : Option J) :
    between R₀ R₁ P₀ P₁ i j = (Y.val i j : ℤ) - X.val i j := by
  cases j with
  | some j => exact isEmptyElim j
  | none =>
    have hd := between_rows R₀ R₁ P₀ P₁ i
    have hx := X.property.1 i
    have hy := Y.property.1 i
    simp only [Fintype.sum_option] at hd hx hy
    simp at hd hx hy
    rw [hx,hy]
    exact hd

/-- Singleton blocks translate every source table to the target table, so
there is no rejection even when a reference arm coincides with the center. -/
theorem singleton_translation_nonnegative {I J : Type*} [Fintype I] [Fintype J]
    {R₀ R₁ : Option I → ℕ} {P₀ P₁ : Option J → ℕ}
    (hs : IsEmpty I ∨ IsEmpty J) (X : Table R₀ P₀) (Y : Table R₁ P₁) :
    ∀ i j, 0 ≤ (X.val i j : ℤ) + between R₀ R₁ P₀ P₁ i j := by
  intro i j
  rcases hs with hi | hj
  · let := hi
    rw [singleton_row_between X Y]
    linarith [Int.natCast_nonneg (Y.val i j)]
  · let := hj
    rw [singleton_column_between X Y]
    linarith [Int.natCast_nonneg (Y.val i j)]

/-- A nonempty ordinary fiber with an empty row or column index set has one
table. This is the separate deterministic branch, with no reference chosen. -/
theorem empty_rectangle_card_one {I J : Type*} [Fintype I] [Fintype J]
    (hs : IsEmpty I ∨ IsEmpty J) (R : I → ℕ) (P : J → ℕ)
    (hne : Nonempty (Table R P)) : Fintype.card (Table R P) = 1 := by
  have hsub : Subsingleton (Table R P) := by
    refine ⟨?_⟩
    intro X Y
    apply Subtype.ext
    funext i j
    rcases hs with hi | hj
    · let := hi
      exact isEmptyElim i
    · let := hj
      exact isEmptyElim j
  have hu : Fintype.card (Table R P) ≤ 1 := by
    have hh := Fintype.card_le_of_injective (fun _ : Table R P => (0 : Fin 1))
      (fun X Y _ => hsub.elim X Y)
    simpa using hh
  have hl := Fintype.card_pos_iff.mpr hne
  omega

end Math115.CompletionAdjustment

namespace Math115.CompletionAdjustment

open scoped BigOperators Classical
open OAI.ContingencyTables
open OAI.ContingencyTables.SmallGraphProfiles
open OAI.ContingencyTables.PhysicalCompletionFibres
open OAI.ContingencyTables.FirstPaperPhysicalMarginal
open OAI.ContingencyTables.CompletionCounts

universe u

/-- Actual physical states with an empty large rectangle have exactly one
completion. This handles the no-reference branch directly. -/
theorem physical_empty_completion_weight
    {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
    (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (B : I → J → ℕ)
    (z : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hcap : ∀ i j, firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L z k) ≤ B i j)
    (hempty : IsEmpty (LargeRows r U) ∨ IsEmpty (LargeColumns c U)) :
    hardMarginal (firstPaperSmall r c U) B r c L
      (physicalProfile (firstPaperSmall r c U) B r c L z) = 1 := by
  have hw := physical_weight_rectangle r c U L B z hcap
  have hz := z.property
  change 0 < hardMarginal (firstPaperSmall r c U) B r c L
    (physicalProfile (firstPaperSmall r c U) B r c L z) at hz
  rw [hw] at hz ⊢
  have hc : 0 < Fintype.card (Table
      (fun i : LargeRows r U => residualRows (firstPaperSmall r c U) B r c L z i.val)
      (fun j : LargeColumns c U => residualColumns (firstPaperSmall r c U) B r c L z j.val)) := by
    exact_mod_cast hz
  rw [empty_rectangle_card_one hempty _ _ (Fintype.card_pos_iff.mp hc)]
  norm_num

end Math115.CompletionAdjustment

namespace Math115.CompletionAdjustment

open scoped Classical
open OAI.ContingencyTables
open OAI.ContingencyTables.SmallGraphProfiles
open OAI.ContingencyTables.PhysicalCompletionFibres
open OAI.ContingencyTables.FirstPaperProfiles
open OAI.ContingencyTables.SmallContextFibres
open OAI.ContingencyTables.SmallContextCoordinates

universe u

/-- The row-major repair preserves both doubled-coordinate views of every
retained prefix cell, including the complemented column coordinate. -/
theorem repaired_profile_prefix
    {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
    (small : I → J → Bool) (B : I → J → ℕ) (z : SmallProfile small) (s t : I × J)
    (hz : ∀ a, z a ≤ B a.1.val.1 a.1.val.2)
    (hd : IsDefect (smallView small z false) (smallQ small B z) s t)
    (hst : RowMajorBefore s t) (a : Cells small) (ha : RowMajorBefore a.val s) (b : Bool) :
    repairedProfile small B z s t (a,b) = z (a,b) := by
  have hs : ¬(a.val.1 = s.1 ∧ a.val.2 = s.2) := fun h => ha.ne (Prod.ext h.1 h.2)
  have ht : ¬(a.val.1 = t.1 ∧ a.val.2 = t.2) := fun h =>
    (ha.trans hst).ne (Prod.ext h.1 h.2)
  have he := hd.2 a.val.1 a.val.2
  simp only [transferInt,hs,ht,ite_false,sub_zero,add_zero] at he
  have hbal := Int.natCast_inj.mp he
  have heta : (⟨(a.val.1,a.val.2),a.property⟩ : Cells small) = a := Subtype.ext (Prod.eta a.val)
  have hx : smallView small z false a.val.1 a.val.2 = z (a,false) := by
    simp only [smallView,a.property,dite_eq_left,heta]
  have hq : smallQ small B z a.val.1 a.val.2 = B a.val.1 a.val.2-z (a,true) := by
    simp only [smallQ,a.property,dite_eq_left,heta]
  have hp := repairMatrix_prefix hd hst ha
  cases b
  · change repairMatrix (smallView small z false) s t a.val.1 a.val.2 = z (a,false)
    rw [hp,hx]
  · change B a.val.1 a.val.2-repairMatrix (smallView small z false) s t a.val.1 a.val.2 = z (a,true)
    rw [hp,←hbal,hq]
    exact Nat.sub_sub_self (hz (a,true))

end Math115.CompletionAdjustment

namespace Math115.CompletionAdjustment

open scoped BigOperators Classical
open OAI.ContingencyTables
open OAI.ContingencyTables.CompletionTranslation
open OAI.ContingencyTables.SmallGraphProfiles
open OAI.ContingencyTables.PhysicalCompletionFibres
open OAI.ContingencyTables.FirstPaperProfiles
open OAI.ContingencyTables.FirstPaperPhysicalMarginal
open OAI.ContingencyTables.CompletionCounts
open OAI.ContingencyTables.PaddedCompletions
open OAI.ContingencyTables.SmallContextFibres
open OAI.ContingencyTables.SmallContextCoordinates

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]

theorem repair_reference_adjustment_bounds (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (B : I → J → ℕ) (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hxcap : ∀ i j, firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L x k) ≤ B i j)
    (hycap : ∀ i j, firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L y k) ≤ B i j)
    (s t : I × J)
    (hd : IsDefect (smallView (firstPaperSmall r c U)
      (physicalProfile (firstPaperSmall r c U) B r c L x) false)
      (smallQ (firstPaperSmall r c U) B (physicalProfile (firstPaperSmall r c U) B r c L x)) s t)
    (ht : firstPaperSmall r c U t.1 t.2 = true)
    (hcap : ∀ a : Cells (firstPaperSmall r c U), repairMatrix
      (smallView (firstPaperSmall r c U) (physicalProfile (firstPaperSmall r c U) B r c L x) false)
      s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2)
    (heq : physicalProfile (firstPaperSmall r c U) B r c L y =
      repairedProfile (firstPaperSmall r c U) B (physicalProfile (firstPaperSmall r c U) B r c L x) s t) :
    Bounds (between (referenceRows r c U L B i₀ x) (referenceRows r c U L B i₀ y)
      (referenceColumns r c U L B j₀ x) (referenceColumns r c U L B j₀ y)) := by
  exact elementary_star_bounds
    (repair_reference_elementary r c U L B i₀ j₀ x y hxcap hycap s t hd ht hcap heq)

theorem repair_reverse_reference_adjustment_bounds (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (B : I → J → ℕ) (i₀ : LargeRows r U) (j₀ : LargeColumns c U)
    (x y : PhysicalStates (firstPaperSmall r c U) B r c L)
    (hxcap : ∀ i j, firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L x k) ≤ B i j)
    (hycap : ∀ i j, firstPaperSmall r c U i j = false →
      (∑ k, residualRows (firstPaperSmall r c U) B r c L y k) ≤ B i j)
    (s t : I × J)
    (hd : IsDefect (smallView (firstPaperSmall r c U)
      (physicalProfile (firstPaperSmall r c U) B r c L x) false)
      (smallQ (firstPaperSmall r c U) B (physicalProfile (firstPaperSmall r c U) B r c L x)) s t)
    (ht : firstPaperSmall r c U t.1 t.2 = true)
    (hcap : ∀ a : Cells (firstPaperSmall r c U), repairMatrix
      (smallView (firstPaperSmall r c U) (physicalProfile (firstPaperSmall r c U) B r c L x) false)
      s t a.val.1 a.val.2 ≤ B a.val.1 a.val.2)
    (heq : physicalProfile (firstPaperSmall r c U) B r c L y =
      repairedProfile (firstPaperSmall r c U) B (physicalProfile (firstPaperSmall r c U) B r c L x) s t) :
    Bounds (between (referenceRows r c U L B i₀ y) (referenceRows r c U L B i₀ x)
      (referenceColumns r c U L B j₀ y) (referenceColumns r c U L B j₀ x)) := by
  rw [between_reverse]
  exact elementary_star_reverse_bounds
    (repair_reference_elementary r c U L B i₀ j₀ x y hxcap hycap s t hd ht hcap heq)

end Math115.CompletionAdjustment
