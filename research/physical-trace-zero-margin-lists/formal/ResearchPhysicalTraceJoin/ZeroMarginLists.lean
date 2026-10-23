/-
SPDX-License-Identifier: Apache-2.0
Stable list filtering of positive margins, its ordered retained indices,
and exact table/law restoration. Repeated positive margin values remain
distinct positions. This module supplies no scale, branch, initialization,
finite-word preprocessing or machine-cost theorem.
-/
import ResearchPhysicalTraceJoin.ZeroMargins
import OAI.Combinatorics.ContingencyTables.Transport.TableReindex
import OAI.Combinatorics.ContingencyTables.Rooted.LargeMarginSemantics
import Mathlib.Algebra.BigOperators.Fin

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables
open ProfilePrograms SmallGraphProfiles CompletionCounts FirstSuccess ResidualMixture FairBits
open scoped BigOperators Classical

noncomputable section

/-- Literal stable filtering of the supplied list, including repeated values. -/
def positiveMargins (xs : List ℕ) : List ℕ := xs.filter (fun v => decide (0 < v))

def listMargin (xs : List ℕ) : Fin xs.length → ℕ := fun i => xs[i.val]

def filteredMargin (xs : List ℕ) : Fin (positiveMargins xs).length → ℕ :=
  listMargin (positiveMargins xs)

theorem ofFn_listMargin (xs : List ℕ) : List.ofFn (listMargin xs) = xs := by
  change List.ofFn (fun i : Fin xs.length => xs[i.val]) = xs
  exact List.ofFn_getElem

theorem ofFn_filteredMargin (xs : List ℕ) :
    List.ofFn (filteredMargin xs) = positiveMargins xs :=
  ofFn_listMargin (positiveMargins xs)

/-- Threshold one in the existing range/filter program retains precisely
the positive positions, in their original order. -/
def positiveIndices (xs : List ℕ) : List ℕ := largeIndices (1, xs)

lemma range_map_getD (xs : List ℕ) :
    (List.range xs.length).map (fun i => xs.getD i 0) = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simpa only [List.length_cons, List.range_succ_eq_map, List.map_cons,
      List.map_map, Function.comp_def, List.getD_cons_zero, List.getD_cons_succ] using
      congrArg (List.cons a) ih

theorem positiveMargins_eq_retained_map (xs : List ℕ) :
    positiveMargins xs = (positiveIndices xs).map (fun i => xs.getD i 0) := by
  have hp : (fun i => decide (0 < xs.getD i 0)) =
      (fun i => largeIndexTest ((1, xs), i)) := by
    funext i
    simp only [largeIndexTest, Nat.succ_le_iff]
  calc
    positiveMargins xs =
        ((List.range xs.length).map (fun i => xs.getD i 0)).filter
          (fun v => decide (0 < v)) := congrArg (positiveMargins) (range_map_getD xs).symm
    _ = _ := by
      rw [List.filter_map]
      change ((List.range xs.length).filter (fun i => decide (0 < xs.getD i 0))).map
        (fun i => xs.getD i 0) = _
      rw [hp]
      rfl

theorem positiveMargins_length (xs : List ℕ) :
    (positiveMargins xs).length = (positiveIndices xs).length := by
  simpa only [List.length_map] using congrArg List.length (positiveMargins_eq_retained_map xs)

theorem mem_positiveIndices (xs : List ℕ) (i : ℕ) :
    i ∈ positiveIndices xs ↔ i < xs.length ∧ 0 < xs.getD i 0 := by
  rw [positiveIndices, mem_largeIndices]
  omega

private def positiveMemberEquiv (xs : List ℕ) :
    {i // i ∈ positiveIndices xs} ≃ PositiveRows (listMargin xs) where
  toFun i := by
    have hi := (mem_positiveIndices xs i.val).mp i.property
    exact ⟨⟨i.val, hi.1⟩, by
      simpa only [listMargin, List.getElem_eq_getD 0] using hi.2⟩
  invFun i := ⟨i.val.val, (mem_positiveIndices xs i.val.val).mpr ⟨i.val.isLt, by
    simpa only [listMargin, List.getElem_eq_getD 0] using i.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Indexing the retained INDEX list, never the possibly repeated margin
values, supplies an explicit correspondence to positive original positions. -/
def positiveIndexEquiv (xs : List ℕ) :
    Fin (positiveMargins xs).length ≃ PositiveRows (listMargin xs) :=
  (finCongr (positiveMargins_length xs)).trans
    ((List.Nodup.getEquiv (positiveIndices xs) (largeIndices_nodup 1 xs)).trans
      (positiveMemberEquiv xs))

theorem positiveIndexEquiv_val (xs : List ℕ) (k : Fin (positiveMargins xs).length) :
    (positiveIndexEquiv xs k).val.val =
      (positiveIndices xs)[k.val]'(by rw [← positiveMargins_length xs]; exact k.isLt) := rfl

theorem positiveIndexEquiv_covers (xs : List ℕ) (i : PositiveRows (listMargin xs)) :
    positiveIndexEquiv xs ((positiveIndexEquiv xs).symm i) = i :=
  (positiveIndexEquiv xs).apply_symm_apply i

theorem positiveIndices_pairwise (xs : List ℕ) : (positiveIndices xs).Pairwise (· < ·) := by
  exact (List.pairwise_lt_range (n := xs.length)).filter _

theorem positiveIndexEquiv_strictMono (xs : List ℕ) :
    StrictMono (fun k => (positiveIndexEquiv xs k).val.val) := by
  intro i j hij
  change (positiveIndexEquiv xs i).val.val < (positiveIndexEquiv xs j).val.val
  rw [positiveIndexEquiv_val, positiveIndexEquiv_val]
  exact (positiveIndices_pairwise xs).rel_getElem_of_lt _ _ hij

/-- The kth filtered value is the original value at the kth retained
position; equality of values never identifies different list positions. -/
theorem filteredMargin_at_retained (xs : List ℕ) (k : Fin (positiveMargins xs).length) :
    filteredMargin xs k = listMargin xs (positiveIndexEquiv xs k).val := by
  have hk : k.val < (positiveIndices xs).length := by
    rw [← positiveMargins_length xs]
    exact k.isLt
  calc
    filteredMargin xs k = (positiveMargins xs).getD k.val 0 := List.getElem_eq_getD 0
    _ = ((positiveIndices xs).map (fun i => xs.getD i 0)).getD k.val 0 :=
      congrArg (fun l : List ℕ => l.getD k.val 0) (positiveMargins_eq_retained_map xs)
    _ = xs.getD ((positiveIndices xs)[k.val]'hk) 0 := by
      rw [List.getD_eq_getElem
        (l := (positiveIndices xs).map (fun i => xs.getD i 0)) (n := k.val) (d := 0)
        (by simpa only [List.length_map] using hk), List.getElem_map]
    _ = _ := by
      simp only [listMargin, List.getElem_eq_getD 0, positiveIndexEquiv_val]

theorem filteredMargin_positive (xs : List ℕ) (k : Fin (positiveMargins xs).length) :
    0 < filteredMargin xs k := by
  rw [filteredMargin_at_retained]
  exact (positiveIndexEquiv xs k).property

theorem positiveMargins_sum (xs : List ℕ) : (positiveMargins xs).sum = xs.sum := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    unfold positiveMargins at ih
    by_cases ha : 0 < a
    · simp [positiveMargins, ha, ih]
    · have hz : a = 0 := by omega
      subst a
      simp [positiveMargins, ih]

theorem filteredMargin_total (xs : List ℕ) :
    (∑ i, filteredMargin xs i) = ∑ i, listMargin xs i := by
  have hs : (List.ofFn (filteredMargin xs)).sum = (List.ofFn (listMargin xs)).sum := by
    rw [ofFn_filteredMargin, ofFn_listMargin]
    exact positiveMargins_sum xs
  simpa only [List.sum_ofFn] using hs

theorem filtered_totals_equal (xs ys : List ℕ)
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) :
    (∑ i, filteredMargin xs i) = ∑ j, filteredMargin ys j := by
  rw [filteredMargin_total, filteredMargin_total]
  exact htotal

/-- Margin relabelling changes only proofs, with the matrix left literal. -/
private def tableMarginCongr {A B : Type*} [Fintype A] [Fintype B]
    (r r' : A → ℕ) (c c' : B → ℕ)
    (hr : ∀ i, r i = r' i) (hc : ∀ j, c j = c' j) : Table r c ≃ Table r' c' where
  toFun X := ⟨X.val, (fun i => (X.property.1 i).trans (hr i)),
    fun j => (X.property.2 j).trans (hc j)⟩
  invFun X := ⟨X.val, (fun i => (X.property.1 i).trans (hr i).symm),
    fun j => (X.property.2 j).trans (hc j).symm⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

/-- Generic predicates keep the exact subtype finite instances of the
checked RestrictedTable alias before specialization to positive margins. -/
private def restrictedTableReindex {I J : Type*} [Fintype I] [Fintype J]
    (r : I → ℕ) (c : J → ℕ) (p : I → Prop) (q : J → Prop) {a b : ℕ}
    (eI : Fin a ≃ {i // p i}) (eJ : Fin b ≃ {j // q j}) :
    RestrictedTable r c p q ≃ Table (fun i => r (eI i).val) (fun j => c (eJ j).val) :=
  tableReindex eI eJ (fun i => r i.val) (fun j => c j.val)

def positiveTableListEquiv (xs ys : List ℕ) :
    PositiveTable (listMargin xs) (listMargin ys) ≃ Table (filteredMargin xs) (filteredMargin ys) :=
  (restrictedTableReindex (listMargin xs) (listMargin ys)
    (fun i => 0 < listMargin xs i) (fun j => 0 < listMargin ys j)
    (positiveIndexEquiv xs) (positiveIndexEquiv ys)).trans
    (tableMarginCongr _ _ _ _ (fun i => (filteredMargin_at_retained xs i).symm)
      (fun j => (filteredMargin_at_retained ys j).symm))

theorem positiveTableListEquiv_symm_entry (xs ys : List ℕ)
    (X : Table (filteredMargin xs) (filteredMargin ys))
    (i : PositiveRows (listMargin xs)) (j : PositiveColumns (listMargin ys)) :
    ((positiveTableListEquiv xs ys).symm X).val i j =
      X.val ((positiveIndexEquiv xs).symm i) ((positiveIndexEquiv ys).symm j) := rfl

def zeroMarginListEquiv (xs ys : List ℕ) :
    Table (listMargin xs) (listMargin ys) ≃ Table (filteredMargin xs) (filteredMargin ys) :=
  (zeroMarginEquiv (listMargin xs) (listMargin ys)).trans (positiveTableListEquiv xs ys)

theorem zeroMarginListEquiv_restrict_entry (xs ys : List ℕ)
    (X : Table (listMargin xs) (listMargin ys))
    (i : Fin (positiveMargins xs).length) (j : Fin (positiveMargins ys).length) :
    (zeroMarginListEquiv xs ys X).val i j =
      X.val (positiveIndexEquiv xs i).val (positiveIndexEquiv ys j).val := rfl

theorem zeroMarginListEquiv_extend_entry (xs ys : List ℕ)
    (X : Table (filteredMargin xs) (filteredMargin ys)) (i : Fin xs.length) (j : Fin ys.length) :
    ((zeroMarginListEquiv xs ys).symm X).val i j =
      if hi : 0 < listMargin xs i then if hj : 0 < listMargin ys j then
        X.val ((positiveIndexEquiv xs).symm ⟨i, hi⟩) ((positiveIndexEquiv ys).symm ⟨j, hj⟩)
      else 0 else 0 := by
  change ((zeroMarginEquiv (listMargin xs) (listMargin ys)).symm
    ((positiveTableListEquiv xs ys).symm X)).val i j = _
  simpa only [positiveTableListEquiv_symm_entry] using
    zeroMarginEquiv_extend_entry (listMargin xs) (listMargin ys)
      ((positiveTableListEquiv xs ys).symm X) i j

def restoreZeroMarginListsLaw (xs ys : List ℕ)
    (q : RationalLaw (Table (filteredMargin xs) (filteredMargin ys))) :
    RationalLaw (Table (listMargin xs) (listMargin ys)) :=
  equivLaw (zeroMarginListEquiv xs ys).symm q

theorem restoreZeroMarginListsLaw_variation (xs ys : List ℕ)
    (q q' : RationalLaw (Table (filteredMargin xs) (filteredMargin ys))) :
    variation (restoreZeroMarginListsLaw xs ys q) (restoreZeroMarginListsLaw xs ys q') =
      variation q q' :=
  variation_equiv (zeroMarginListEquiv xs ys).symm q q'

theorem restoreZeroMarginListsLaw_uniform (xs ys : List ℕ)
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j) :
    letI := table_nonempty (listMargin xs) (listMargin ys) htotal
    letI := table_nonempty (filteredMargin xs) (filteredMargin ys) (filtered_totals_equal xs ys htotal)
    restoreZeroMarginListsLaw xs ys (uniformLaw (α := Table (filteredMargin xs) (filteredMargin ys))) =
      uniformLaw (α := Table (listMargin xs) (listMargin ys)) := by
  letI := table_nonempty (listMargin xs) (listMargin ys) htotal
  letI := table_nonempty (filteredMargin xs) (filteredMargin ys) (filtered_totals_equal xs ys htotal)
  exact uniform_equiv (zeroMarginListEquiv xs ys).symm

theorem restoreZeroMarginListsLaw_uniform_variation (xs ys : List ℕ)
    (htotal : (∑ i, listMargin xs i) = ∑ j, listMargin ys j)
    (q : RationalLaw (Table (filteredMargin xs) (filteredMargin ys))) :
    letI := table_nonempty (listMargin xs) (listMargin ys) htotal
    letI := table_nonempty (filteredMargin xs) (filteredMargin ys) (filtered_totals_equal xs ys htotal)
    variation (restoreZeroMarginListsLaw xs ys q)
        (uniformLaw (α := Table (listMargin xs) (listMargin ys))) =
      variation q (uniformLaw (α := Table (filteredMargin xs) (filteredMargin ys))) := by
  letI := table_nonempty (listMargin xs) (listMargin ys) htotal
  letI := table_nonempty (filteredMargin xs) (filteredMargin ys) (filtered_totals_equal xs ys htotal)
  rw [← restoreZeroMarginListsLaw_uniform xs ys htotal]
  exact restoreZeroMarginListsLaw_variation xs ys q _

end
end Math115.PhysicalTraceJoin
