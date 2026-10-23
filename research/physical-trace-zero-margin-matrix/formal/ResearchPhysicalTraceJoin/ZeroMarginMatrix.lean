/-
SPDX-License-Identifier: Apache-2.0
Literal matrix-list zero reinsertion through retained-index ranks. On an
actual reduced-table code this agrees with the checked table restoration
equivalence. Defaults make the function total on all matrix lists; no
feasibility or accuracy is claimed for malformed input codes. No encoded
realizer, polynomial-time bound, or sampler branch is supplied.
-/
import ResearchPhysicalTraceJoin.ZeroMarginLists
import OAI.Combinatorics.ContingencyTables.Dense.DenseIntegerProgram

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables
open ProfilePrograms SmallGraphProfiles CompletionCounts

/-- Position in the computed retained-index list. Absent positions have
the usual idxOf default; their matrix entries are discarded by the guard. -/
def retainedRank (xs : List ℕ) (i : ℕ) : ℕ := (largeIndices (1, xs)).idxOf i

/-- An ordinary list program with no table equivalence in its definition.
Only positive original row/column pairs read the supplied reduced code. -/
def restoreZeroMarginMatrix (xs ys : List ℕ) (A : DensePrograms.MatrixCode) :
    DensePrograms.MatrixCode :=
  DensePrograms.matrixCode (fun i : Fin xs.length => fun j : Fin ys.length =>
    if 0 < xs.getD i.val 0 then if 0 < ys.getD j.val 0 then
      DensePrograms.matrixEntry (A, (retainedRank xs i.val, retainedRank ys j.val))
    else 0 else 0)

open scoped Classical
noncomputable section

lemma listMargin_eq_getD (xs : List ℕ) (i : Fin xs.length) :
    listMargin xs i = xs.getD i.val 0 := List.getElem_eq_getD 0

/-- The executable rank is exactly the inverse of the ordered retained
correspondence. The proof uses its public entry/coverage laws only. -/
theorem retainedRank_at_positive (xs : List ℕ) (i : PositiveRows (listMargin xs)) :
    retainedRank xs i.val.val = ((positiveIndexEquiv xs).symm i).val := by
  let k := (positiveIndexEquiv xs).symm i
  have hk : k.val < (positiveIndices xs).length := by
    rw [← positiveMargins_length xs]
    exact k.isLt
  have hget : (positiveIndices xs)[k.val]'hk = i.val.val := by
    calc
      _ = (positiveIndexEquiv xs k).val.val := (positiveIndexEquiv_val xs k).symm
      _ = i.val.val := congrArg (fun z : PositiveRows (listMargin xs) => z.val.val)
        ((positiveIndexEquiv xs).apply_symm_apply i)
  change (positiveIndices xs).idxOf i.val.val = k.val
  rw [← hget]
  exact (largeIndices_nodup 1 xs).idxOf_getElem k.val hk

theorem retainedRank_lt_filtered_length (xs : List ℕ)
    (i : PositiveRows (listMargin xs)) : retainedRank xs i.val.val < (positiveMargins xs).length := by
  rw [retainedRank_at_positive]
  exact ((positiveIndexEquiv xs).symm i).isLt

theorem restoreZeroMarginMatrix_length (xs ys : List ℕ) (A : DensePrograms.MatrixCode) :
    (restoreZeroMarginMatrix xs ys A).length = xs.length := by
  simp only [restoreZeroMarginMatrix, DensePrograms.matrixCode, List.length_ofFn]

theorem restoreZeroMarginMatrix_row_length (xs ys : List ℕ) (A : DensePrograms.MatrixCode)
    (i : Fin xs.length) :
    ((restoreZeroMarginMatrix xs ys A)[i.val]'(by
      rw [restoreZeroMarginMatrix_length]; exact i.isLt)).length = ys.length := by
  simp only [restoreZeroMarginMatrix, DensePrograms.matrixCode,
    List.getElem_ofFn, List.length_ofFn]

/-- For every actual filtered table, literal list reinsertion returns
exactly the code of its checked zero-extension. No law premise is used. -/
theorem restoreZeroMarginMatrix_code (xs ys : List ℕ)
    (X : Table (filteredMargin xs) (filteredMargin ys)) :
    restoreZeroMarginMatrix xs ys (DensePrograms.matrixCode X.val) =
      DensePrograms.matrixCode (((zeroMarginListEquiv xs ys).symm X).val) := by
  unfold restoreZeroMarginMatrix
  apply congrArg (DensePrograms.matrixCode (m := xs.length) (n := ys.length))
  funext i j
  change (if 0 < xs.getD i.val 0 then if 0 < ys.getD j.val 0 then
      DensePrograms.matrixEntry (DensePrograms.matrixCode X.val,
        (retainedRank xs i.val, retainedRank ys j.val)) else 0 else 0) =
    ((zeroMarginListEquiv xs ys).symm X).val i j
  rw [zeroMarginListEquiv_extend_entry]
  rw [← listMargin_eq_getD xs i, ← listMargin_eq_getD ys j]
  by_cases hi : 0 < listMargin xs i
  · by_cases hj : 0 < listMargin ys j
    · simp only [hi, hj, ite_true, dite_true]
      rw [retainedRank_at_positive xs ⟨i, hi⟩, retainedRank_at_positive ys ⟨j, hj⟩]
      exact DensePrograms.matrixEntry_code X.val
        ((positiveIndexEquiv xs).symm ⟨i, hi⟩) ((positiveIndexEquiv ys).symm ⟨j, hj⟩)
    · simp only [hi, hj, ite_true, ite_false, dite_true, dite_false]
  · simp only [hi, ite_false, dite_false]

end
end Math115.PhysicalTraceJoin
