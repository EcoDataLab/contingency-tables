/-
SPDX-License-Identifier: Apache-2.0
Executable coarse-margin request and frozen completion draw on raw profile
codes at free scales. Correspondence retains the actual residual block.
No new completion oracle, random source, or runtime theorem is introduced.
-/
import ResearchPhysicalTraceJoin.GeneralJointCode
import OAI.Combinatorics.ContingencyTables.Machines.BinVectorProgram

set_option maxHeartbeats 800000
namespace Math115.PhysicalTraceJoin
open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles FirstPaperProfiles CompletionCounts
open PhysicalCompletionFibres FirstPaperPhysicalMarginal SmallContextCoordinates
open SmallContextFibres PaddedCompletions FirstSuccess ResidualMixture
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace Math115.PhysicalComputedProposal
open Math115.LegacyPhysicalCompletion Math115.PhysicalCompletionWidth
open scoped BigOperators

/-- Exact existing large-line order and row residual/padding arithmetic. -/
def rawCoarseRows (rs cs : List ℕ) (U L : ℕ) (state : List ℕ × List ℕ) : List ℕ :=
  largePaddedMargins true (((((smallCellCatalog ((rs,cs),U),state.1),(rs,cs)),U),L))

/-- The profile's second list is a complement view, so complementValues is
applied before forming physical column residual margins. -/
def rawCoarseColumns (rs cs : List ℕ) (U L : ℕ) (state : List ℕ × List ℕ) : List ℕ :=
  largePaddedMargins false
    (((((smallCellCatalog ((rs,cs),U),complementValues (U,state.2)),(rs,cs)),U),L))

def rawCoarseMargins (rs cs : List ℕ) (U L : ℕ) (state : List ℕ × List ℕ) :
    List ℕ × List ℕ := (rawCoarseRows rs cs U L state,rawCoarseColumns rs cs U L state)

def rawCompletionBits (rs cs : List ℕ) (U L : ℕ) (state : List ℕ × List ℕ) (h : ℕ) : ℕ :=
  LatticeScheduleProgram.totalBits (rawCoarseMargins rs cs U L state,h)

/-- The original frozen draw receives only computed list margins and the
needed prefix of the supplied reserved word. No typed completion is supplied. -/
def rawCompletionResidual (rs cs : List ℕ) (U L : ℕ) (state : List ℕ × List ℕ)
    (h : ℕ) (word : List Bool) : MatrixCode :=
  Math115.LatticeSampler.draw ((rawCoarseMargins rs cs U L state,h),
    word.take (rawCompletionBits rs cs U L state h))

def rawCompletionSource (rs cs : List ℕ) (U L : ℕ) (state : List ℕ × List ℕ)
    (h : ℕ) (word : List Bool) : MatrixCode :=
  jointSourceMatrixCode rs cs U state (rawCompletionResidual rs cs U L state h word)

open scoped Classical
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)
variable (hr : 0 < (largeIndices (U,List.ofFn r)).length)
variable (hc : 0 < (largeIndices (U,List.ofFn c)).length)

lemma rawCoarseRows_eq (z : States r c U L) :
    rawCoarseRows (List.ofFn r) (List.ofFn c) U L (computedStateCode r c U L z) =
      List.ofFn (coarseRows r c U L hr z) := by
  have he := coarseRows_code r c U L hr (computedCellEquiv r c U) z
  rw [computedCellEquiv_catalog] at he
  simpa only [rawCoarseRows, computedStateCode, Math115.PhysicalComputedProposal.stateCode,
    profileCode, computedCatalog] using he.symm

lemma rawCoarseColumns_eq (z : States r c U L) :
    rawCoarseColumns (List.ofFn r) (List.ofFn c) U L (computedStateCode r c U L z) =
      List.ofFn (coarseColumns r c U L hc z) := by
  have he := coarseColumns_code r c U L hc (computedCellEquiv r c U) z
  rw [computedCellEquiv_catalog] at he
  simpa only [rawCoarseColumns, computedStateCode, Math115.PhysicalComputedProposal.stateCode,
    profileCode, computedCatalog] using he.symm

theorem rawCoarseMargins_eq (z : States r c U L) :
    rawCoarseMargins (List.ofFn r) (List.ofFn c) U L (computedStateCode r c U L z) =
      (List.ofFn (coarseRows r c U L hr z),List.ofFn (coarseColumns r c U L hc z)) :=
  Prod.ext (rawCoarseRows_eq r c U L hr z) (rawCoarseColumns_eq r c U L hc z)

lemma rawCoarseRows_length (z : States r c U L) :
    (rawCoarseRows (List.ofFn r) (List.ofFn c) U L (computedStateCode r c U L z)).length =
      (largeIndices (U,List.ofFn r)).length := by
  rw [rawCoarseRows_eq r c U L hr z, List.length_ofFn]
  unfold tailCount
  omega

lemma rawCoarseColumns_length (z : States r c U L) :
    (rawCoarseColumns (List.ofFn r) (List.ofFn c) U L (computedStateCode r c U L z)).length =
      (largeIndices (U,List.ofFn c)).length := by
  rw [rawCoarseColumns_eq r c U L hc z, List.length_ofFn]
  unfold tailCount
  omega

theorem rawCompletionBits_eq (z : States r c U L) (h : ℕ) :
    rawCompletionBits (List.ofFn r) (List.ofFn c) U L (computedStateCode r c U L z) h =
      bits r c U L hr hc z h := by
  unfold rawCompletionBits bits
  rw [rawCoarseMargins_eq r c U L hr hc z]

/-- Any sufficiently long input word yields exactly the residual of the
actual inherited completion on its existing reserved prefix. -/
theorem rawCompletionResidual_eq (z : States r c U L) (h N : ℕ)
    (hN : bits r c U L hr hc z h ≤ N) (word : Fin N → Bool) :
    rawCompletionResidual (List.ofFn r) (List.ofFn c) U L (computedStateCode r c U L z)
      h (List.ofFn word) = matrixCode ((finiteFibreEquiv r c U L hr hc z)
        (completionDraw r c U L hr hc z h (prefixWord hN word))).val := by
  unfold rawCompletionResidual
  rw [rawCoarseMargins_eq r c U L hr hc z,rawCompletionBits_eq r c U L hr hc z h,
    BinVectorProgram.take_ofFn_prefix hN word]
  exact completionDraw_code r c U L hr hc z h _

/-- Fresh terminal completion is now identified from raw profile and word
codes, with no semantic residual matrix among the program inputs. -/
theorem rawCompletionResidual_terminal (d : DefectVertices r c U L) (h : ℕ)
    (word : Fin (uniformCompletionBits r c U L h) → Bool) :
    rawCompletionResidual (List.ofFn r) (List.ofFn c) U L (computedStateCode r c U L d.val)
      h (List.ofFn word) = jointResidualMatrixCode r c U L hr hc
        ⟨d,terminalCompletion r c U L hr hc d h word⟩ := by
  rw [jointResidualMatrixCode_eq]
  exact rawCompletionResidual_eq r c U L hr hc d.val h _
    (completionBits_le_uniform r c U L hr hc d.val h) word

theorem rawCompletionSource_terminal (d : DefectVertices r c U L) (h : ℕ)
    (word : Fin (uniformCompletionBits r c U L h) → Bool) :
    rawCompletionSource (List.ofFn r) (List.ofFn c) U L (computedStateCode r c U L d.val)
      h (List.ofFn word) = terminalSourceMatrixCode r c U L
        ⟨d,terminalCompletion r c U L hr hc d h word⟩ := by
  unfold rawCompletionSource
  rw [rawCompletionResidual_terminal r c U L hr hc d h word]
  exact jointSourceMatrixCode_eq r c U L hr hc _

end
end Math115.PhysicalTraceJoin
