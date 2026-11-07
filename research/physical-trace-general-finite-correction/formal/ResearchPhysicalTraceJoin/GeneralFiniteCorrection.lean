/-
SPDX-License-Identifier: Apache-2.0
Typed bounded-bit correction of the actual partial repair, using the literal
ordered-list inverse counter on ordinary table codes. This wrapper is not
an encoded full program or an initialization/retry theorem.
-/
import ResearchPhysicalTraceJoin.GeneralListedCount
import ResearchPhysicalTraceJoin.GeneralBoundedCoin

set_option maxHeartbeats 800000

namespace Math115.PhysicalTraceJoin

open OAI OAI.ContingencyTables OAI.CommonBasesFPRAS
open ProfilePrograms DensePrograms SmallGraphProfiles FirstPaperProfiles
open CompletionCounts PhysicalCompletionFibres SmallContextCoordinates
open SmallContextFibres PaddedCompletions FirstSuccess ResidualMixture
open Math115.ReducedSmallChain Math115.PhysicalDefectTrace
open Math115.PhysicalStationarySuccess

variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ) (U L : ℕ)

/-- An ordinary list counter evaluated on the existing ordinary table code. -/
def terminalListedCount (X : Table r c) : ℕ :=
  listedInverseCount (List.ofFn r) (List.ofFn c) U (matrixCode X.val)

noncomputable section
open scoped BigOperators Classical

/-- The actual padding failure remains none. A successful ordinary output
uses the existing threshold/decoder on one fresh reserved k-bit bank. -/
def terminalBitCorrection (k : ℕ) (a : DefectJoint r c U L)
    (bits : Fin k → Bool) : Option (Table r c) :=
  partialBitTerminal (terminalPartialRepair r c U L a) (terminalListedCount r c U)
    k (inverseSupportAllowance r c U) bits

def terminalFiniteCorrectionRow (k : ℕ) (a : DefectJoint r c U L) :
    RationalLaw (Option (Table r c)) :=
  mapLaw (uniformLaw (α := Fin k → Bool)) (terminalBitCorrection r c U L k a)

lemma terminalListedCount_eq_terminalInverseCount (hL : 1 ≤ L) (X : Table r c) :
    terminalListedCount r c U X = terminalInverseCount r c U L X :=
  listedInverseCount_eq_terminalInverseCount r c U L hL X

/-- The error is on the entire Option-valued row, before conditioning or
retries, and the inverse count is discharged by the actual list counter. -/
theorem terminalFiniteCorrectionRow_variation (hL : 1 ≤ L) (k : ℕ)
    (a : DefectJoint r c U L) :
    variation (terminalFiniteCorrectionRow r c U L k a)
      (terminalIdealCorrectionRow r c U L (inverseSupportAllowance r c U) a) ≤
        1 / (2 : ℚ)^k :=
  PartialRepairCorrection.finiteRow_variation
    (terminalPartialRepair r c U L) (terminalListedCount r c U)
    (fun X => terminalListedCount_eq_terminalInverseCount r c U L hL X)
    k (inverseSupportAllowance r c U) a

/-- Endpoint error and one bounded correction coin are added before any
successful-output conditioning. Both endpoint laws are actual joint laws. -/
theorem terminalFiniteCorrectionRow_bind_variation (hL : 1 ≤ L) (k : ℕ)
    (p q : RationalLaw (DefectJoint r c U L)) :
    variation (bindLaw p (terminalFiniteCorrectionRow r c U L k))
      (bindLaw q (terminalIdealCorrectionRow r c U L (inverseSupportAllowance r c U))) ≤
        variation p q + 1 / (2 : ℚ)^k :=
  PartialRepairCorrection.finiteRow_bind_variation
    (terminalPartialRepair r c U L) (terminalListedCount r c U)
    (fun X => terminalListedCount_eq_terminalInverseCount r c U L hL X)
    k (inverseSupportAllowance r c U) p q

end
end Math115.PhysicalTraceJoin
