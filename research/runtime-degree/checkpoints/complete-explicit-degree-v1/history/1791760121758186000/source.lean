import ResearchBounds.DrawAssemblyDegree
import CountBounds.TightWordCountDegreeV2
import PrinterRuntime.PrinterDegree
import InitialRuntime.InitialDegree
import UnitRuntime.UnitPackedTrialDegree
import RetryRuntime.ActualRetryWordsDegree
import DrawRuntime.BranchDegree

namespace Math115.CompleteDrawNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds Math115.DrawDegree
noncomputable section

/-- Largest already closed draw-field degree before the reference field. -/
def unitTrialDegree : ℕ := 272019144737569436269241336269647035188617216
/-- One common degree suffices for the fixed assembly record. -/
def seamDegree (referenceDegree : ℕ) : ℕ := max unitTrialDegree referenceDegree
/-- Existing exact publicDraw assembly, retaining retries, branches, fallback
and final printing. This is a conservative upper-bound formula. -/
def drawDegree (referenceDegree : ℕ) : ℕ :=
  let k := seamDegree referenceDegree
  8*(1+k*(k+1))*k^5

lemma typed_actual_schedule : Typed Math115.LatticeScheduleProgram.scheduleRealizer 1008 :=
  (Math115.TightCountDegreeV2.circuit_schedule 1008 (by decide)
    Math115.CatalogueDegreeV1.typed_smallCellCatalog (by decide)).1

/-- Every original field is closed except the explicit reference packed-trial
hypothesis. No alternate realizer or restricted input domain is introduced. -/
lemma actual_seams_of_reference {r : ℕ}
    (hReference : Typed Math115.LatticeOuterProgram.packedTrialRealizer r) :
    ActualDrawSeams (seamDegree r) := by
  have hU : unitTrialDegree ≤ seamDegree r := Nat.le_max_left _ _
  have hR : r ≤ seamDegree r := Nat.le_max_right _ _
  have hpos : 1≤seamDegree r := (by decide : 1≤unitTrialDegree).trans hU
  have hlower (a : ℕ) (ha : a≤unitTrialDegree) : a≤seamDegree r := ha.trans hU
  exact {
    positive := hpos
    parser := typed_weaken Math115.ParserDegreeV1.typed_parsedSampling (hlower 16 (by decide))
    printer := typed_weaken Math115.PrinterRuntimeNext.typed_actual_printMatrix (hlower 4 (by decide))
    schedule := typed_weaken typed_actual_schedule (hlower 1008 (by decide))
    initial := typed_weaken Math115.InitialRuntimeNext.typed_actual_initialConfiguration (hlower 4032 (by decide))
    fallback := typed_weaken Math115.InitialRuntimeNext.typed_actual_initialFallback (hlower 18 (by decide))
    branch := typed_weaken Math115.DrawRuntimeNext.typed_actual_bothLargeTest (hlower 1008 (by decide))
    referenceTrial := typed_weaken hReference hR
    unitTrial := typed_weaken Math115.UnitRuntimeNext.typed_actual_unitPackedTrial hU
    retryWords := typed_weaken Math115.RetryRuntimeNext.typed_actual_retryWords (hlower 42914304 (by decide))
  }

/-- Conditional only on the one explicitly exposed reference field. The final
module will close it with the owner's exact concrete certificate. -/
theorem typed_publicDraw_of_reference {r : ℕ}
    (hReference : Typed Math115.LatticeOuterProgram.packedTrialRealizer r) :
    Typed Math115.PublicLatticeSampler.publicDrawRealizer (drawDegree r) :=
  typed_publicDraw_of_actual_seams (actual_seams_of_reference hReference)

end
end Math115.CompleteDrawNext
