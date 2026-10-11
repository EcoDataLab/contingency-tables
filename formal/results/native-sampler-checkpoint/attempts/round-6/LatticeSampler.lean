/-
SPDX-License-Identifier: Apache-2.0
One encoded ideal-scale sampler: compute the schedule and initial configuration,
select the actual reference or empty-block branch, then consume a reserved
Boolean word. Supplied-word polynomial cost and reserved-bit bounds are stated
separately; no explicit full machine-time exponent is asserted here.
-/
import Math115.LatticeUnitOuter
import Math115.LatticeScheduleProgram

namespace Math115.LatticeSampler

open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped
open ProfilePrograms DensePrograms

abbrev Input := LatticeScheduleProgram.ScheduleInput × List Bool
abbrev PreparedInput := LatticeSamplerPreparation.Margins × LatticeScheduleProgram.ScheduleOutput

def trialParameters (z : PreparedInput) : LatticeOuterProgram.TrialParameters :=
  ((LatticeSamplerPreparation.initialConfiguration (z.1, z.2.2), z.2.1.1.1), z.2.1.1.2)

def trialParametersRealizer : Realizer trialParameters :=
  pair (pair (composition (pair first (composition second second))
    LatticeSamplerPreparation.initialConfigurationRealizer)
    (composition (composition (composition second first) first) first))
    (composition (composition (composition second first) first) second)

theorem polynomial_trialParameters : PolynomialTime trialParametersRealizer :=
  polynomial_pair (polynomial_pair (polynomial_composition
    (polynomial_pair polynomial_first (polynomial_composition polynomial_second polynomial_second))
    LatticeSamplerPreparation.polynomial_initialConfiguration)
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_second polynomial_first) polynomial_first) polynomial_first))
    (polynomial_composition (polynomial_composition
      (polynomial_composition polynomial_second polynomial_first) polynomial_first) polynomial_second)

def assembleParameters (z : PreparedInput) : LatticeOuterProgram.RetryParameters :=
  ((trialParameters z, LatticeSamplerPreparation.initialFallback z.1), z.2.1.2)

def assembleParametersRealizer : Realizer assembleParameters :=
  pair (pair trialParametersRealizer
    (composition first LatticeSamplerPreparation.initialFallbackRealizer))
    (composition (composition second first) second)

theorem polynomial_assembleParameters : PolynomialTime assembleParametersRealizer :=
  polynomial_pair (polynomial_pair polynomial_trialParameters
    (polynomial_composition polynomial_first LatticeSamplerPreparation.polynomial_initialFallback))
    (polynomial_composition (polynomial_composition polynomial_second polynomial_first) polynomial_second)

def prepare (z : LatticeScheduleProgram.ScheduleInput) : LatticeOuterProgram.RetryParameters :=
  assembleParameters (z.1, LatticeScheduleProgram.schedule z)

def prepareRealizer : Realizer prepare :=
  composition (pair first LatticeScheduleProgram.scheduleRealizer) assembleParametersRealizer

theorem polynomial_prepare : PolynomialTime prepareRealizer :=
  polynomial_composition (polynomial_pair polynomial_first LatticeScheduleProgram.polynomial_schedule)
    polynomial_assembleParameters

/-- A total ordinary list function, with all choices computed from its input. -/
def draw (z : Input) : MatrixCode :=
  if LatticeSamplerPreparation.bothLargeTest z.1.1 then
    LatticeOuterProgram.retry (prepare z.1, z.2)
  else LatticeUnitOuter.retry (prepare z.1, z.2)

def drawRealizer : Realizer draw :=
  (choose (composition (composition first first) LatticeSamplerPreparation.bothLargeTestRealizer)
    (composition (pair (composition first prepareRealizer) second) LatticeOuterProgram.retryRealizer)
    (composition (pair (composition first prepareRealizer) second) LatticeUnitOuter.retryRealizer)).congr
      (by intro z; rfl)

/-- Polynomial tree-machine time includes the supplied Boolean bank as input.
The next theorem bounds that bank separately; d^17 is the gap allowance. -/
theorem polynomial_draw : PolynomialTime drawRealizer :=
  polynomial_congr _ (polynomial_choose
    (polynomial_composition (polynomial_composition polynomial_first polynomial_first)
      LatticeSamplerPreparation.polynomial_bothLargeTest)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_prepare) polynomial_second)
      LatticeOuterProgram.polynomial_retry)
    (polynomial_composition (polynomial_pair
      (polynomial_composition polynomial_first polynomial_prepare) polynomial_second)
      LatticeUnitOuter.polynomial_retry))

open OAI.CommonBasesFPRAS SmallGraphProfiles CompletionCounts ReducedSmallChain
open PhysicalCompletionOracle FirstSuccess FairBits
open scoped BigOperators Classical
noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => dimensionAllowance (I := Fin m) (J := Fin n)
local notation "p" => CompletionOuterSchedule.physicalSmallCount r c
local notation "base" => CompletionOuterSchedule.physicalMassBase (J := Fin n) r
local notation "T" => CompletionOuterSchedule.walkCount p d base
local notation "R" => CompletionOuterSchedule.restartCount p
local notation "hS" => CompletionOuterSchedule.stepPrecision p d base
local notation "hT" => CompletionOuterSchedule.terminalPrecision p

/-- The ordinary list program returns the exact encoded table of the proved
two-branch experiment, for every reserved word, including zero margins. -/
theorem draw_code (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ)
    (bits : Fin (PhysicalReferenceBoolean.outerBits (n := n) r (T h) (R h) (hS h) (hT h)) → Bool) :
    draw (((List.ofFn r, List.ofFn c), h), List.ofFn bits) =
      matrixCode (PhysicalBooleanSampler.draw r c htotal (T h) (R h) (hS h) (hT h) bits).val := by
  have hbranch := LatticeSamplerPreparation.bothLargeTest_code r c
  by_cases hb : PhysicalBooleanSampler.bothLarge r c
  · unfold draw
    rw [if_pos (hbranch.mpr hb)]
    unfold prepare assembleParameters trialParameters
    rw [LatticeScheduleProgram.schedule_ofFn]
    change LatticeOuterProgram.retry _ = _
    rw [LatticeOuterSemantics.initialized_retry_code r c hb.1 hb.2 htotal]
    simp only [PhysicalBooleanSampler.draw, dif_pos hb]
  · unfold draw
    rw [if_neg (fun htest => hb (hbranch.mp htest))]
    unfold prepare assembleParameters trialParameters
    rw [LatticeScheduleProgram.schedule_ofFn]
    change LatticeUnitOuter.retry _ = _
    rw [LatticeUnitOuter.initialized_retry_code r c htotal hb]
    simp only [PhysicalBooleanSampler.draw, dif_neg hb]

/-- The exact computed word requirement obeys the separated polynomial bound. -/
theorem reservedBits_separated (h : ℕ) :
    LatticeScheduleProgram.totalBits ((List.ofFn r, List.ofFn c), h) ≤
      CompletionRandomBudget.budgetCoefficient * d^20 * (h + 3) *
        (CompletionRandomBudget.combinedSize d (∑ i, r i) h)^64 := by
  rw [LatticeScheduleProgram.totalBits_ofFn_budget]
  exact CompletionRandomBudget.physicalTotalReservedBits_separated r c h

theorem reservedBits_combined (h : ℕ) :
    LatticeScheduleProgram.totalBits ((List.ofFn r, List.ofFn c), h) ≤
      CompletionRandomBudget.budgetCoefficient *
        (CompletionRandomBudget.combinedSize d (∑ i, r i) h)^85 := by
  rw [LatticeScheduleProgram.totalBits_ofFn_budget]
  exact CompletionRandomBudget.physicalTotalReservedBits_combined r c h

/-- Explicit contract connecting the executable program to feasible tables
and their distribution, using its own computed number of reserved fair bits. -/
theorem draw_spec (htotal : ∑ i, r i = ∑ j, c j) (h : ℕ) :
    let q := LatticeScheduleProgram.totalBits ((List.ofFn r, List.ofFn c), h)
    letI := OAI.ContingencyTables.table_nonempty r c htotal
    ∃ f : (Fin q → Bool) → Table r c,
      (∀ bits, draw (((List.ofFn r, List.ofFn c), h), List.ofFn bits) = matrixCode (f bits).val) ∧
      (variation (mapLaw (uniformLaw (α := Fin q → Bool)) f)
        (uniformLaw (α := Table r c)) : ℝ) ≤ (CompletionRetryBudget.dyadic h : ℝ) := by
  dsimp only
  rw [LatticeScheduleProgram.totalBits_ofFn]
  letI := OAI.ContingencyTables.table_nonempty r c htotal
  refine ⟨PhysicalBooleanSampler.draw r c htotal (T h) (R h) (hS h) (hT h), ?_, ?_⟩
  · exact draw_code r c htotal h
  · exact PhysicalBooleanSampler.draw_explicit_accuracy r c htotal h

end
end Math115.LatticeSampler
