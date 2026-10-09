/-
SPDX-License-Identifier: Apache-2.0
Total binary-list computation of the ideal-scale physical schedule and reserved
word widths. Fixed powers are arithmetic circuits of fixed program size.
The schedule produces numbers; it never allocates a list of T or R elements.
This source-only draft neither recompiles nor changes the frozen baseline.
-/
import Math115.CompletionRandomBudget
import Math115.PhysicalReferenceBoolean
import OAI.Combinatorics.ContingencyTables.Sampling.ProfileWordProgram
import OAI.Combinatorics.ContingencyTables.Dense.DenseWordProgram
import OAI.Combinatorics.MatchingCount.Complexity.TreePolynomialSums

namespace Math115.LatticeScheduleProgram
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped
open ProfilePrograms DensePrograms
open scoped BigOperators

abbrev Margins := List ℕ × List ℕ
abbrev ScheduleInput := Margins × ℕ
/-- (((step schedule, terminal precision/width), restart count), init precision). -/
abbrev ScheduleOutput := ((ProfileWordSchedule × (ℕ × ℕ)) × ℕ) × ℕ

/-- A fixed exponent is part of the program syntax, not a binary input loop. -/
def fixedPowerRealizer : (k : ℕ) → Realizer (fun x : ℕ => x^k)
  | 0 => constant 1
  | k + 1 => (composition (pair (fixedPowerRealizer k) identity) multiply).congr
      (by intro x; simp only [Function.comp_apply, id_eq, pow_succ])

lemma polynomial_fixedPower (k : ℕ) : PolynomialTime (fixedPowerRealizer k) := by
  induction k with
  | zero => exact polynomial_constant 1
  | succ k ih => exact polynomial_congr _ (polynomial_composition
      (polynomial_pair ih polynomial_identity) polynomial_multiply)

def addGet {f g : ScheduleInput → ℕ} (F : Realizer f) (G : Realizer g) :
    Realizer (fun z => f z + g z) := composition (pair F G) add
lemma polynomial_addGet {f g : ScheduleInput → ℕ} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (addGet F G) :=
  polynomial_composition (polynomial_pair hF hG) polynomial_add

def mulGet {f g : ScheduleInput → ℕ} (F : Realizer f) (G : Realizer g) :
    Realizer (fun z => f z * g z) := composition (pair F G) multiply
lemma polynomial_mulGet {f g : ScheduleInput → ℕ} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (mulGet F G) :=
  polynomial_composition (polynomial_pair hF hG) polynomial_multiply

def powerGet {f : ScheduleInput → ℕ} (F : Realizer f) (k : ℕ) :
    Realizer (fun z => (f z)^k) := composition F (fixedPowerRealizer k)
lemma polynomial_powerGet {f : ScheduleInput → ℕ} {F : Realizer f}
    (hF : PolynomialTime F) (k : ℕ) : PolynomialTime (powerGet F k) :=
  polynomial_composition hF (polynomial_fixedPower k)

def logGet {f : ScheduleInput → ℕ} (F : Realizer f) :
    Realizer (fun z => Nat.clog 2 (f z)) := composition F ceilLogTwoRealizer
lemma polynomial_logGet {f : ScheduleInput → ℕ} {F : Realizer f}
    (hF : PolynomialTime F) : PolynomialTime (logGet F) :=
  polynomial_composition hF polynomial_ceilLogTwo

def target (z : ScheduleInput) : ℕ := z.2
def targetRealizer : Realizer target := second
lemma polynomial_target : PolynomialTime targetRealizer := polynomial_second

def dimension (z : ScheduleInput) : ℕ := marginDimension z.1
def dimensionRealizer : Realizer dimension := composition first marginDimensionRealizer
lemma polynomial_dimension : PolynomialTime dimensionRealizer :=
  polynomial_composition polynomial_first polynomial_marginDimension

def cutoff (z : ScheduleInput) : ℕ := PhysicalComputedProposal.idealMarginThreshold z.1
def cutoffRealizer : Realizer cutoff :=
  composition first PhysicalComputedProposal.idealMarginThresholdRealizer
lemma polynomial_cutoff : PolynomialTime cutoffRealizer :=
  polynomial_composition polynomial_first PhysicalComputedProposal.polynomial_idealMarginThreshold

/-- Actual computed small-cell catalogue length, using the ideal cutoff 5d^3. -/
def smallCount (z : ScheduleInput) : ℕ :=
  (PhysicalComputedProposal.idealMarginCatalog z.1).length
def smallCountRealizer : Realizer smallCount :=
  composition (f := fun z : ScheduleInput => PhysicalComputedProposal.idealMarginCatalog z.1)
    (g := List.length)
    (composition (f := fun z : ScheduleInput => z.1)
      (g := PhysicalComputedProposal.idealMarginCatalog)
      first PhysicalComputedProposal.idealMarginCatalogRealizer) listLength
lemma polynomial_smallCount : PolynomialTime smallCountRealizer :=
  polynomial_composition (f := fun z : ScheduleInput => PhysicalComputedProposal.idealMarginCatalog z.1)
    (g := List.length)
    (polynomial_composition (f := fun z : ScheduleInput => z.1)
      (g := PhysicalComputedProposal.idealMarginCatalog) polynomial_first
      PhysicalComputedProposal.polynomial_idealMarginCatalog) polynomial_listLength

def massTotal (z : ScheduleInput) : ℕ := z.1.1.sum
def massTotalRealizer : Realizer massTotal := composition (composition first first) listSum
lemma polynomial_massTotal : PolynomialTime massTotalRealizer :=
  polynomial_composition (polynomial_composition polynomial_first polynomial_first) polynomial_listSum

def padding (z : ScheduleInput) : ℕ := (3 * dimension z)
def paddingRealizer : Realizer padding :=
  (mulGet (constant 3) dimensionRealizer)
lemma polynomial_padding : PolynomialTime paddingRealizer :=
  (polynomial_mulGet (polynomial_constant 3) polynomial_dimension)

def massBase (z : ScheduleInput) : ℕ := (((massTotal z + (3 * (dimension z)^2)) + cutoff z) + 3)
def massBaseRealizer : Realizer massBase :=
  (addGet (addGet (addGet massTotalRealizer (mulGet (constant 3) (powerGet dimensionRealizer 2))) cutoffRealizer) (constant 3))
lemma polynomial_massBase : PolynomialTime massBaseRealizer :=
  (polynomial_addGet (polynomial_addGet (polynomial_addGet polynomial_massTotal (polynomial_mulGet (polynomial_constant 3) (polynomial_powerGet polynomial_dimension 2))) polynomial_cutoff) (polynomial_constant 3))

def restarts (z : ScheduleInput) : ℕ := ((2 * (1 + (smallCount z)^2)) * (target z + 3))
def restartsRealizer : Realizer restarts :=
  (mulGet (mulGet (constant 2) (addGet (constant 1) (powerGet smallCountRealizer 2))) (addGet targetRealizer (constant 3)))
lemma polynomial_restarts : PolynomialTime restartsRealizer :=
  (polynomial_mulGet (polynomial_mulGet (polynomial_constant 2) (polynomial_addGet (polynomial_constant 1) (polynomial_powerGet polynomial_smallCount 2))) (polynomial_addGet polynomial_target (polynomial_constant 3)))

def mixBudget (z : ScheduleInput) : ℕ := (((target z + 3) + Nat.clog 2 (restarts z)) + ((2 * dimension z) * Nat.clog 2 (massBase z)))
def mixBudgetRealizer : Realizer mixBudget :=
  (addGet (addGet (addGet targetRealizer (constant 3)) (logGet restartsRealizer)) (mulGet (mulGet (constant 2) dimensionRealizer) (logGet massBaseRealizer)))
lemma polynomial_mixBudget : PolynomialTime mixBudgetRealizer :=
  (polynomial_addGet (polynomial_addGet (polynomial_addGet polynomial_target (polynomial_constant 3)) (polynomial_logGet polynomial_restarts)) (polynomial_mulGet (polynomial_mulGet (polynomial_constant 2) polynomial_dimension) (polynomial_logGet polynomial_massBase)))

def walkSteps (z : ScheduleInput) : ℕ := ((80000 * (dimension z)^17) * mixBudget z)
def walkStepsRealizer : Realizer walkSteps :=
  (mulGet (mulGet (constant 80000) (powerGet dimensionRealizer 17)) mixBudgetRealizer)
lemma polynomial_walkSteps : PolynomialTime walkStepsRealizer :=
  (polynomial_mulGet (polynomial_mulGet (polynomial_constant 80000) (polynomial_powerGet polynomial_dimension 17)) polynomial_mixBudget)

def terminalPrecision (z : ScheduleInput) : ℕ := ((target z + 3) + Nat.clog 2 (restarts z))
def terminalPrecisionRealizer : Realizer terminalPrecision :=
  (addGet (addGet targetRealizer (constant 3)) (logGet restartsRealizer))
lemma polynomial_terminalPrecision : PolynomialTime terminalPrecisionRealizer :=
  (polynomial_addGet (polynomial_addGet polynomial_target (polynomial_constant 3)) (polynomial_logGet polynomial_restarts))

def stepPrecision (z : ScheduleInput) : ℕ := (terminalPrecision z + Nat.clog 2 (walkSteps z))
def stepPrecisionRealizer : Realizer stepPrecision :=
  (addGet terminalPrecisionRealizer (logGet walkStepsRealizer))
lemma polynomial_stepPrecision : PolynomialTime stepPrecisionRealizer :=
  (polynomial_addGet polynomial_terminalPrecision (polynomial_logGet polynomial_walkSteps))

def proposalBits (z : ScheduleInput) : ℕ := Nat.clog 2 ((32 * (dimension z)^2))
def proposalBitsRealizer : Realizer proposalBits :=
  (logGet (mulGet (constant 32) (powerGet dimensionRealizer 2)))
lemma polynomial_proposalBits : PolynomialTime proposalBitsRealizer :=
  (polynomial_logGet (polynomial_mulGet (polynomial_constant 32) (polynomial_powerGet polynomial_dimension 2)))

def fineMarginMax (z : ScheduleInput) : ℕ := ((dimension z)^12 * ((massTotal z + (3 * (dimension z)^2)) + (2 * dimension z)))
def fineMarginMaxRealizer : Realizer fineMarginMax :=
  (mulGet (powerGet dimensionRealizer 12) (addGet (addGet massTotalRealizer (mulGet (constant 3) (powerGet dimensionRealizer 2))) (mulGet (constant 2) dimensionRealizer)))
lemma polynomial_fineMarginMax : PolynomialTime fineMarginMaxRealizer :=
  (polynomial_mulGet (polynomial_powerGet polynomial_dimension 12) (polynomial_addGet (polynomial_addGet polynomial_massTotal (polynomial_mulGet (polynomial_constant 3) (polynomial_powerGet polynomial_dimension 2))) (polynomial_mulGet (polynomial_constant 2) polynomial_dimension)))

def fineBinaryBits (z : ScheduleInput) : ℕ := Nat.clog 2 ((fineMarginMax z + 2))
def fineBinaryBitsRealizer : Realizer fineBinaryBits :=
  (logGet (addGet fineMarginMaxRealizer (constant 2)))
lemma polynomial_fineBinaryBits : PolynomialTime fineBinaryBitsRealizer :=
  (polynomial_logGet (polynomial_addGet polynomial_fineMarginMax (polynomial_constant 2)))

/-- Dynamic inner precision is still computed by a fixed arithmetic circuit. -/
def finePrecisionGet {f : ScheduleInput → ℕ} (F : Realizer f) :
    Realizer (fun z => CompletionRetryBudget.finePrecision (f z)) :=
  addGet (addGet F (constant 2)) (logGet (mulGet (constant 4) (addGet F (constant 2))))
lemma polynomial_finePrecisionGet {f : ScheduleInput → ℕ} {F : Realizer f}
    (hF : PolynomialTime F) : PolynomialTime (finePrecisionGet F) :=
  polynomial_addGet (polynomial_addGet hF (polynomial_constant 2))
    (polynomial_logGet (polynomial_mulGet (polynomial_constant 4)
      (polynomial_addGet hF (polynomial_constant 2))))

/-- Common completion reservation from the frozen baseline, at the chosen precision. -/
def completionBitsFor (t : ScheduleInput → ℕ) (z : ScheduleInput) : ℕ :=
  CompletionRandomBudget.completionReservation (dimension z) (massTotal z) (t z)
def completionBitsForRealizer {t : ScheduleInput → ℕ} (F : Realizer t) :
    Realizer (completionBitsFor t) :=
  mulGet (mulGet (constant 4) (addGet F (constant 2)))
    (mulGet (constant 25) (powerGet
      (addGet (addGet (addGet dimensionRealizer fineBinaryBitsRealizer)
        (finePrecisionGet F)) (constant 1)) 62))
lemma polynomial_completionBitsFor {t : ScheduleInput → ℕ} {F : Realizer t}
    (hF : PolynomialTime F) : PolynomialTime (completionBitsForRealizer F) :=
  polynomial_mulGet (polynomial_mulGet (polynomial_constant 4)
    (polynomial_addGet hF (polynomial_constant 2)))
    (polynomial_mulGet (polynomial_constant 25) (polynomial_powerGet
      (polynomial_addGet (polynomial_addGet
        (polynomial_addGet polynomial_dimension polynomial_fineBinaryBits)
        (polynomial_finePrecisionGet hF)) (polynomial_constant 1)) 62))

def stepCompletionBits : ScheduleInput → ℕ := completionBitsFor stepPrecision
def stepCompletionBitsRealizer : Realizer stepCompletionBits :=
  completionBitsForRealizer stepPrecisionRealizer
lemma polynomial_stepCompletionBits : PolynomialTime stepCompletionBitsRealizer :=
  polynomial_completionBitsFor polynomial_stepPrecision

def terminalCompletionBits : ScheduleInput → ℕ := completionBitsFor terminalPrecision
def terminalCompletionBitsRealizer : Realizer terminalCompletionBits :=
  completionBitsForRealizer terminalPrecisionRealizer
lemma polynomial_terminalCompletionBits : PolynomialTime terminalCompletionBitsRealizer :=
  polynomial_completionBitsFor polynomial_terminalPrecision

def stepSchedule (z : ScheduleInput) : ProfileWordSchedule :=
  ((walkSteps z, proposalBits z), stepCompletionBits z)
def stepScheduleRealizer : Realizer stepSchedule :=
  pair (pair walkStepsRealizer proposalBitsRealizer) stepCompletionBitsRealizer
lemma polynomial_stepSchedule : PolynomialTime stepScheduleRealizer :=
  polynomial_pair (polynomial_pair polynomial_walkSteps polynomial_proposalBits) polynomial_stepCompletionBits

def terminalSchedule (z : ScheduleInput) : ℕ × ℕ :=
  (terminalPrecision z, terminalCompletionBits z)
def terminalScheduleRealizer : Realizer terminalSchedule :=
  pair terminalPrecisionRealizer terminalCompletionBitsRealizer
lemma polynomial_terminalSchedule : PolynomialTime terminalScheduleRealizer :=
  polynomial_pair polynomial_terminalPrecision polynomial_terminalCompletionBits

/-- Accepted API for initialization, walk, fresh terminal, and independent restarts. -/
def schedule (z : ScheduleInput) : ScheduleOutput :=
  (((stepSchedule z, terminalSchedule z), restarts z), stepPrecision z)
def scheduleRealizer : Realizer schedule :=
  pair (pair (pair stepScheduleRealizer terminalScheduleRealizer) restartsRealizer) stepPrecisionRealizer
lemma polynomial_schedule : PolynomialTime scheduleRealizer :=
  polynomial_pair (polynomial_pair (polynomial_pair polynomial_stepSchedule
    polynomial_terminalSchedule) polynomial_restarts) polynomial_stepPrecision

def attemptBits (z : ScheduleInput) : ℕ := ((walkSteps z * (proposalBits z + stepCompletionBits z)) + terminalCompletionBits z)
def attemptBitsRealizer : Realizer attemptBits :=
  (addGet (mulGet walkStepsRealizer (addGet proposalBitsRealizer stepCompletionBitsRealizer)) terminalCompletionBitsRealizer)
lemma polynomial_attemptBits : PolynomialTime attemptBitsRealizer :=
  (polynomial_addGet (polynomial_mulGet polynomial_walkSteps (polynomial_addGet polynomial_proposalBits polynomial_stepCompletionBits)) polynomial_terminalCompletionBits)

def totalBits (z : ScheduleInput) : ℕ := (restarts z * attemptBits z)
def totalBitsRealizer : Realizer totalBits :=
  (mulGet restartsRealizer attemptBitsRealizer)
lemma polynomial_totalBits : PolynomialTime totalBitsRealizer :=
  (polynomial_mulGet polynomial_restarts polynomial_attemptBits)

/-- Exact formula identity; this does not reprove the degree-85 allowance. -/
lemma totalBits_eq_totalReservedBits (z : ScheduleInput) :
    totalBits z = CompletionRandomBudget.totalReservedBits
      (dimension z) (smallCount z) (massTotal z) (target z) := rfl

noncomputable section
variable {m n : ℕ} (r : Fin m → ℕ) (c : Fin n → ℕ)
local notation "d" => CompletionCounts.dimensionAllowance (I := Fin m) (J := Fin n)
local notation "U" => IdealOracleScales.cutoff (I := Fin m) (J := Fin n)
local notation "L" => IdealOracleScales.padding (I := Fin m) (J := Fin n)
local notation "p" => CompletionOuterSchedule.physicalSmallCount r c
local notation "base" => CompletionOuterSchedule.physicalMassBase (J := Fin n) r
local notation "T" => CompletionOuterSchedule.walkCount p d base
local notation "R" => CompletionOuterSchedule.restartCount p
local notation "hS" => CompletionOuterSchedule.stepPrecision p d base
local notation "hT" => CompletionOuterSchedule.terminalPrecision p
local notation "f" => PhysicalLatticeCompletion.reservedCompletionBits (J := Fin n) r

lemma dimension_ofFn (h : ℕ) : dimension ((List.ofFn r, List.ofFn c), h) = d := by
  simp only [dimension, marginDimension, List.length_ofFn,
    CompletionCounts.dimensionAllowance, Fintype.card_fin]
lemma cutoff_ofFn (h : ℕ) : cutoff ((List.ofFn r, List.ofFn c), h) = U :=
  PhysicalComputedProposal.idealMarginThreshold_ofFn r c
lemma padding_ofFn (h : ℕ) : padding ((List.ofFn r, List.ofFn c), h) = L := by
  simp only [padding, dimension_ofFn, IdealOracleScales.padding, IdealOracleScales.idealL]
lemma massTotal_ofFn (h : ℕ) : massTotal ((List.ofFn r, List.ofFn c), h) = ∑ i, r i := by
  simp only [massTotal, List.sum_ofFn]

/-- Cardinality is tied to the actual executable ideal catalogue, not the old
source cutoff. Its proof equivalence is used only in this semantic theorem. -/
lemma smallCount_ofFn (h : ℕ) : smallCount ((List.ofFn r, List.ofFn c), h) = p := by
  have hcat : PhysicalComputedProposal.idealMarginCatalog (List.ofFn r, List.ofFn c) =
      PhysicalComputedProposal.computedCatalog r c U := by
    unfold PhysicalComputedProposal.idealMarginCatalog
    rw [PhysicalComputedProposal.idealMarginThreshold_ofFn]
    rfl
  unfold smallCount
  rw [hcat]
  change (PhysicalComputedProposal.computedCatalog r c U).length =
    Fintype.card (SmallContextCoordinates.Cells (CompletionCounts.firstPaperSmall r c U))
  simpa only [Fintype.card_fin] using
    Fintype.card_congr (PhysicalComputedProposal.computedCellEquiv r c U)

lemma massBase_ofFn (h : ℕ) : massBase ((List.ofFn r, List.ofFn c), h) = base := by
  simp only [massBase, massTotal_ofFn, dimension_ofFn, cutoff_ofFn]
  unfold CompletionOuterSchedule.physicalMassBase IdealOracleScales.padding IdealOracleScales.idealL
    IdealOracleScales.cutoff IdealOracleScales.idealU
  ring
lemma restarts_ofFn (h : ℕ) : restarts ((List.ofFn r, List.ofFn c), h) = R h := by
  simp only [restarts, smallCount_ofFn, target,
    CompletionOuterSchedule.restartCount, CompletionOuterSchedule.successFactor]
lemma mixBudget_ofFn (h : ℕ) : mixBudget ((List.ofFn r, List.ofFn c), h) =
    CompletionOuterSchedule.mixExponent p d base h := by
  simp only [mixBudget, target, restarts_ofFn, dimension_ofFn, massBase_ofFn,
    CompletionOuterSchedule.mixExponent]
lemma walkSteps_ofFn (h : ℕ) : walkSteps ((List.ofFn r, List.ofFn c), h) = T h := by
  simp only [walkSteps, dimension_ofFn, mixBudget_ofFn,
    CompletionOuterSchedule.walkCount, CompletionOuterSchedule.gapFactor]
lemma terminalPrecision_ofFn (h : ℕ) : terminalPrecision ((List.ofFn r, List.ofFn c), h) = hT h := by
  simp only [terminalPrecision, target, restarts_ofFn, CompletionOuterSchedule.terminalPrecision]
lemma stepPrecision_ofFn (h : ℕ) : stepPrecision ((List.ofFn r, List.ofFn c), h) = hS h := by
  simp only [stepPrecision, terminalPrecision_ofFn, walkSteps_ofFn,
    CompletionOuterSchedule.terminalPrecision, CompletionOuterSchedule.stepPrecision]
lemma proposalBits_ofFn (h : ℕ) : proposalBits ((List.ofFn r, List.ofFn c), h) =
    CompletionRandomBudget.proposalReservation d := by
  simp only [proposalBits, dimension_ofFn, CompletionRandomBudget.proposalReservation]

lemma stepCompletionBits_ofFn (h : ℕ) :
    stepCompletionBits ((List.ofFn r, List.ofFn c), h) = f (hS h) := by
  simp only [stepCompletionBits, completionBitsFor, dimension_ofFn, massTotal_ofFn,
    stepPrecision_ofFn]
  exact CompletionRandomBudget.completionReservation_eq_reserved r (hS h)
lemma terminalCompletionBits_ofFn (h : ℕ) :
    terminalCompletionBits ((List.ofFn r, List.ofFn c), h) = f (hT h) := by
  simp only [terminalCompletionBits, completionBitsFor, dimension_ofFn, massTotal_ofFn,
    terminalPrecision_ofFn]
  exact CompletionRandomBudget.completionReservation_eq_reserved r (hT h)

lemma stepSchedule_ofFn (h : ℕ) : stepSchedule ((List.ofFn r, List.ofFn c), h) =
    ((T h, CompletionRandomBudget.proposalReservation d), f (hS h)) := by
  simp only [stepSchedule, walkSteps_ofFn, proposalBits_ofFn, stepCompletionBits_ofFn]
lemma terminalSchedule_ofFn (h : ℕ) : terminalSchedule ((List.ofFn r, List.ofFn c), h) =
    (hT h, f (hT h)) := by
  simp only [terminalSchedule, terminalPrecision_ofFn, terminalCompletionBits_ofFn]
lemma schedule_ofFn (h : ℕ) : schedule ((List.ofFn r, List.ofFn c), h) =
    (((((T h, CompletionRandomBudget.proposalReservation d), f (hS h)),
      (hT h, f (hT h))), R h), hS h) := by
  simp only [schedule, stepSchedule_ofFn, terminalSchedule_ofFn, restarts_ofFn, stepPrecision_ofFn]

lemma attemptBits_ofFn (h : ℕ) : attemptBits ((List.ofFn r, List.ofFn c), h) =
    PhysicalReferenceBoolean.attemptBits (n := n) r (T h) (hS h) (hT h) := by
  simp only [attemptBits, walkSteps_ofFn, proposalBits_ofFn,
    stepCompletionBits_ofFn, terminalCompletionBits_ofFn]
  rfl
lemma totalBits_ofFn (h : ℕ) : totalBits ((List.ofFn r, List.ofFn c), h) =
    PhysicalReferenceBoolean.outerBits (n := n) r (T h) (R h) (hS h) (hT h) := by
  simp only [totalBits, restarts_ofFn, attemptBits_ofFn]
  rfl

lemma totalBits_ofFn_budget (h : ℕ) : totalBits ((List.ofFn r, List.ofFn c), h) =
    CompletionRandomBudget.physicalTotalReservedBits r c h := by
  rw [totalBits_eq_totalReservedBits, dimension_ofFn, smallCount_ofFn, massTotal_ofFn]
  rfl

end
end Math115.LatticeScheduleProgram
