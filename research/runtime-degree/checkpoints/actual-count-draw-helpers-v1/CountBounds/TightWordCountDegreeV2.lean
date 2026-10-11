/- Private checkpoint12 tightened COMPLETE count candidate v2, not compiled.
Every circuit result certifies exact execution plus encoded output, and retains
an independent affine output bound. Catalogue list output is handled cubically
before its scalar cardinality returns to the affine circuit. -/
import CountBounds.ScalarCircuitDegreeV2
import ResearchBounds.SmallCellCatalogueDegree

namespace Math115.TightCountDegreeV2
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped
open ProfilePrograms DensePrograms Math115.DegreeBounds
open Math115.ScalarCircuitDegreeV2 Math115.ScalarOutputDegree
open Math115.LatticeScheduleProgram Polynomial

noncomputable section

variable (e : ℕ) (he : 16≤e)
include he

lemma circuit_id {A : Type} [Codec A] : Circuit (identity (A:=A)) e :=
  circuit_mono circuit_identity (by omega)
lemma circuit_fst {A B : Type} [Codec A] [Codec B] : Circuit (first (A:=A) (B:=B)) e :=
  circuit_mono circuit_first (by omega)
lemma circuit_snd {A B : Type} [Codec A] [Codec B] : Circuit (second (A:=A) (B:=B)) e :=
  circuit_mono circuit_second (by omega)
lemma circuit_const {A B : Type} [Codec A] [Codec B] (b : B) : Circuit (constant (A:=A) b) e :=
  circuit_mono (circuit_constant b) (by omega)
lemma circuit_len {A : Type} [Codec A] : Circuit (listLength (A:=A)) e :=
  circuit_mono circuit_listLength (by omega)
lemma circuit_sum : Circuit listSum e := circuit_mono circuit_listSum (by omega)
lemma circuit_add_e : Circuit add e := circuit_mono circuit_add (by omega)
lemma circuit_mul_e : Circuit multiply e := circuit_mono circuit_multiply (by omega)
lemma circuit_pow_e (k : ℕ) : Circuit (fixedPowerRealizer k) e :=
  circuit_mono (circuit_fixedPower k) (by omega)
lemma circuit_log_e : Circuit ceilLogTwoRealizer e := circuit_mono circuit_log (by omega)

lemma circuit_pair_e {A B D : Type} [Codec A] [Codec B] [Codec D]
    {f : A→B} {g : A→D} {F : Realizer f} {G : Realizer g}
    (hF : Circuit F e) (hG : Circuit G e) : Circuit (pair F G) e :=
  circuit_pair_same (by omega) hF hG
lemma circuit_addGet_e {f g : ScheduleInput→ℕ} {F : Realizer f} {G : Realizer g}
    (hF : Circuit F e) (hG : Circuit G e) : Circuit (addGet F G) e :=
  circuit_composition_same (circuit_pair_e e he hF hG) (circuit_add_e e he)
lemma circuit_mulGet_e {f g : ScheduleInput→ℕ} {F : Realizer f} {G : Realizer g}
    (hF : Circuit F e) (hG : Circuit G e) : Circuit (mulGet F G) e :=
  circuit_composition_same (circuit_pair_e e he hF hG) (circuit_mul_e e he)
lemma circuit_powerGet_e {f : ScheduleInput→ℕ} {F : Realizer f}
    (hF : Circuit F e) (k : ℕ) : Circuit (powerGet F k) e :=
  circuit_composition_same hF (circuit_pow_e e he k)
lemma circuit_logGet_e {f : ScheduleInput→ℕ} {F : Realizer f}
    (hF : Circuit F e) : Circuit (logGet F) e :=
  circuit_composition_same hF (circuit_log_e e he)

lemma circuit_successor_e : Circuit successor e := by
  unfold successor
  apply circuit_congr
  exact circuit_composition_same
    (circuit_pair_e e he (circuit_id e he) (circuit_const e he 1)) (circuit_add_e e he)
lemma circuit_square_e : Circuit squareNat e :=
  circuit_composition_same (circuit_pair_e e he (circuit_id e he) (circuit_id e he)) (circuit_mul_e e he)
lemma circuit_cube_e : Circuit PhysicalComputedProposal.cubeNat e := by
  unfold PhysicalComputedProposal.cubeNat
  apply circuit_congr
  exact circuit_composition_same
    (circuit_pair_e e he (circuit_square_e e he) (circuit_id e he)) (circuit_mul_e e he)
lemma circuit_dimensionBase : Circuit marginDimensionRealizer e := by
  unfold marginDimensionRealizer
  exact circuit_composition_same (circuit_pair_e e he (circuit_const e he 10)
    (circuit_composition_same (circuit_pair_e e he
      (circuit_composition_same (circuit_composition_same (circuit_fst e he) (circuit_len e he)) (circuit_successor_e e he))
      (circuit_composition_same (circuit_composition_same (circuit_snd e he) (circuit_len e he)) (circuit_successor_e e he)))
      (circuit_mul_e e he))) (circuit_add_e e he)
lemma circuit_cutoffBase : Circuit PhysicalComputedProposal.idealMarginThresholdRealizer e := by
  unfold PhysicalComputedProposal.idealMarginThresholdRealizer
  apply circuit_congr
  exact circuit_composition_same (circuit_pair_e e he (circuit_const e he 5)
    (circuit_composition_same (circuit_dimensionBase e he) (circuit_cube_e e he))) (circuit_mul_e e he)

lemma typed_catalogueBase {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Typed PhysicalComputedProposal.idealMarginCatalogRealizer e := by
  unfold PhysicalComputedProposal.idealMarginCatalogRealizer
  have hp := circuit_pair_e e he (circuit_id e he) (circuit_cutoffBase e he)
  obtain ⟨P,hP,hPb⟩ :=
    typed_composition_linear hp.1 (Math115.ListRepeatDegreeV1.typed_mono hc hce) hp.2
  refine ⟨P,(by simpa only [max_self] using hP),?_⟩
  intro z
  change (composition (pair identity PhysicalComputedProposal.idealMarginThresholdRealizer)
    smallCellCatalogRealizer).cost z+
    weight (smallCellCatalog (z,PhysicalComputedProposal.idealMarginThreshold z)) ≤ P.eval (weight z)
  simpa only [Function.comp_apply, id] using hPb z

omit he in
lemma smallCount_linear : LinearOutput smallCount := by
  refine ⟨4,1,fun z=>?_⟩
  have hlen : (PhysicalComputedProposal.idealMarginCatalog z.1).length≤z.1.1.length*z.1.2.length := by
    unfold PhysicalComputedProposal.idealMarginCatalog smallCellCatalog
    exact (List.length_filter_le _ _).trans (by simp [cellPairs])
  have hsize := (Nat.size_le_size hlen).trans (nat_size_mul z.1.1.length z.1.2.length)
  have hr : z.1.1.length.size≤weight z.1.1 :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (list_length_le_weight z.1.1)
  have hc : z.1.2.length.size≤weight z.1.2 :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (list_length_le_weight z.1.2)
  have hw := weight_nat_le ((PhysicalComputedProposal.idealMarginCatalog z.1).length)
  change weight ((PhysicalComputedProposal.idealMarginCatalog z.1).length)≤_
  have hweights : weight z.1.1+weight z.1.2 ≤ weight z := by
    rcases z with ⟨⟨rs,cs⟩,h⟩
    change weight rs+weight cs ≤ weight ((rs,cs),h)
    rw [weight_prod,weight_prod]
    omega
  omega

lemma circuit_smallCount {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit smallCountRealizer e := by
  refine ⟨?_,smallCount_linear⟩
  unfold smallCountRealizer
  have hbase : Typed (composition (first (A:=Margins) (B:=ℕ)) PhysicalComputedProposal.idealMarginCatalogRealizer) e := by
    simpa only [max_self] using typed_composition_linear (circuit_fst e he).1 (typed_catalogueBase e he hc hce)
      (circuit_fst e he).2
  have hcomp := typed_composition_from_output_size (e:=e) (t:=2) (s:=3) hbase
    Math115.WordCountSeedDegrees.typed_listLength_seed (8*X^3+4*X^2+1) (by
      have h1 := degree_scale 8 (show (X^3 : Polynomial ℕ).natDegree≤3 by simp)
      have h2 := degree_scale 4 (show (X^2 : Polynomial ℕ).natDegree≤2 by simp)
      simpa using degree_add (degree_add h1 h2) (show (1 : Polynomial ℕ).natDegree≤0 by simp)) (by
      intro z
      have hout : weight (PhysicalComputedProposal.idealMarginCatalog z.1)≤weight (cellPairs z.1) := by
        unfold PhysicalComputedProposal.idealMarginCatalog smallCellCatalog
        exact weight_sublist List.filter_sublist
      have hcell := Math115.CatalogueDegreeV1.weight_cellPairs_output z.1
      have hfirst : weight z.1≤weight z := OAI.MatchingFPRAS.TreeTyped.weight_fst z
      simp only [Function.comp_apply,eval_add,eval_mul,eval_ofNat,eval_pow,eval_X,eval_one]
      apply hout.trans (hcell.trans ?_)
      gcongr <;> exact hfirst)
  exact Math115.ListRepeatDegreeV1.typed_mono hcomp (by omega)

lemma circuit_target {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit targetRealizer e := by
  unfold targetRealizer
  exact (circuit_snd e he)

lemma circuit_dimension {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit dimensionRealizer e := by
  unfold dimensionRealizer
  exact circuit_composition_same (circuit_fst e he) (circuit_dimensionBase e he)

lemma circuit_cutoff {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit cutoffRealizer e := by
  unfold cutoffRealizer
  exact circuit_composition_same (circuit_fst e he) (circuit_cutoffBase e he)

lemma circuit_massTotal {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit massTotalRealizer e := by
  unfold massTotalRealizer
  exact circuit_composition_same (circuit_composition_same (circuit_fst e he) (circuit_fst e he)) (circuit_sum e he)

lemma circuit_padding {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit paddingRealizer e := by
  unfold paddingRealizer
  exact circuit_mulGet_e e he (circuit_const e he 3) (circuit_dimension e he hc hce)

lemma circuit_massBase {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit massBaseRealizer e := by
  unfold massBaseRealizer
  exact circuit_addGet_e e he (circuit_addGet_e e he (circuit_addGet_e e he (circuit_massTotal e he hc hce) (circuit_mulGet_e e he (circuit_const e he 3) (circuit_powerGet_e e he (circuit_dimension e he hc hce) 2))) (circuit_cutoff e he hc hce)) (circuit_const e he 3)

lemma circuit_restarts {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit restartsRealizer e := by
  unfold restartsRealizer
  exact circuit_mulGet_e e he (circuit_mulGet_e e he (circuit_const e he 2) (circuit_addGet_e e he (circuit_const e he 1) (circuit_powerGet_e e he (circuit_smallCount e he hc hce) 2))) (circuit_addGet_e e he (circuit_target e he hc hce) (circuit_const e he 3))

lemma circuit_mixBudget {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit mixBudgetRealizer e := by
  unfold mixBudgetRealizer
  exact circuit_addGet_e e he (circuit_addGet_e e he (circuit_addGet_e e he (circuit_target e he hc hce) (circuit_const e he 3)) (circuit_logGet_e e he (circuit_restarts e he hc hce))) (circuit_mulGet_e e he (circuit_mulGet_e e he (circuit_const e he 2) (circuit_dimension e he hc hce)) (circuit_logGet_e e he (circuit_massBase e he hc hce)))

lemma circuit_walkSteps {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit walkStepsRealizer e := by
  unfold walkStepsRealizer
  exact circuit_mulGet_e e he (circuit_mulGet_e e he (circuit_const e he 80000) (circuit_powerGet_e e he (circuit_dimension e he hc hce) 17)) (circuit_mixBudget e he hc hce)

lemma circuit_terminalPrecision {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit terminalPrecisionRealizer e := by
  unfold terminalPrecisionRealizer
  exact circuit_addGet_e e he (circuit_addGet_e e he (circuit_target e he hc hce) (circuit_const e he 3)) (circuit_logGet_e e he (circuit_restarts e he hc hce))

lemma circuit_stepPrecision {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit stepPrecisionRealizer e := by
  unfold stepPrecisionRealizer
  exact circuit_addGet_e e he (circuit_terminalPrecision e he hc hce) (circuit_logGet_e e he (circuit_walkSteps e he hc hce))

lemma circuit_proposalBits {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit proposalBitsRealizer e := by
  unfold proposalBitsRealizer
  exact circuit_logGet_e e he (circuit_mulGet_e e he (circuit_const e he 32) (circuit_powerGet_e e he (circuit_dimension e he hc hce) 2))

lemma circuit_fineMarginMax {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit fineMarginMaxRealizer e := by
  unfold fineMarginMaxRealizer
  exact circuit_mulGet_e e he (circuit_powerGet_e e he (circuit_dimension e he hc hce) 12) (circuit_addGet_e e he (circuit_addGet_e e he (circuit_massTotal e he hc hce) (circuit_mulGet_e e he (circuit_const e he 3) (circuit_powerGet_e e he (circuit_dimension e he hc hce) 2))) (circuit_mulGet_e e he (circuit_const e he 2) (circuit_dimension e he hc hce)))

lemma circuit_fineBinaryBits {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit fineBinaryBitsRealizer e := by
  unfold fineBinaryBitsRealizer
  exact circuit_logGet_e e he (circuit_addGet_e e he (circuit_fineMarginMax e he hc hce) (circuit_const e he 2))


lemma circuit_finePrecisionGet_e {f : ScheduleInput→ℕ} {F : Realizer f}
    (hF : Circuit F e) : Circuit (finePrecisionGet F) e := by
  unfold finePrecisionGet
  exact circuit_addGet_e e he (circuit_addGet_e e he hF (circuit_const e he 2))
    (circuit_logGet_e e he (circuit_mulGet_e e he (circuit_const e he 4)
      (circuit_addGet_e e he hF (circuit_const e he 2))))
lemma circuit_completionBitsFor_e {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e)
    {f : ScheduleInput→ℕ} {F : Realizer f} (hF : Circuit F e) :
    Circuit (completionBitsForRealizer F) e := by
  unfold completionBitsForRealizer
  exact circuit_mulGet_e e he
    (circuit_mulGet_e e he (circuit_const e he 4) (circuit_addGet_e e he hF (circuit_const e he 2)))
    (circuit_mulGet_e e he (circuit_const e he 25) (circuit_powerGet_e e he
      (circuit_addGet_e e he (circuit_addGet_e e he
        (circuit_addGet_e e he (circuit_dimension e he hc hce) (circuit_fineBinaryBits e he hc hce))
        (circuit_finePrecisionGet_e e he hF)) (circuit_const e he 1)) 62))
lemma circuit_stepCompletionBits {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit stepCompletionBitsRealizer e := by
  unfold stepCompletionBitsRealizer
  exact circuit_completionBitsFor_e e he hc hce (circuit_stepPrecision e he hc hce)

lemma circuit_terminalCompletionBits {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit terminalCompletionBitsRealizer e := by
  unfold terminalCompletionBitsRealizer
  exact circuit_completionBitsFor_e e he hc hce (circuit_terminalPrecision e he hc hce)

lemma circuit_stepSchedule {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit stepScheduleRealizer e := by
  unfold stepScheduleRealizer
  exact circuit_pair_e e he (circuit_pair_e e he (circuit_walkSteps e he hc hce) (circuit_proposalBits e he hc hce)) (circuit_stepCompletionBits e he hc hce)

lemma circuit_terminalSchedule {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit terminalScheduleRealizer e := by
  unfold terminalScheduleRealizer
  exact circuit_pair_e e he (circuit_terminalPrecision e he hc hce) (circuit_terminalCompletionBits e he hc hce)

lemma circuit_schedule {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit scheduleRealizer e := by
  unfold scheduleRealizer
  exact circuit_pair_e e he (circuit_pair_e e he (circuit_pair_e e he (circuit_stepSchedule e he hc hce) (circuit_terminalSchedule e he hc hce)) (circuit_restarts e he hc hce)) (circuit_stepPrecision e he hc hce)

lemma circuit_attemptBits {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit attemptBitsRealizer e := by
  unfold attemptBitsRealizer
  exact circuit_addGet_e e he (circuit_mulGet_e e he (circuit_walkSteps e he hc hce) (circuit_addGet_e e he (circuit_proposalBits e he hc hce) (circuit_stepCompletionBits e he hc hce))) (circuit_terminalCompletionBits e he hc hce)

lemma circuit_totalBits {c : ℕ} (hc : Typed smallCellCatalogRealizer c) (hce : c≤e) :
    Circuit totalBitsRealizer e := by
  unfold totalBitsRealizer
  exact circuit_mulGet_e e he (circuit_restarts e he hc hce) (circuit_attemptBits e he hc hce)


omit he

/-- Conditional tight degree of the ACTUAL complete count realizer. -/
theorem typed_wordCount_from_catalogue {c : ℕ} (hc : Typed smallCellCatalogRealizer c) :
    Typed PublicLatticeSampler.wordCountRealizer (max c 16) := by
  let E := max c 16
  have hE : 16≤E := Nat.le_max_right _ _
  have hcE : c≤E := Nat.le_max_left _ _
  unfold PublicLatticeSampler.wordCountRealizer
  obtain ⟨P,hP,hPb⟩ := typed_composition_linear
    (Math115.ListRepeatDegreeV1.typed_mono Math115.ParserDegreeV1.typed_parsedSampling hE)
    (circuit_totalBits E hE hc hcE).1 parsedSampling_linear
  refine ⟨P,(by simpa only [E, max_self] using hP),?_⟩
  intro as
  change (composition parsedSamplingRealizer totalBitsRealizer).cost as+
    weight (totalBits (parsedSampling as)) ≤ P.eval (weight as)
  simpa only [Function.comp_apply] using hPb as

/-- Numerical candidate binding to the catalogue lane's exact certificate. -/
theorem typed_complete_wordCount_1008 : Typed PublicLatticeSampler.wordCountRealizer 1008 := by
  exact typed_wordCount_from_catalogue Math115.CatalogueDegreeV1.typed_smallCellCatalog

theorem complete_wordCount_charged_work_1008 :
    ∃ P : Polynomial ℕ,P.natDegree≤1008 ∧ ∀ as,
      PublicLatticeSampler.wordCountRealizer.cost as+weight (PublicLatticeSampler.wordCount as)≤P.eval (weight as) :=
  typed_complete_wordCount_1008

end
end Math115.TightCountDegreeV2
