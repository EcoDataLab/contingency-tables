/- Exact original reference packed-trial certificate closes the last seam.
No realizer, codec, machine or restricted input domain is introduced. -/
import CompleteDraw.PublicBridge
import ReferenceRuntime.PackedTrialDegree
namespace Math115.CompleteDrawNext
open OAI OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds
noncomputable section

/-- Literal numerical degree certified by the exact reference endpoint. -/
def referenceTrialDegree : ℕ := 249569086149969927754465653530857316378662151100210635200859836899115394502462433742952346464893494918298349218830740503411950490371359547202234848664532691737852411594490630793354441329305157924334049610980689568025133584089872528423843231844695041473652053370821139768976712765532769803598329631937527257644643545333786414444514615499205181845594806221996072304130411642154202278059154591154845186413464438667829092073424522772982022332107776812250045880396804598645709356960800186404581118066277180403051396836632512938969750164048642049142739626451320875705881681967964561744998704271360

lemma typed_actual_referencePackedTrial :
    Typed Math115.LatticeOuterProgram.packedTrialRealizer referenceTrialDegree :=
  Math115.ReferenceRuntimeNext.typed_actual_packedTrial

/-- Fixed literal-natural expression for the exact supplied-word public draw. -/
def explicitDrawDegree : ℕ := drawDegree referenceTrialDegree

/-- All original draw fields are now closed; no degree premise remains. -/
theorem typed_actual_publicDraw :
    Typed Math115.PublicLatticeSampler.publicDrawRealizer explicitDrawDegree :=
  typed_publicDraw_of_reference typed_actual_referencePackedTrial

/-- Charged work plus the entire encoded output for every literal word/bank pair. -/
theorem actual_publicDraw_polynomial :
    ∃ p : Polynomial ℕ, p.natDegree ≤ explicitDrawDegree ∧
      ∀ z : List Symbol × List Bool,
        Math115.PublicLatticeSampler.publicDrawRealizer.cost z +
          weight (Math115.PublicLatticeSampler.publicDraw z) ≤ p.eval (weight z) :=
  typed_actual_publicDraw

end
end Math115.CompleteDrawNext
