import ReferenceRuntime.DenseTrialConstructionDegree
import CompletionRuntime.MatrixDegree
import InputNormalization.CanonicalDegree

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds DensePrograms
set_option maxHeartbeats 1600000
noncomputable section

lemma typed_acceptCompletion : Typed acceptCompletionRealizer 1886 := by
  unfold acceptCompletionRealizer
  exact typed_choose Math115.CompletionRuntimeNext.typed_completionValid
    (typed_composition Math115.CompletionRuntimeNext.typed_completedMatrix typed_some) (typed_constant none)

lemma typed_denseTrialCode : Typed denseTrialCodeRealizer 160783450526040547937661160571574099781028877331290954993478604403449973359743741593051897069727648699121664 := by
  unfold denseTrialCodeRealizer
  exact typed_composition typed_denseTrialCompletion typed_acceptCompletion

lemma typed_drawChunks : Typed drawChunksRealizer 3101626277945669376 := by
  unfold drawChunksRealizer
  exact typed_composition
    (typed_pair (typed_composition (typed_composition typed_first typed_first) typed_denseTrialWidth) typed_second)
    typed_denseWordChunks

lemma typed_denseDrawCode : Typed denseDrawCodeRealizer 641449016910039752977665513687001190589821839233178797986180910690648338182926250246270201858507390175635287180688965912070196017192067030656223102339541238591485649808549550720531391612302383184413031028961140113813337711524100159488 := by
  unfold denseDrawCodeRealizer
  exact typed_composition (typed_pair typed_first typed_drawChunks)
    (Math115.DrawDegree.typed_firstSuccessRetry typed_denseTrialCode (by decide))

lemma typed_normalizedDraw : Typed normalizedDrawRealizer 641449016910039752977665513687001190589821839233178797986180910690648338182926250246270201858507390175635287180688965912070196017192067030656223102339541238591485649808549550720531391612302383184413031028961140113813337711524100159488 := by
  unfold normalizedDrawRealizer
  exact Math115.ScalarOutputDegree.typed_composition_from_output_size
    Math115.InputNormalization.typed_preparedDraw typed_denseDrawCode (18*X+16)
    (by simpa using degree_affine 18 16)
    (fun z => by simpa only [eval_add,eval_mul,eval_ofNat,eval_X] using Math115.InputNormalization.preparedDraw_weight z)

lemma typed_normalizedDenseCode : Typed normalizedDenseCodeRealizer 2318196747112883667261283166464822302791616126988708175922057811236003094193095468390020509516645708094745927871009922806221688406132130248791590291855102036269629138408098076304000449286860812828468694138665560371321402489448097976389632 := by
  unfold normalizedDenseCodeRealizer
  exact typed_composition
    (typed_pair Math115.InputNormalization.typed_drawIndices typed_normalizedDraw) Math115.InputNormalization.typed_swapMatrix

/-- Original canonical dense draw, including zero-grid construction, eager
binary greedy fallback, maximal-margin normalization, every supplied complete
trial, first-success selection and the original inverse output permutation. -/
theorem typed_canonicalDenseDraw : Typed canonicalDenseDrawRealizer 4636393494225767334522566332929644605583232253977416351844115622472006188386190936780041019033291416189491855742019845612443376812264260497583180583710204072539258276816196152608000898573721625656937388277331120742642804978896195952779264 := by
  unfold canonicalDenseDrawRealizer
  exact Math115.ScalarOutputDegree.typed_composition_from_output_size
    Math115.InputNormalization.typed_canonicalInput typed_normalizedDenseCode (20*(X+1)^2)
    (Math115.InputNormalization.degree_quadratic_envelope 20 1)
    (fun z => by simpa only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one] using Math115.InputNormalization.canonicalInput_weight z)

#check typed_denseTrialCode
#print axioms typed_denseTrialCode
#check typed_canonicalDenseDraw
#print axioms typed_canonicalDenseDraw
end
end Math115.ReferenceRuntimeNext
