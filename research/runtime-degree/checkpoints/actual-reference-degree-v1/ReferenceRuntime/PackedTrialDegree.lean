import ReferenceRuntime.ProfileStepDegree
import ReferenceRuntime.OuterWordParsingDegree

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds DensePrograms ProfilePrograms
open Math115.AffineMapWithNext
set_option maxHeartbeats 2000000
noncomputable section

lemma outputBound_of_typed {A B : Type} [Codec A] [Codec B]
    {f : A → B} {F : Realizer f} {e : ℕ} (hF : Typed F e) : OutputBound f e := by
  obtain ⟨p,hp,hpb⟩ := hF
  refine ⟨p,hp,fun z => ?_⟩
  have h := hpb z
  omega

lemma outputBound_composition {A B D : Type} [Codec A] [Codec B] [Codec D]
    {f : A → B} {g : B → D} {s t : ℕ} (hf : OutputBound f s) (hg : OutputBound g t) :
    OutputBound (g ∘ f) (t*s) := by
  obtain ⟨p,hp,hpb⟩ := hf
  obtain ⟨q,hq,hqb⟩ := hg
  exact ⟨q.comp p,degree_comp hq hp,fun z => (hqb (f z)).trans
    (by simpa only [eval_comp] using polynomial_eval_monotone q (hpb z))⟩

lemma outputBound_pair {A B D : Type} [Codec A] [Codec B] [Codec D]
    {f : A → B} {g : A → D} {s t : ℕ} (hf : OutputBound f s) (hg : OutputBound g t) :
    OutputBound (fun z => (f z,g z)) (max s t) := by
  obtain ⟨p,hp,hpb⟩ := hf
  obtain ⟨q,hq,hqb⟩ := hg
  refine ⟨p+q+1,natDegree_add_le_of_degree_le (degree_add hp hq) (by simp),fun z => ?_⟩
  have h1 := hpb z
  have h2 := hqb z
  simp only [eval_add,eval_one,weight_prod]
  omega

lemma typed_referenceWithPrecision : Typed LatticeOuterProgram.withPrecisionRealizer 1 := by
  unfold LatticeOuterProgram.withPrecisionRealizer
  exact typed_pair (typed_composition typed_first typed_first)
    (typed_pair (typed_composition (typed_composition typed_first typed_second) typed_first) typed_second)

lemma typed_referenceTrialState : Typed LatticeOuterProgram.trialStateRealizer 12199682796582558701020431472379011374309723016488768812616461262878430516462983621905834360407048315144675590899661629294864970581053017811224060172015413211584159596727114517935294322664097235811837109649097996545870414588367457722049829882231989241738555454623119832403564124534809022132843617826514031543355356062528738150977154242986053677236005423066262040444791326483380941011134472122294978975118237987132787493761141011767768297506467776352330046103979923629526015683511020054782937237363762952201133896207225404489181293412875944827638025147017538335727100188688385 := by
  unfold LatticeOuterProgram.trialStateRealizer
  exact typed_composition (typed_composition typed_first typed_first) typed_actual_profileWalk

/-- The exact original cap-guarded fold bounds every final encoded state by
this cubic envelope, independently of the callback's charged-work degree. -/
lemma referenceTrialState_output : OutputBound LatticeOuterProgram.trialState 3 := by
  refine ⟨20*(X+1)^3,?_,fun z => ?_⟩
  · simpa using degree_scale 20 (natDegree_pow_le_of_le 3
      (show (X+1 : Polynomial ℕ).natDegree ≤ 1 by simpa using degree_affine 1 1))
  · have h := LatticeProfileWalk.profileFold_weight z.1.1.2 z.1.1.1 (weight z)
      ((weight_fst z.1.1).trans ((weight_fst z.1).trans (weight_fst z)))
    simpa only [LatticeOuterProgram.trialState,LatticeProfileWalk.profileWalk,
      eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one] using h

lemma typed_referenceTrialParameters : Typed LatticeOuterProgram.trialParametersRealizer 12199682796582558701020431472379011374309723016488768812616461262878430516462983621905834360407048315144675590899661629294864970581053017811224060172015413211584159596727114517935294322664097235811837109649097996545870414588367457722049829882231989241738555454623119832403564124534809022132843617826514031543355356062528738150977154242986053677236005423066262040444791326483380941011134472122294978975118237987132787493761141011767768297506467776352330046103979923629526015683511020054782937237363762952201133896207225404489181293412875944827638025147017538335727100188688385 := by
  unfold LatticeOuterProgram.trialParametersRealizer
  exact typed_composition
    (typed_pair (typed_composition typed_referenceTrialState Math115.DrawDegree.typed_currentParameters)
      (typed_composition typed_first typed_second)) typed_referenceWithPrecision

lemma referenceTrialParameters_output : OutputBound LatticeOuterProgram.trialParameters 3 := by
  have hcurrent : OutputBound (fun z : LatticeOuterProgram.TrialData => currentParameters (LatticeOuterProgram.trialState z)) 3 :=
    outputBound_composition referenceTrialState_output (outputBound_of_typed Math115.DrawDegree.typed_currentParameters)
  have hprec : OutputBound (fun z : LatticeOuterProgram.TrialData => z.1.2) 1 :=
    outputBound_of_typed (typed_composition typed_first typed_second)
  exact outputBound_composition (outputBound_pair hcurrent hprec) (outputBound_of_typed typed_referenceWithPrecision)

lemma typed_referenceTrialCompletion : Typed LatticeOuterProgram.trialCompletionRealizer 12199682796582558701020431472379011374309723016488768812616461262878430516462983621905834360407048315144675590899661629294864970581053017811224060172015413211584159596727114517935294322664097235811837109649097996545870414588367457722049829882231989241738555454623119832403564124534809022132843617826514031543355356062528738150977154242986053677236005423066262040444791326483380941011134472122294978975118237987132787493761141011767768297506467776352330046103979923629526015683511020054782937237363762952201133896207225404489181293412875944827638025147017538335727100188688385 := by
  have hresidual : Typed (composition LatticeOuterProgram.trialParametersRealizer residualParametersRealizer) 12199682796582558701020431472379011374309723016488768812616461262878430516462983621905834360407048315144675590899661629294864970581053017811224060172015413211584159596727114517935294322664097235811837109649097996545870414588367457722049829882231989241738555454623119832403564124534809022132843617826514031543355356062528738150977154242986053677236005423066262040444791326483380941011134472122294978975118237987132787493761141011767768297506467776352330046103979923629526015683511020054782937237363762952201133896207225404489181293412875944827638025147017538335727100188688385 :=
    typed_comp_output typed_referenceTrialParameters Math115.ReferenceMetadata.typed_residualParameters referenceTrialParameters_output
  have hinput : Typed (pair (composition LatticeOuterProgram.trialParametersRealizer residualParametersRealizer)
      (second (A:=((ProfileConfiguration×List ProfileWord)×ℕ)) (B:=List Bool))) 12199682796582558701020431472379011374309723016488768812616461262878430516462983621905834360407048315144675590899661629294864970581053017811224060172015413211584159596727114517935294322664097235811837109649097996545870414588367457722049829882231989241738555454623119832403564124534809022132843617826514031543355356062528738150977154242986053677236005423066262040444791326483380941011134472122294978975118237987132787493761141011767768297506467776352330046103979923629526015683511020054782937237363762952201133896207225404489181293412875944827638025147017538335727100188688385 :=
    typed_pair hresidual typed_second
  have horesidual : OutputBound (fun z : LatticeOuterProgram.TrialData => residualParameters (LatticeOuterProgram.trialParameters z)) 635876136 :=
    outputBound_composition referenceTrialParameters_output (outputBound_of_typed Math115.ReferenceMetadata.typed_residualParameters)
  have hword : OutputBound (fun z : LatticeOuterProgram.TrialData => z.2) 1 := outputBound_of_typed typed_second
  unfold LatticeOuterProgram.trialCompletionRealizer
  exact typed_comp_output hinput typed_completionDraw (outputBound_pair horesidual hword)

lemma typed_referenceTrialOutputInput : Typed LatticeOuterProgram.trialOutputInputRealizer 12199682796582558701020431472379011374309723016488768812616461262878430516462983621905834360407048315144675590899661629294864970581053017811224060172015413211584159596727114517935294322664097235811837109649097996545870414588367457722049829882231989241738555454623119832403564124534809022132843617826514031543355356062528738150977154242986053677236005423066262040444791326483380941011134472122294978975118237987132787493761141011767768297506467776352330046103979923629526015683511020054782937237363762952201133896207225404489181293412875944827638025147017538335727100188688385 := by
  unfold LatticeOuterProgram.trialOutputInputRealizer
  exact typed_pair (typed_composition typed_referenceTrialParameters typed_first) typed_referenceTrialCompletion

lemma typed_referenceProfileTrial : Typed LatticeOuterProgram.profileTrialRealizer 198085795544716048011964128640640331627379666308076357564433351191134717012139364382486559662397686584294001145191014953053526689629812705731734202498390902590873917055974606631421474437183434550834071176042531469084258470557973090349616503991331912172397304374635797464708987959029235404918414126741027298623262998874347898287897026677592246588307368039149071916693979574756649933692689753469189070289057292196730141402380278793449359897347557283928018230275326214255776120212968755083388193121283193325087781955317637644590183191773851062575195908935379898552494223343972685018063840 := by
  unfold LatticeOuterProgram.profileTrialRealizer
  exact typed_composition typed_referenceTrialOutputInput Math115.UnitRuntimeNext.typed_outerTrial

/-- Exact remaining reference-trial seam. This is a single unconditional
numerical certificate for the original packed trial, including its supplied
word parser, cap-guarded profile walk, every step completion/proposal/translation,
independent terminal completion, original outer checks and encoded output.
All malformed dimensions, word lengths, catalogues and row values are included. -/
theorem typed_actual_packedTrial : Typed LatticeOuterProgram.packedTrialRealizer 249569086149969927754465653530857316378662151100210635200859836899115394502462433742952346464893494918298349218830740503411950490371359547202234848664532691737852411594490630793354441329305157924334049610980689568025133584089872528423843231844695041473652053370821139768976712765532769803598329631937527257644643545333786414444514615499205181845594806221996072304130411642154202278059154591154845186413464438667829092073424522772982022332107776812250045880396804598645709356960800186404581118066277180403051396836632512938969750164048642049142739626451320875705881681967964561744998704271360 := by
  unfold LatticeOuterProgram.packedTrialRealizer
  exact typed_composition typed_referencePrepareTrial typed_referenceProfileTrial

#check referenceTrialParameters_output
#print axioms referenceTrialParameters_output
#check typed_referenceTrialCompletion
#print axioms typed_referenceTrialCompletion
#check typed_actual_packedTrial
#print axioms typed_actual_packedTrial
end
end Math115.ReferenceRuntimeNext
