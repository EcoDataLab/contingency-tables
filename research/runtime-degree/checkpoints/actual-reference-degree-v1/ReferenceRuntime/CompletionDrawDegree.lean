import ReferenceRuntime.DenseDrawDegree
import ReferenceRuntime.CompletionReservationDegree

namespace Math115.ReferenceRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS.TreeTyped Polynomial
open Math115.DegreeBounds DensePrograms
set_option maxHeartbeats 1600000
noncomputable section

lemma typed_completionTrial : Typed CompletionSamplerProgram.trialRealizer 89609402001286431396220945870027846032851675337726013627526613234516359774301873172609264188487055717773071433481175462486861152715803481897679824329823422090283532481908466029949443892958403960893422410587613299981842077922377682566079328727423200012043066102382592 := by
  unfold CompletionSamplerProgram.trialRealizer Realizer.fst Realizer.snd
  exact typed_composition
    (typed_pair
      (typed_composition typed_first typed_first)
      (typed_composition
        (typed_pair (typed_composition typed_first typed_second) typed_second) typed_canonicalDenseDraw)) typed_decode

/-- Original lattice completion sampler, including eager dense draws, rejected
prefix-floor decodes, every supplied reserved trial, and the binary greedy
coarse fallback. Arbitrary raw margins, dimensions, precisions and words are
included; no feasibility or successful-output premise is introduced. -/
theorem typed_completionDraw : Typed CompletionSamplerProgram.drawRealizer 396528349890136264877226803784534982738225119577744530704129784156836684820378968682894968317903441006016924735789805668509771579679636606961793253865919704688276667741814087759610045388787018456732041112125287604232858549277687123294639645825353687644951017360848894019722277876168622520927319863626123946883307428401806666194510128093390705540277302880395808907949491309942447682838872282521004076014045393165359626911890735793005365565805825706587175614160951934663307705712328446547359009982148248621108956728434478711599519739647679399965286724921737609216 := by
  unfold CompletionSamplerProgram.drawRealizer Realizer.fst
  exact typed_composition
    (typed_pair
      (typed_pair (typed_composition typed_first typed_completionPrepare)
        (typed_composition (typed_composition typed_first typed_first) Math115.InitialRuntimeNext.typed_actual_greedyTable))
      typed_completionReservedWords)
    (Math115.DrawDegree.typed_firstSuccessRetry typed_completionTrial (by decide))

#check typed_completionTrial
#print axioms typed_completionTrial
#check typed_completionDraw
#print axioms typed_completionDraw
end
end Math115.ReferenceRuntimeNext
