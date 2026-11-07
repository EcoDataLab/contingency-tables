import Research.PhysicalTraceGeometry
import Research.PhysicalAcceptedConductance

namespace Math115.PhysicalDefectTrace
open OAI.ContingencyTables
open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts SmallContextCoordinates SmallContextFibres
open SmallGraphProfiles FiniteExposureVariance CompletionTranslation RowMajorEnumeration
open IntegerWeightedTransport FactorialSignatures SmallContextEnumeration
open Math115.ReducedSmallChain

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

/-- The actual exchange/repair graph has no self edges, on balanced or defect
states. Thus masking by actual adjacency also masks raw accepted self counts. -/
theorem physicalAdjacent_irreflexive (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x : States r c U L) :
    ¬physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) x x := by
  intro hxx
  rcases Finset.mem_union.mp hxx with hex|hrp
  · obtain ⟨D,i,j,hij,hi,_hj,hx,hy⟩ := (Finset.mem_filter.mp hex).2
    exact hij (removeOne_injective_valid D i j hi (hx.symm.trans hy))
  · rcases Finset.mem_union.mp hrp with hfw|hbw
    · obtain ⟨z,_,he⟩ := Finset.mem_image.mp hfw
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      dsimp only at h1 h2
      have hnat := h1.trans h2.symm
      have hb := rawChoice_balanced (firstPaperSmall r c U) (capacity r c U L) U
        (capacity_small r c U L) (wordChoices _ U (repairWord r c U L _ (capacity_small r c U L) z))
      have hd := (congrArg (SingleDefect (firstPaperSmall r c U) (capacity r c U L)) hnat).mp z.property.1
      exact balanced_not_defect _ _ _ hb hd
    · obtain ⟨z,_,he⟩ := Finset.mem_image.mp hbw
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      dsimp only at h1 h2
      have hnat := h2.trans h1.symm
      have hb := rawChoice_balanced (firstPaperSmall r c U) (capacity r c U L) U
        (capacity_small r c U L) (wordChoices _ U (repairWord r c U L _ (capacity_small r c U L) z))
      have hd := (congrArg (SingleDefect (firstPaperSmall r c U) (capacity r c U L)) hnat).mp z.property.1
      exact balanced_not_defect _ _ _ hb hd

lemma acceptedConductance_diag_zero (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (x : States r c U L) :
    acceptedConductance r c U L x x=0 :=
  acceptedConductance_off_edge r c U L x x (physicalAdjacent_irreflexive r c U L x)

end
end Math115.PhysicalDefectTrace
#print axioms Math115.PhysicalDefectTrace.acceptedConductance_diag_zero
