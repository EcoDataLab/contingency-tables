import PrinterRuntime.LinearCollections
import OAI.Combinatorics.ContingencyTables.Sampling.GreedyPublicProgram

namespace Math115.PrinterRuntimeNext
open OAI OAI.ContingencyTables OAI.MatchingFPRAS OAI.MatchingFPRAS.TreeTyped
open OAI.MatchingFPRAS.LiteralCodec Polynomial Math115.DegreeBounds
noncomputable section

lemma typed_fromBit : Typed LiteralCodec.fromBitRealizer 1 := by
  unfold LiteralCodec.fromBitRealizer
  exact typed_choose typed_identity (typed_constant (2 : Symbol)) (typed_constant (1 : Symbol)) (by decide)

lemma affine_fromBit : AffineOutput LiteralCodec.fromBit := by
  refine ⟨0,17,fun b => ?_⟩
  simp only [zero_mul,zero_add,LiteralCodec.weight_symbol]
  exact le_rfl

lemma affine_bits : AffineOutput Nat.bits := by
  refine ⟨1,0,fun n => ?_⟩
  simp only [one_mul,add_zero,weight_nat]
  exact le_rfl

lemma affine_natWord : AffineOutput LiteralCodec.natWord := by
  refine ⟨18,19,fun n => ?_⟩
  rw [LiteralCodec.weight_word]
  simp only [LiteralCodec.natWord,List.length_append,List.length_map,List.length_singleton]
  have h := size_le_weight n
  rw [Nat.size_eq_bits_len]
  nlinarith

/-- Exact bits/map/append program with its encoded Symbol output charged. -/
theorem typed_actual_natWord : Typed LiteralCodec.natWordRealizer 2 := by
  have hmap : Typed (TreeTyped.map LiteralCodec.fromBitRealizer) 2 :=
    typed_map_affine typed_fromBit (by decide) affine_fromBit
  have hbits : Typed (composition toBits (TreeTyped.map LiteralCodec.fromBitRealizer)) 2 := by
    simpa using typed_comp_affine Math115.DegreeBounds.typed_toBits hmap affine_bits
  have harg : Typed (pair (composition toBits (TreeTyped.map LiteralCodec.fromBitRealizer))
      (constant ([3] : List Symbol))) 2 :=
    typed_pair_same hbits (typed_weaken (typed_constant ([3] : List Symbol)) (by decide)) (by decide)
  have hargout : AffineOutput (fun n : ℕ => (n.bits.map LiteralCodec.fromBit,([3] : List Symbol))) := by
    refine ⟨18,40,fun n => ?_⟩
    rw [weight_prod,LiteralCodec.weight_word,LiteralCodec.weight_word]
    simp only [List.length_map,List.length_singleton]
    have h := size_le_weight n
    rw [Nat.size_eq_bits_len]
    nlinarith
  unfold LiteralCodec.natWordRealizer
  apply typed_congr
  exact typed_comp_affine harg typed_append hargout

lemma typed_actual_printRow : Typed (flatMapPoly LiteralCodec.natWordRealizer) 3 := by
  simpa using typed_flatMapPoly_affine typed_actual_natWord (by decide) affine_natWord

lemma affine_printRow : AffineOutput (List.flatMap LiteralCodec.natWord) :=
  affine_flatMap affine_natWord

/-- Global actual printer certificate. No feasibility, equal-total,
rectangularity, successful parse, or assumed printer-cost premise is used. -/
theorem typed_actual_printMatrix : Typed GreedyFeasibleTable.printMatrixRealizer 4 := by
  have h := typed_flatMapPoly_affine typed_actual_printRow (by decide) affine_printRow
  obtain ⟨p,hp,hpb⟩ := h
  refine ⟨p,(by simpa using hp),fun rows => ?_⟩
  have hn : (LiteralCodec.natWord : ℕ → List Symbol) = encodeNat := by
    funext n
    exact LiteralCodec.natWord_eq n
  have heq : List.flatMap (List.flatMap LiteralCodec.natWord) rows =
      rows.flatMap (fun row => row.flatMap encodeNat) := by
    rw [hn]
  change (flatMapPoly (flatMapPoly LiteralCodec.natWordRealizer)).cost rows +
    weight (rows.flatMap (fun row => row.flatMap encodeNat)) ≤ p.eval (weight rows)
  rw [← heq]
  exact hpb rows

theorem actual_printMatrix_polynomial :
    ∃ p : Polynomial ℕ, p.natDegree ≤ 4 ∧
      ∀ rows : List (List ℕ), GreedyFeasibleTable.printMatrixRealizer.cost rows +
        weight (GreedyFeasibleTable.printMatrix rows) ≤ p.eval (weight rows) :=
  typed_actual_printMatrix

end
end Math115.PrinterRuntimeNext
