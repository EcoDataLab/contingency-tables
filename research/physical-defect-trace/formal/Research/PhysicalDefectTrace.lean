import Research.PhysicalTraceGeometry
import Research.PhysicalTraceIrreflexive
import Research.WeightedHarmonicTrace

namespace Math115.PhysicalDefectTrace

open OAI.ContingencyTables OAI.CommonBasesFPRAS
open scoped BigOperators Classical
open PhysicalCompletionFibres FirstPaperProfiles FirstPaperPhysicalMarginal
open PaddedCompletions CompletionCounts SmallContextCoordinates SmallContextFibres
open SmallGraphProfiles FiniteExposureVariance CompletionTranslation RowMajorEnumeration
open Math115.ReducedSmallChain Math115.ReducedAllSmallChain

universe u
variable {I J : Type u} [Fintype I] [Fintype J] [LinearOrder I] [LinearOrder J]
noncomputable section

def balancedWeight (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (b : BalancedVertices r c U L) : ℝ :=
  weight r c U L b.val

def defectWeight (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (d : DefectVertices r c U L) : ℝ :=
  weight r c U L d.val

def ddConductance (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (d e : DefectVertices r c U L) : ℝ := acceptedConductance r c U L d.val e.val

def crossConductance (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (b : BalancedVertices r c U L) (d : DefectVertices r c U L) : ℝ :=
  acceptedConductance r c U L b.val d.val

def splitAccepted (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (x y : BalancedVertices r c U L ⊕ DefectVertices r c U L) : ℝ :=
  acceptedConductance r c U L (partitionEquiv r c U L x) (partitionEquiv r c U L y)

def splitMinimum (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (x y : BalancedVertices r c U L ⊕ DefectVertices r c U L) : ℝ :=
  minimumConductance r c U L (partitionEquiv r c U L x) (partitionEquiv r c U L y)

lemma accepted_balanced_balanced_zero (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (b b' : BalancedVertices r c U L) : acceptedConductance r c U L b.val b'.val=0 :=
  acceptedConductance_off_edge r c U L b.val b'.val
    (physicalAdjacent_no_balanced_balanced r c U L b.val b'.val b.property b'.property)

lemma fullConductance_actual (r : I → ℕ) (c : J → ℕ) (U L : ℕ) :
    Research.WeightedHarmonicTrace.fullConductance (ddConductance r c U L) (crossConductance r c U L)=
      splitAccepted r c U L := by
  exact Research.WeightedHarmonicTrace.fullConductance_of_blocks (splitAccepted r c U L)
    (fun x y => acceptedConductance_symmetric r c U L _ _)
    (fun b b' => accepted_balanced_balanced_zero r c U L b b')

lemma variance_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (w H : Y → ℝ) :
    variance (fun x => w (e x)) (fun x => H (e x))=variance w H := by
  unfold variance mean
  rw [e.sum_comp (fun y => w y*H y),e.sum_comp w]
  exact e.sum_comp (fun y => w y*(H y-(∑ j,w j*H j)/(∑ j,w j))^2)

lemma matrixEnergy_equiv {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (M : Y → Y → ℝ) (H : Y → ℝ) :
    Research.WeightedHarmonicTrace.graphEnergy (fun x y => M (e x) (e y)) (fun x => H (e x))=
      Research.WeightedHarmonicTrace.graphEnergy M H := by
  unfold Research.WeightedHarmonicTrace.graphEnergy
  apply congrArg (fun t : ℝ => t/2)
  calc
    _ = ∑ x : X,∑ y : Y,M (e x) y*(H (e x)-H y)^2 := by
      apply Finset.sum_congr rfl
      intro x _
      exact e.sum_comp (fun y => M (e x) y*(H (e x)-H y)^2)
    _ = _ := e.sum_comp (fun x => ∑ y,M x y*(H x-H y)^2)

lemma split_variance_identity (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (F : BalancedVertices r c U L ⊕ DefectVertices r c U L → ℝ) :
    variance (Sum.elim (balancedWeight r c U L) (defectWeight r c U L)) F=
      variance (weight r c U L) (fun x => F ((partitionEquiv r c U L).symm x)) := by
  let e := partitionEquiv r c U L
  have h := variance_equiv e (weight r c U L) (fun x => F (e.symm x))
  simp only [Equiv.symm_apply_apply] at h
  have hw : (fun x => weight r c U L (e x))=Sum.elim (balancedWeight r c U L) (defectWeight r c U L) := by
    funext x
    cases x <;> rfl
  rw [hw] at h
  exact h

lemma split_energy_identity (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (F : BalancedVertices r c U L ⊕ DefectVertices r c U L → ℝ) :
    Research.WeightedHarmonicTrace.graphEnergy (splitMinimum r c U L) F=
      graphEnergy r c U L (fun x => F ((partitionEquiv r c U L).symm x)) := by
  let e := partitionEquiv r c U L
  have h := matrixEnergy_equiv e (minimumConductance r c U L) (fun x => F (e.symm x))
  simp only [Equiv.symm_apply_apply] at h
  rw [graphEnergy_minimum_matrix]
  exact h

lemma split_full_variance_square (r : I → ℕ) (c : J → ℕ) (U L : ℕ)
    (hU : 2≤U) (hp : 2≤Fintype.card (Cells (firstPaperSmall r c U)))
    (F : BalancedVertices r c U L ⊕ DefectVertices r c U L → ℝ) :
    variance (Sum.elim (balancedWeight r c U L) (defectWeight r c U L)) F ≤
      (2*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^3*(U:ℝ)^2)*
        Research.WeightedHarmonicTrace.graphEnergy (splitMinimum r c U L) F := by
  rw [split_variance_identity,split_energy_identity]
  exact Math115.RetainedRepairSquare.state_variance_square r c U L hU hp _

lemma split_half_accepted (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (hL : 7≤L) :
    ∀ x y,splitMinimum r c U L x y/2 ≤
      Research.WeightedHarmonicTrace.fullConductance (ddConductance r c U L) (crossConductance r c U L) x y := by
  rw [fullConductance_actual]
  intro x y
  exact half_minimum_accepted r c U L hL _ _

lemma cross_dd_row_identity (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (d : DefectVertices r c U L) :
    (∑ e,ddConductance r c U L d e)+(∑ b,crossConductance r c U L b d)=
      ∑ y,acceptedConductance r c U L d.val y := by
  have he := (partitionEquiv r c U L).sum_comp (fun y => acceptedConductance r c U L d.val y)
  rw [Fintype.sum_sum_type] at he
  have hb : (∑ b,crossConductance r c U L b d)=∑ b : BalancedVertices r c U L,
      acceptedConductance r c U L d.val b.val := by
    apply Finset.sum_congr rfl
    intro b _
    exact acceptedConductance_symmetric r c U L b.val d.val
  rw [hb]
  exact (add_comm _ _).trans he

lemma accepted_defect_row_of_degree (r : I → ℕ) (c : J → ℕ) (U L Q : ℕ)
    (hdegree : ∀ d : DefectVertices r c U L,
      (Finset.univ.filter (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) d.val)).card≤Q) :
    ∀ d,(∑ e,ddConductance r c U L d e)+(∑ b,crossConductance r c U L b d)≤
      (Q:ℝ)*defectWeight r c U L d := by
  intro d
  rw [cross_dd_row_identity]
  exact (acceptedConductance_row_degree r c U L d.val).trans
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hdegree d) (weight_positive r c U L d.val).le)

/-- Exact rational accepted trace on actual positive defects. This constructor
still exposes the actual geometric D-neighbor bound as an explicit input. -/
def rationalPhysicalTrace (r : I → ℕ) (c : J → ℕ) (U L Q : ℕ)
    [Nonempty (DefectVertices r c U L)] (hQ : 1≤Q)
    (hdegree : ∀ d : DefectVertices r c U L,
      (Finset.univ.filter (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) d.val)).card≤Q) :
    FiniteChain (DefectVertices r c U L) :=
  Research.WeightedHarmonicTrace.rationalChain (defectWeight r c U L)
    (ddConductance r c U L) (crossConductance r c U L)
    (fun d => weight_positive r c U L d.val)
    (fun d e => acceptedConductance_nonnegative r c U L d.val e.val)
    (fun d e => acceptedConductance_symmetric r c U L d.val e.val)
    (fun b d => acceptedConductance_nonnegative r c U L b.val d.val) Q hQ
    (accepted_defect_row_of_degree r c U L Q hdegree)


lemma ddConductance_diag_zero (r : I → ℕ) (c : J → ℕ) (U L : ℕ) (d : DefectVertices r c U L) :
    ddConductance r c U L d d=0 := acceptedConductance_diag_zero r c U L d.val

lemma rationalPhysicalTrace_pi (r : I → ℕ) (c : J → ℕ) (U L Q : ℕ)
    [Nonempty (DefectVertices r c U L)] (hQ : 1≤Q)
    (hdegree : ∀ d : DefectVertices r c U L,
      (Finset.univ.filter (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) d.val)).card≤Q)
    (d : DefectVertices r c U L) :
    (rationalPhysicalTrace r c U L Q hQ hdegree).π d=
      defectWeight r c U L d/(∑ e,defectWeight r c U L e) := rfl

lemma rationalPhysicalTrace_lazy (r : I → ℕ) (c : J → ℕ) (U L Q : ℕ)
    [Nonempty (DefectVertices r c U L)] (hQ : 1≤Q)
    (hdegree : ∀ d : DefectVertices r c U L,
      (Finset.univ.filter (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) d.val)).card≤Q)
    (d : DefectVertices r c U L) : 1/2≤(rationalPhysicalTrace r c U L Q hQ hdegree).P d d :=
  (rationalPhysicalTrace r c U L Q hQ hdegree).lazy d

lemma rationalPhysicalTrace_move (r : I → ℕ) (c : J → ℕ) (U L Q : ℕ)
    [Nonempty (DefectVertices r c U L)] (hQ : 1≤Q)
    (hdegree : ∀ d : DefectVertices r c U L,
      (Finset.univ.filter (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) d.val)).card≤Q)
    (d e : DefectVertices r c U L) (hne : d≠e) :
    (rationalPhysicalTrace r c U L Q hQ hdegree).P d e=
      (1/(2*(Q:ℝ)))*Research.WeightedHarmonicTrace.traceConductance
        (ddConductance r c U L) (crossConductance r c U L) d e/defectWeight r c U L d := by
  simp only [rationalPhysicalTrace,Research.WeightedHarmonicTrace.rationalChain,
    Research.WeightedHarmonicTrace.traceChain,FiniteChain.ofMoves,
    Research.WeightedHarmonicTrace.traceMove,ite_eq_right hne,add_zero]

/-- All physical variance, capacity, decomposition and acceptance premises
are discharged. Only the genuine neighbor-count geometry remains explicit;
the actual degree module will instantiate that final premise. -/
theorem rationalPhysicalTrace_square_of_degree (r : I → ℕ) (c : J → ℕ) (U L Q : ℕ)
    [Nonempty (DefectVertices r c U L)] (hU : 2≤U) (hL : 7≤L)
    (hp : 2≤Fintype.card (Cells (firstPaperSmall r c U))) (hQ : 1≤Q)
    (hQp : Q≤4*Fintype.card (Cells (firstPaperSmall r c U))-3)
    (hdegree : ∀ d : DefectVertices r c U L,
      (Finset.univ.filter (physicalAdjacent r c U L (capacity r c U L) (capacity_small r c U L) d.val)).card≤Q)
    (g : DefectVertices r c U L → ℝ) :
    (rationalPhysicalTrace r c U L Q hQ hdegree).variance g ≤
      (32*(Fintype.card (Cells (firstPaperSmall r c U)):ℝ)^4*(U:ℝ)^2)*
        (rationalPhysicalTrace r c U L Q hQ hdegree).energy g :=
  Research.WeightedHarmonicTrace.width_square_rational_trace
    (balancedWeight r c U L) (defectWeight r c U L)
    (fun b => (weight_positive r c U L b.val).le) (fun d => weight_positive r c U L d.val)
    (ddConductance r c U L) (crossConductance r c U L)
    (fun d e => acceptedConductance_nonnegative r c U L d.val e.val)
    (fun d e => acceptedConductance_symmetric r c U L d.val e.val)
    (fun b d => acceptedConductance_nonnegative r c U L b.val d.val)
    _ U Q hQ hQp (accepted_defect_row_of_degree r c U L Q hdegree) (splitMinimum r c U L)
    (split_full_variance_square r c U L hU hp) (split_half_accepted r c U L hL) g

end
end Math115.PhysicalDefectTrace

#print axioms Math115.PhysicalDefectTrace.rationalPhysicalTrace_square_of_degree
