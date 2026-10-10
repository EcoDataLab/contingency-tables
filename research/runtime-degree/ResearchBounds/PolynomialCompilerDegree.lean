/- Pure polynomial algebra for the exact expression in pinned
   ContingencyTables/Machines/FiniteWordMachine.machineTime_polynomial.
   This module does not import that machine or assert a runtime bound. -/
import ResearchBounds.TreeDegreeBounds

namespace Math115.DegreeBounds
open Polynomial

def blockBudget (w H : ℕ) (p q : Polynomial ℕ) : Polynomial ℕ :=
  (p+1)*(C (3+w+H)+2*(q+p*C (H+w)))

def physicalEnvelope (width packCost eraseCost unpackCost accesses overhead : ℕ)
    (p : Polynomial ℕ) : Polynomial ℕ :=
  let pk := (1+blockBudget 1 (18*width) X 0)*C packCost
  let out := C eraseCost+(1+blockBudget (18*width) 1 p 0)*C unpackCost
  let fac := C overhead*(1+2*C accesses*(X+p*C accesses+1))+1
  pk+p*fac+out

lemma blockBudget_degree (w H : ℕ) {p : Polynomial ℕ} {e : ℕ}
    (hp : p.natDegree≤e) : (blockBudget w H p 0).natDegree≤2*e := by
  unfold blockBudget
  have h1 : (p+1).natDegree≤e := natDegree_add_le_of_degree_le hp (by simp)
  have h2 : (p*C (H+w)).natDegree≤e := by
    simpa using degree_mul hp (show (C (H+w) : Polynomial ℕ).natDegree≤0 by simp)
  have h3 : (0+p*C (H+w)).natDegree≤e := by simpa using h2
  have h4 : (C (3+w+H)+2*(0+p*C (H+w))).natDegree≤e :=
    natDegree_add_le_of_degree_le (by simp) (degree_scale 2 h3)
  simpa [two_mul] using degree_mul h1 h4

theorem physicalEnvelope_degree (width packCost eraseCost unpackCost accesses overhead : ℕ)
    {p : Polynomial ℕ} {e : ℕ} (hp : p.natDegree≤e) (he : 1≤e) :
    (physicalEnvelope width packCost eraseCost unpackCost accesses overhead p).natDegree≤2*e := by
  have hpk : ((1+blockBudget 1 (18*width) X 0)*C packCost).natDegree≤2 := by
    have h1 := blockBudget_degree 1 (18*width) (show (X : Polynomial ℕ).natDegree≤1 by simp)
    have h2 : (1+blockBudget 1 (18*width) X 0).natDegree≤2 :=
      natDegree_add_le_of_degree_le (by simp) h1
    simpa using degree_mul h2 (show (C packCost : Polynomial ℕ).natDegree≤0 by simp)
  have hout : (C eraseCost+(1+blockBudget (18*width) 1 p 0)*C unpackCost).natDegree≤2*e := by
    apply natDegree_add_le_of_degree_le (by simp)
    have h1 : (1+blockBudget (18*width) 1 p 0).natDegree≤2*e :=
      natDegree_add_le_of_degree_le (by simp) (blockBudget_degree _ _ hp)
    simpa using degree_mul h1 (show (C unpackCost : Polynomial ℕ).natDegree≤0 by simp)
  have hfac : (C overhead*(1+2*C accesses*(X+p*C accesses+1))+1 : Polynomial ℕ).natDegree≤e := by
    have h1 : (p*C accesses).natDegree≤e := by
      simpa using degree_mul hp (show (C accesses : Polynomial ℕ).natDegree≤0 by simp)
    have h2 : (X+p*C accesses+1).natDegree≤e :=
      natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le (by simpa using he) h1) (by simp)
    have h3 : (2*C accesses*(X+p*C accesses+1)).natDegree≤e := by
      have hc : (2*C accesses : Polynomial ℕ).natDegree≤0 := by simp
      simpa using degree_mul hc h2
    exact natDegree_add_le_of_degree_le
      (degree_scale overhead (natDegree_add_le_of_degree_le (by simp) h3)) (by simp)
  unfold physicalEnvelope
  exact natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (hpk.trans (by omega))
      (by simpa [two_mul] using degree_mul hp hfac)) hout

/-- Includes the degree-zero input case; no positivity of p is assumed. -/
theorem physicalEnvelope_degree_max (width packCost eraseCost unpackCost accesses overhead : ℕ)
    (p : Polynomial ℕ) :
    (physicalEnvelope width packCost eraseCost unpackCost accesses overhead p).natDegree≤
      2*max 1 p.natDegree :=
  physicalEnvelope_degree _ _ _ _ _ _ (le_max_right _ _) (le_max_left _ _)

end Math115.DegreeBounds
