import OAI.Combinatorics.ContingencyTables.Transport.IntegerLeafEnergy
import Math115.GlobalDisplayOwnership

/-! The independent ownership abstraction uses exactly upstream unit removal. -/

namespace Math115.GlobalDisplayOwnership

lemma eraseUnit_eq_removeOne {C : Type*} [DecidableEq C] (D : C → ℕ) (i : C) :
    eraseUnit D i = OAI.ContingencyTables.FactorialSignatures.removeOne D i := rfl

theorem edge_owner_unique_upstream {S : Type*} [DecidableEq S]
    (U : S → ℕ) (s s' : S) (D D' : S × Bool → ℕ)
    (i j i' j' : S × Bool) (hij : i ≠ j) (hij' : i' ≠ j')
    (hs : IsSpecialDisplay U s D) (hs' : IsSpecialDisplay U s' D')
    (he : SameUnorderedPair
      (OAI.ContingencyTables.FactorialSignatures.removeOne D i)
      (OAI.ContingencyTables.FactorialSignatures.removeOne D j)
      (OAI.ContingencyTables.FactorialSignatures.removeOne D' i')
      (OAI.ContingencyTables.FactorialSignatures.removeOne D' j')) :
    D = D' ∧ s = s' ∧ D (s, false) = D' (s', false) := by
  apply edge_owner_unique U s s' D D' i j i' j' hij hij' hs hs'
  simpa only [eraseUnit_eq_removeOne] using he

end Math115.GlobalDisplayOwnership
