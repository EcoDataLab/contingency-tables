import Math115.CompletionBooleanRetry

open Math115.CompletionBooleanRetry

def coarse : Fin 2 → Fin 2 → Nat := fun i j => if i = j then 1 else 0
def digits : Math115.LatticeCompletion.FiniteDigits 2 2 3 := fun _ _ => ⟨2, by decide⟩
def fine : Fin 2 → Fin 2 → Nat := encodeCells 3 coarse digits

def rejected : Fin 2 → Fin 2 → Nat := fun i j => if i = j then 0 else 15

def matrixRows (X : Fin 2 → Fin 2 → Nat) : List (List Nat) :=
  List.ofFn (fun i => List.ofFn (X i))

#eval matrixRows fine
#eval (rawTrial 3 fine).map matrixRows
#eval (rawTrial 3 rejected).map matrixRows
#eval flatRetry (q := 1) (fun w => if w 0 then some (7 : Nat) else none) 99 3
  (fun i => decide (i.val = 2))
#eval flatRetry (q := 1) (fun w => if w 0 then some (7 : Nat) else none) 99 3
  (fun _ => false)
#eval flatRetry (q := 0) (fun _ => none (α := Nat)) 99 0 (Fin.elim0)
