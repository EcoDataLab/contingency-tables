import Math115.LatticeCompletionProgram
open Math115.LatticeCompletionProgram

def checkCodec (name : String) (b : Bool) : IO Unit := do
  unless b do throw (IO.userError name)
  IO.println s!"PASS {name}"

#eval checkCodec "empty matrix" (decode (3, []) == some [])
#eval checkCodec "zero columns" (decode (3, [[]]) == some [[]])
#eval checkCodec "zero divisor rejects nonempty" (decode (0, [[9]]) == none)
#eval checkCodec "single accepted cell" (decode (3, [[9]]) == some [[1]])
#eval checkCodec "negative signed cell rejects" (decode (3, [[5]]) == none)
#eval checkCodec "balanced 2x2" (decode (3, [[6,6],[6,6]]) == some [[0,0],[0,0]])
#eval checkCodec "nonsymmetric 2x2 order" (decode (3, [[9,12],[6,9]]) == some [[1,2],[0,1]])
#eval checkCodec "ragged total semantics" (decode (3, [[6],[6,6]]) == some [[0],[0,0]])
#eval checkCodec "huge binary divisor bounded by input shape"
  (decode (2^100, [[0]]) == none)
