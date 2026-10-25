import Lake

/- Preparation only: caller supplies an independently checked list of existing
package-cache artifact paths. This creates/refreshes only their Lake .hash
sidecars using the pinned official binary hashing implementation. -/
def main (args : List String) : IO UInt32 := do
  let some request := args.head? | throw <| IO.userError "Need owned artifact request"
  let paths ← IO.FS.lines request
  let mut count : Nat := 0
  for path in paths do
    if !path.isEmpty then
      Lake.cacheFileHash (System.FilePath.mk path) (text := false)
      count := count + 1
  IO.println s!"MATH115_MEMO_NORMALIZED={count}"
  return 0
