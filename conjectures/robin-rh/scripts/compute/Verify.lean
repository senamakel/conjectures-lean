import RobinCompute.Core
open RobinCompute
def parse (l : String) : St :=
  let w := (l.splitOn " ").toArray
  ⟨w[0]!.toNat!, w[1]!.toNat!, w[2]!.toNat!, w[3]!.toNat!⟩
def main (args : List String) : IO Unit := do
  let i := args[0]!.toNat!
  let ls ← IO.FS.lines args[1]!
  let s := parse ls[i]!
  let e := parse ls[i+1]!
  let t0 ← IO.monoMsNow
  let r := runChunk Gc s ((i + 1) * 2 ^ 34)
  let t1 ← IO.monoMsNow
  IO.println s!"chunk {i}: match={decide (r = e)} ms={t1 - t0} cov {r.cov} vs {e.cov}"
