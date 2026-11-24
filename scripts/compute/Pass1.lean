import RobinCompute.Core
open RobinCompute
partial def loop (h : IO.FS.Handle) (sp : Array Nat) (B1 : Nat) (s : St) : IO St := do
  if s.B < B1 then
    let s1 := segStep sp s
    if wantCk s1.B then
      match ckEps s1.B with
      | none => h.putStrLn s!"N {s1.B}"
      | some c => h.putStrLn s!"C {s1.B} {s1.A} {s1.T} {c.εn} {c.εd} {c.Q} {c.E}"
    loop h sp B1 s1
  else return s
def main (args : List String) : IO Unit := do
  let B0 := args[0]!.toNat!
  let B1 := args[1]!.toNat!
  let out := args[2]!
  let t0 ← IO.monoMsNow
  let h ← IO.FS.Handle.mk (out ++ ".tmp") .write
  let sp := smallPrimes (Nat.sqrt B1 + 1)
  let s ← loop h sp B1 ⟨B0, 0, 0, 0⟩
  let t1 ← IO.monoMsNow
  h.putStrLn s!"END {s.B} {s.A} {s.T} {t1 - t0}"
  h.flush
  IO.FS.rename (out ++ ".tmp") out
