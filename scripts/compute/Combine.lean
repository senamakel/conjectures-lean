import RobinCompute.Core
open RobinCompute
/-- Read pass-1 outputs out/c0000 .. and produce chunk boundary states. -/
def main (args : List String) : IO Unit := do
  let n := args[0]!.toNat!
  let x0 := args[1]!.toNat!
  let outp := args[2]!
  let G := Gc
  let mut s : St := ⟨2, 0, 0, x0⟩
  let mut states : Array St := #[s]
  let mut nck := 0
  let mut nfail := 0
  for i in [0:n] do
    let f := s!"out/c{if i < 10 then "000" else if i < 100 then "00" else "0"}{i}"
    let lines ← IO.FS.lines f
    let A0 := s.A
    let T0 := s.T
    for l in lines do
      let w := (l.splitOn " ").toArray
      if w[0]! == "C" then
        let B := w[1]!.toNat!
        let s1 : St := ⟨B, A0 + w[2]!.toNat!, T0 + w[3]!.toNat!, s.cov⟩
        let ck : CK := ⟨w[4]!.toNat!, w[5]!.toNat!, w[6]!.toNat!, w[7]!.toNat!⟩
        let s2 := applyCk G s1 ck
        nck := nck + 1
        if s2.cov == s1.cov then nfail := nfail + 1
        s := s2
      else if w[0]! == "END" then
        s := ⟨w[1]!.toNat!, A0 + w[2]!.toNat!, T0 + w[3]!.toNat!, s.cov⟩
      else if w[0]! == "N" then
        IO.println s!"ckEps none at {w[1]!}"
    states := states.push s
  IO.println s!"checkpoints {nck}, non-extending {nfail}"
  IO.println s!"final B={s.B} cov={s.cov / XS} (cov/XS ≈ {s.cov.toFloat / XS.toFloat}) T/D≈{s.T.toFloat / D.toFloat}"
  let h ← IO.FS.Handle.mk outp .write
  for st in states do
    h.putStrLn s!"{st.B} {st.A} {st.T} {st.cov}"
