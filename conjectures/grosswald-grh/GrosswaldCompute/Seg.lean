/-!
# A segmented checker for the finite range (core Lean only)

`segOk a L` checks the odd numbers `n = a + 2 i`, `i < L`. For each one it either finds a
witness `w` with `1 < w < n`, `w ∣ n`, or a primitive root `g` with `g + 3 ≤ ⌊√a⌋` by Lucas'
test against a list of numbers containing every prime factor of `n - 1`.

The arrays (`cw`, `wit`, `fl`) and the starting offsets are computed by untrusted sieves.
Only the Boolean checks `cwOk`, `progAll`, `numAll` matter for correctness; their soundness is
proved in `Grosswald/SegSound.lean`.
-/

namespace GrosswaldCompute

/-! ### Untrusted builders -/

/-- `cw[q] = 0` for the primes `q < B`, otherwise a divisor of `q` (a sieve). -/
def buildCw (B : Nat) : Array Nat := Id.run do
  let mut cw : Array Nat := Array.replicate B 0
  for i in [2:B] do
    if cw.getD i 1 == 0 then
      let mut j := i * i
      while j < B do
        if cw.getD j 1 == 0 then cw := cw.set! j i
        j := j + i
  return cw

/-- The first index `j < q` with `q ∣ c + 2 j` (for odd `q`). -/
def start (c q : Nat) : Nat := ((q - c % q) % q * ((q + 1) / 2)) % q

/-- `wit[i]` = an odd prime `q < B` dividing `a + 2 i` (and `≠ a + 2 i`), or `0`. -/
def buildWit (a L B : Nat) (cw : Array Nat) : Array Nat := Id.run do
  let mut wit : Array Nat := Array.replicate L 0
  for q in [3:B] do
    if q % 2 == 1 && cw.getD q 1 == 0 then
      let mut j := start a q
      while j < L do
        if wit.getD j 0 == 0 && a + 2 * j != q then wit := wit.set! j q
        j := j + q
  return wit

/-- `fl[i]` = the odd primes `q < B` dividing `a + 2 i - 1` (only where `wit[i] = 0`). -/
def buildFl (a L B : Nat) (cw wit : Array Nat) : Array (List Nat) := Id.run do
  let mut fl : Array (List Nat) := Array.replicate L []
  for q in [3:B] do
    if q % 2 == 1 && cw.getD q 1 == 0 then
      let mut j := start (a - 1) q
      while j < L do
        if wit.getD j 0 == 0 then fl := fl.modify j (q :: ·)
        j := j + q
  return fl

/-! ### Checks -/

/-- Every `q ∈ [lo, lo + k)` has `cw[q] = 0` or a proper divisor `cw[q]`. -/
def cwOk (cw : Array Nat) : Nat → Nat → Bool
  | _, 0 => true
  | q, k + 1 =>
    (cw.getD q 1 == 0 || (1 < cw.getD q 1 && cw.getD q 1 < q && q % cw.getD q 1 == 0)) &&
      cwOk cw (q + 1) k

/-- Along `j, j + q, …` (below `L`, at most `f` steps): `wit[j] ≠ 0` or `q ∈ fl[j]`. -/
def progOk (q L : Nat) (wit : Array Nat) (fl : Array (List Nat)) : Nat → Nat → Bool
  | _, 0 => true
  | j, f + 1 =>
    if j < L then (wit.getD j 0 != 0 || (fl.getD j []).contains q) && progOk q L wit fl (j + q) f
    else true

/-- For every odd `q ∈ [lo, lo + k)` with `cw[q] = 0`: the offset `j0 = start (a - 1) q` is
correct and the progression from it is covered. -/
def progAll (a L : Nat) (cw wit : Array Nat) (fl : Array (List Nat)) : Nat → Nat → Bool
  | _, 0 => true
  | q, k + 1 =>
    (q % 2 == 0 || cw.getD q 1 != 0 ||
      (let j0 := start (a - 1) q
       j0 < q && (a - 1 + 2 * j0) % q == 0 && progOk q L wit fl j0 (L / q + 1))) &&
      progAll a L cw wit fl (q + 1) k

/-- Divide `r` by `q` as long as possible (at most `f` times). -/
def divOut (q : Nat) : Nat → Nat → Nat
  | r, 0 => r
  | r, f + 1 => if r % q == 0 && 0 < r then divOut q (r / q) f else r

/-- Lucas' test of `g` for `n` against the list `ts`. -/
def lucas (n m g : Nat) (ts : List Nat) : Bool :=
  ts.all (fun t => m % t != 0 || Nat.powMod g (m / t) n != 1) && Nat.powMod g m n == 1

/-- Search `g ∈ [g, g + f)` with `g + 3 ≤ s` passing Lucas' test. -/
def findRoot (n m s : Nat) (ts : List Nat) : Nat → Nat → Bool
  | _, 0 => false
  | g, f + 1 => (g + 3 ≤ s && lucas n m g ts) || (g + 3 < s && findRoot n m s ts (g + 1) f)

/-- The check of `n` given its witness slot `w` and factor list `fs` (odd primes of `n - 1`). -/
def numOk (B s n w : Nat) (fl : List Nat) : Bool :=
  if w != 0 then 1 < w && w < n && n % w == 0
  else
    let m := n - 1
    let fs := 2 :: fl
    fs.all (fun q => 2 ≤ q && q < B) &&
      (let r := fs.foldl (fun r q => divOut q r 64) m
       findRoot n m s (if 1 < r then r :: fs else fs) 2 s)

/-- `numOk` for `i ∈ [i0, i0 + k)`. -/
def numAll (a B s : Nat) (wit : Array Nat) (fl : Array (List Nat)) : Nat → Nat → Bool
  | _, 0 => true
  | i, k + 1 => numOk B s (a + 2 * i) (wit.getD i 0) (fl.getD i []) && numAll a B s wit fl (i + 1) k

/-- The segment check for the odd numbers `a + 2 i`, `i < L`. -/
def segOk (a L : Nat) : Bool :=
  let B := Nat.sqrt (a + 2 * L) + 1
  let s := Nat.sqrt a
  let cw := buildCw B
  let wit := buildWit a L B cw
  let fl := buildFl a L B cw wit
  cwOk cw 2 (B - 2) && progAll a L cw wit fl 3 (B - 3) && numAll a B s wit fl 0 L

/-- `segOk` on `S` consecutive segments of `L` odd numbers starting at `a`. -/
def segsOk (L : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | a, S + 1 => segOk a L && segsOk L (a + 2 * L) S

end GrosswaldCompute
