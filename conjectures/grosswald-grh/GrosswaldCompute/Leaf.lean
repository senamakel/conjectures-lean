import GrosswaldCompute.Seg

/-!
# The leaf check of Algorithm 1 (core Lean only)

A leaf of `Grosswald.Alg.checkNode` enumerates `p = k P + 1` for `k ∈ [k0, k0 + cnt)`, where
`P = ∏ X`. `leafOk X Y P k0 cnt` checks every such `k`: some `q ∈ Y` divides `k`, or the
base-2 Fermat test fails for `p`, or a prime `g ∈ gPrimes` with `g + 3 ≤ ⌊√p⌋` passes Lucas'
test against `X`, the primes of `k` below `B` and the cofactor, or a trial divisor of `p` is
found. The factor lists of `k` come from an untrusted sieve over blocks of consecutive `k`,
checked as in `segOk` (`cwOk`, `progAllK`). Soundness: `Grosswald/Alg.lean`.
-/

namespace GrosswaldCompute

/-- `fl[i]` = the primes `q < B` dividing `c + i`. -/
def buildFlK (c L B : Nat) (cw : Array Nat) : Array (List Nat) := Id.run do
  let mut fl : Array (List Nat) := Array.replicate L []
  for q in [2:B] do
    if cw.getD q 1 == 0 then
      let mut j := (q - c % q) % q
      while j < L do
        fl := fl.modify j (q :: ·)
        j := j + q
  return fl

/-- Along `j, j + q, …` (below `L`, at most `f` steps): `q ∈ fl[j]`. -/
def progOkK (q L : Nat) (fl : Array (List Nat)) : Nat → Nat → Bool
  | _, 0 => true
  | j, f + 1 => if j < L then (fl.getD j []).contains q && progOkK q L fl (j + q) f else true

/-- For every `q ∈ [lo, lo + k)` with `cw[q] = 0`: the offset is right and its progression
is covered. -/
def progAllK (c L : Nat) (cw : Array Nat) (fl : Array (List Nat)) : Nat → Nat → Bool
  | _, 0 => true
  | q, k + 1 =>
    (cw.getD q 1 != 0 ||
      (let j0 := (q - c % q) % q
       j0 < q && (c + j0) % q == 0 && progOkK q L fl j0 (L / q + 1))) &&
      progAllK c L cw fl (q + 1) k

/-- Trial-division primality. -/
def isPrimeTD (q : Nat) : Bool :=
  2 ≤ q && (List.range q).all (fun d => d < 2 || q < d * d || q % d != 0)

/-- The primes below `2000`, tried as primitive roots (in increasing order). -/
def gPrimes : List Nat := (List.range 2000).filter isPrimeTD

/-- Some `g ∈ gs` with `g + 3 ≤ s` passes Lucas' test. -/
def lucasAny (p m s : Nat) (ts : List Nat) : List Nat → Bool
  | [] => false
  | g :: gs => (g + 3 ≤ s && lucas p m g ts) || lucasAny p m s ts gs

/-- Untrusted: a divisor `d ∈ [2, ⌊√p⌋]` of `p`, searching from `d` for `f` steps, or `0`. -/
def trialDiv (p : Nat) : Nat → Nat → Nat
  | _, 0 => 0
  | d, f + 1 => if p < d * d then 0 else if p % d == 0 then d else trialDiv p (d + 1) f

/-- The check of one `k` (with `fl` the listed primes of `k`). -/
def candK (X Y : List Nat) (P B s k : Nat) (fl : List Nat) : Bool :=
  let p := k * P + 1
  Y.any (fun q => k % q == 0) || Nat.powMod 2 (p - 1) p != 1 ||
    (fl.all (fun q => 2 ≤ q && q < B) &&
      (let r := fl.foldl (fun r q => divOut q r 64) k
       lucasAny p (p - 1) s (X ++ (if 1 < r then r :: fl else fl)) gPrimes)) ||
    (let d := trialDiv p 2 (Nat.sqrt p)
     1 < d && d < p && p % d == 0)

/-- `candK` for `i ∈ [i0, i0 + k)`, `k = c + i`. -/
def candAll (X Y : List Nat) (P B s c : Nat) (fl : Array (List Nat)) : Nat → Nat → Bool
  | _, 0 => true
  | i, k + 1 => candK X Y P B s (c + i) (fl.getD i []) && candAll X Y P B s c fl (i + 1) k

/-- One block `k ∈ [c, c + L)`. -/
def blockOk (X Y : List Nat) (P c L : Nat) : Bool :=
  let B := Nat.sqrt (c + L) + 1
  let s := Nat.sqrt (c * P + 1)
  let cw := buildCw B
  let fl := buildFlK c L B cw
  cwOk cw 2 (B - 2) && progAllK c L cw fl 2 (B - 2) && candAll X Y P B s c fl 0 L

/-- Block length. -/
def blockLen : Nat := 4194304

/-- All `k ∈ [c, c + cnt)`, in blocks (at most `f` of them). -/
def leafBlocks (X Y : List Nat) (P : Nat) : Nat → Nat → Nat → Bool
  | _, _, 0 => false
  | c, cnt, f + 1 =>
    if cnt ≤ blockLen then blockOk X Y P c cnt
    else blockOk X Y P c blockLen && leafBlocks X Y P (c + blockLen) (cnt - blockLen) f

/-- The leaf check. -/
def leafOk (X Y : List Nat) (P k0 cnt : Nat) : Bool :=
  0 < k0 && leafBlocks X Y P k0 cnt (cnt / blockLen + 1)

end GrosswaldCompute
