/-!
# Executable checkers for the finite range (core Lean only, precompiled)

This module imports nothing beyond Lean's core, so that Lake compiles it to native code
(`precompileModules`) and `native_decide` evaluates it at native speed. Nothing here is trusted:
the soundness theorems in `Goldbach.Compute.Sieve`, `Goldbach.Compute.Binary` and
`Goldbach.Compute.Ladder` (which import Mathlib) say what a `true` result means.

* `markFrom`, `sieve`: an odd-only segmented sieve of Eratosthenes. Byte `i` of
  `sieve lo len ps` is `1` exactly when no `p ∈ ps` divides `lo + 2 i` other than `lo + 2 i`
  itself.
* `goldbachChunk`: binary Goldbach for the even numbers of a range, by looking up `m − p` in a
  sieve segment for the small odd primes `p ≤ P`.
* `ladderCover`: a chain of primes with consecutive gaps at most `G`, each certified by
  Pocklington's criterion with a prime-power part `F = p^e > √c` of `c − 1`
  (`p ≤ 31` prime).
-/

namespace Goldbach.Check

/-! ## The sieve -/

/-- Set bytes `j, j + p, j + 2p, … < len` of `a` to `0`. -/
def markFrom (p len : Nat) (a : ByteArray) (j : Nat) : ByteArray :=
  if j < len ∧ 0 < p then markFrom p len (a.set! j 0) (j + p) else a
termination_by len - j
decreasing_by omega

/-- The index (in the odd-only segment starting at the odd number `lo`) of the least odd
multiple of the odd number `p` that is `≥ max lo (3 p)`. -/
def firstIdx (lo p : Nat) : Nat :=
  let s := max lo (3 * p)
  let k := (s + p - 1) / p
  let k := if k % 2 = 0 then k + 1 else k
  (p * k - lo) / 2

/-- Odd-only segment sieve: byte `i` stands for `lo + 2 i`. -/
def sieve (lo len : Nat) (ps : List Nat) : ByteArray :=
  ps.foldl (fun a p => markFrom p len a (firstIdx lo p)) ⟨Array.replicate len 1⟩

/-- The odd numbers `3, 5, …, 2 r + 1`. -/
def oddsUpTo (r : Nat) : List Nat := (List.range r).map (fun i => 2 * i + 3)

/-- The unmarked odd numbers in `[3, 3 + 2 len)` after sieving by the odd numbers
`3, …, 2 r + 1`: the odd primes there, when `(2 r + 3)² > 3 + 2 len`. -/
def basePrimes (len r : Nat) : List Nat :=
  let s := sieve 3 len (oddsUpTo r)
  (List.range len).filterMap (fun i => if s[i]! == 1 then some (3 + 2 * i) else none)

/-- `⌈√H⌉`. -/
def sqrtUp (H : Nat) : Nat := Id.run do
  let mut b := Nat.sqrt H
  while b * b < H do b := b + 1
  return b

/-! ## Binary Goldbach -/

/-- Is the even `m` equal to `p + x` with `p ∈ qs` and `x` an unmarked entry of the segment
`seg` (odd-only, from `lo`, of length `len`)? -/
def hasRep (seg : ByteArray) (lo len : Nat) (qs : List Nat) (m : Nat) : Bool :=
  qs.any fun p => decide (lo + p ≤ m) && decide ((m - p - lo) / 2 < len) &&
    seg[(m - p - lo) / 2]! == 1

/-- `allEven f m k`: `f` holds at `m, m + 2, …, m + 2 (k − 1)`. -/
def allEven (f : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | m, k + 1 => f m && allEven f (m + 2) k

/-- The start of the sieve segment for the even numbers from `A`. -/
def segLo (P A : Nat) : Nat := if P + 3 ≤ A then A - P else 3

/-- One segment: every even `m ∈ [A, A + 2 k)` is `p + x`, `p ∈ qs`, `x` an unmarked odd number
of the sieve of `[segLo P A, A + 2 k)` by `ps`. -/
def goldbachSeg (ps qs : List Nat) (P A k : Nat) : Bool :=
  let lo := segLo P A
  let len := (A + 2 * k - lo) / 2
  let seg := sieve lo len ps
  allEven (hasRep seg lo len qs) A k

/-- `n` consecutive segments of `k` even numbers each, from `A`. -/
def goldbachFrom (ps qs : List Nat) (P k : Nat) : Nat → Nat → Bool
  | _, 0 => true
  | A, n + 1 => goldbachSeg ps qs P A k && goldbachFrom ps qs P k (A + 2 * k) n

/-- The full chunk check: every even `m ∈ [A, A + 2 k n)` is a sum of two primes, the smaller
one an odd prime `≤ P`. Base primes: the odd primes up to `max P ⌈√(A + 2kn)⌉`. -/
def goldbachChunk (P A k n : Nat) : Bool :=
  let H := A + 2 * k * n
  let B := sqrtUp H
  let len := max B P / 2 + 1
  let r := sqrtUp (3 + 2 * len) / 2 + 1
  let ps := basePrimes len r
  let qs := ps.filter (· ≤ P)
  A % 2 == 0 && P % 2 == 1 && decide (6 ≤ A) && decide (H ≤ B * B) &&
    decide (3 + 2 * len < (2 * r + 3) * (2 * r + 3)) &&
    goldbachFrom ps qs P k A n

/-! ## The prime ladder -/

/-- `acc * b ^ e % m`, by binary exponentiation. -/
def powModAux (m : Nat) (b e acc : Nat) : Nat :=
  if e = 0 then acc % m
  else powModAux m (b * b % m) (e / 2) (if e % 2 = 1 then acc * b % m else acc)
termination_by e
decreasing_by omega

/-- `b ^ e % m`. -/
def powMod (b e m : Nat) : Nat := powModAux m (b % m) e 1

/-- Pocklington's criterion with `F = p ^ e`: `F ∣ c − 1`, `F² > c`, `a^(c−1) ≡ 1` and
`gcd(a^((c−1)/p) − 1, c) = 1`. For a prime `p` and `e ≥ 1` this proves `c` prime. -/
def pockOK (c p e a : Nat) : Bool :=
  let F := p ^ e
  decide (0 < e) && decide (2 ≤ c) && decide (c < F * F) && (c - 1) % F == 0 &&
    powMod a (c - 1) c == 1 && Nat.gcd ((powMod a ((c - 1) / p) c + c - 1) % c) c == 1

/-- The bases `p` of the prime powers `F = p^e` the ladder uses. -/
def ladderBases : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31]

/-- Witnesses `a` tried for Pocklington's criterion. -/
def witnesses : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37]

/-- Small primes used to discard candidates before the Fermat test. -/
def filterPrimes : List Nat := [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
  67, 71, 73, 79, 83, 89, 97]

/-- The least `e` with `p^(2e) > t` (for `p ≥ 2`). -/
def expFor (p t : Nat) : Nat := Id.run do
  let mut e := 1
  while p ^ (2 * e) ≤ t do e := e + 1
  return e

/-- A witness `a` for the candidate `c = k p^e + 1`, if one is found (untrusted search). -/
def findWitness (c p e : Nat) : Option Nat :=
  if filterPrimes.any (fun q => c % q == 0) then none
  else if powMod 2 (c - 1) c != 1 then none
  else witnesses.find? (fun a => pockOK c p e a)

/-- Search `c' = k p^e + 1` for `k = k₀, k₀ − 1, …` while `c' > lo` (untrusted search). -/
def searchDown (lo p e F : Nat) : Nat → Nat → Option (Nat × Nat × Nat × Nat)
  | _, 0 => none
  | k, fuel + 1 =>
    let c := k * F + 1
    if c ≤ lo then none
    else match findWitness c p e with
      | some a => some (c, p, e, a)
      | none => searchDown lo p e F (k - 1) fuel

/-- The next rung above `c`: a certified prime in `(c, c + G]` (untrusted search). -/
def nextRung (c G : Nat) : Option (Nat × Nat × Nat × Nat) :=
  let t := c + G
  ladderBases.firstM fun p =>
    let e := expFor p t
    let F := p ^ e
    searchDown c p e F ((t - 1) / F) (G / F + 1)

/-- One checked rung: `c'` is a Pocklington-certified prime in `(c, c + G]`. -/
def rungOK (G c c' p e a : Nat) : Bool :=
  pockOK c' p e a && ladderBases.contains p && decide (c < c') && decide (c' ≤ c + G)

/-- Climb the ladder from `c` until a rung `≥ hi` is reached, re-checking each rung. -/
def ladderTo (G hi : Nat) : Nat → Nat → Bool
  | c, 0 => decide (hi ≤ c)
  | c, f + 1 =>
    if hi ≤ c then true
    else match nextRung c G with
      | some (c', p, e, a) => rungOK G c c' p e a && ladderTo G hi c' f
      | none => false

/-- `ladderCover G lo hi`: a certified prime `c ∈ (lo − G, lo]` (found by `nextRung`) and a
ladder from `c` to beyond `hi`. Then every `y ∈ [lo, hi]` has a prime `q ≤ y` with
`y < q + G`. -/
def ladderCover (G lo hi : Nat) : Bool :=
  match nextRung (lo - G) G with
  | some (c, p, e, a) => pockOK c p e a && ladderBases.contains p && decide (c ≤ lo) &&
      ladderTo G hi c (hi + 1)
  | none => false

end Goldbach.Check
