/-!
# The verified computation for `5040 < n ≤ exp(e^{30})`: executable part

This module imports only Lean core, so that it can be compiled to native code
(`precompileModules`) and evaluated at native speed by `native_decide`. Nothing here is trusted:
every function is a plain total definition, and `Robin/Compute/` proves what its output means.

Fixed point: a natural number `a` stands for `a / D` with `D = 2^96`.

## Pieces

* `logLoS r s`, `logUpS r s`: `D · log(1 + s/r)` from below and above, by the series
  `log(1 + 1/a) = Σ_k 2/(2k+1) · (1/(2a+1))^{2k+1}` (Mathlib's `Real.hasSum_log_one_add_inv`).
* `logLoQ u v`, `logUpQ u v`: `D · log(u/v)` for `u ≥ v > 0`, through `u/v = 2^k (1 + s/r)`.
* `sieveSeg`: a segmented sieve; a marked entry is a multiple `q·t` with `t ≥ q ≥ 2`, hence
  composite. Unmarked entries form a superset of the primes in the segment.
* `step`: process one segment `[B, B+h)`, accumulating upper bounds for `Σ log(1 + 1/m)` and
  lower bounds for `Σ log m` over unmarked `m`, then possibly a *checkpoint*: an exponent `ε`
  for which the colossally-abundant envelope `log(σ(n)/n) ≤ εx + C` (all `n`, `x = log n`)
  is checked against `γ + log log x` at the two ends of an interval of `x`.
-/

namespace RobinCompute

/-- Fixed-point scale. -/
def D : Nat := 2 ^ 96

/-- Scale for `x = log n` values. -/
def XS : Nat := 2 ^ 20

/-- Ceiling division. -/
def cdiv (a b : Nat) : Nat := (a + b - 1) / b

/-! ### Logarithms -/

/-- `k`-th term numerator/denominator of `2/(2k+1) z^{2k+1}`, `z = p/q`, scaled by `D`. -/
def termNum (p k : Nat) : Nat := 2 * D * p ^ (2 * k + 1)
def termDen (q k : Nat) : Nat := (2 * k + 1) * q ^ (2 * k + 1)

/-- Lower bound: partial sum of floors. -/
def seriesLo (p q : Nat) : Nat → Nat
  | 0 => 0
  | J + 1 => seriesLo p q J + termNum p J / termDen q J

/-- Upper bound: partial sum of ceilings plus the geometric tail
`2/(2J+1) · z^{2J+1}/(1 - z²)`. -/
def seriesUpPart (p q : Nat) : Nat → Nat
  | 0 => 0
  | J + 1 => seriesUpPart p q J + cdiv (termNum p J) (termDen q J)

def seriesUp (p q J : Nat) : Nat :=
  seriesUpPart p q J + cdiv (termNum p J * q ^ 2) (termDen q J * (q ^ 2 - p ^ 2))

/-- Number of series terms: stop once a term is below `1/D`, at most 200. -/
def nTerms (p q : Nat) : Nat := go 0 200
where
  go (k : Nat) : Nat → Nat
    | 0 => k
    | fuel + 1 => if termNum p k < termDen q k then k + 1 else go (k + 1) fuel

/-- `D · log(1 + s/r)` from below (`r > 0`). -/
def logLoS (r s : Nat) : Nat :=
  let q := 2 * r + s
  seriesLo s q (nTerms s q)

/-- `D · log(1 + s/r)` from above (`r > 0`). -/
def logUpS (r s : Nat) : Nat :=
  let q := 2 * r + s
  seriesUp s q (nTerms s q)

/-- `log 2 = log(1 + 1/1)`. -/
def log2Lo : Nat := logLoS 1 1
def log2Up : Nat := logUpS 1 1

/-- Largest `k` with `v · 2^k ≤ u` (for `v > 0`; at most 4096). -/
def log2Floor (u v : Nat) : Nat := go 0 4096
where
  go (k : Nat) : Nat → Nat
    | 0 => k
    | fuel + 1 => if v * 2 ^ (k + 1) ≤ u then go (k + 1) fuel else k

/-- `D · log(u/v)` from below, for `u ≥ v > 0`. -/
def logLoQ (u v : Nat) : Nat :=
  let k := log2Floor u v
  let r := v * 2 ^ k
  let s := u - r
  k * log2Lo + (if s = 0 then 0 else logLoS r s)

/-- `D · log(u/v)` from above, for `u ≥ v > 0`. -/
def logUpQ (u v : Nat) : Nat :=
  let k := log2Floor u v
  let r := v * 2 ^ k
  let s := u - r
  k * log2Up + (if s = 0 then 0 else logUpS r s)

def logLoNat (m : Nat) : Nat := logLoQ m 1

/-- A cheaper lower bound for `D · log m`: 12 series terms (relative error `< 3^{-25}`). -/
def logLoNatC (m : Nat) : Nat :=
  let k := log2Floor m 1
  let r := 2 ^ k
  let s := m - r
  k * log2Lo + (if s = 0 then 0 else seriesLo s (2 * r + s) 12)
def logUpNat (m : Nat) : Nat := logUpQ m 1

/-- `D · log log x` from below for `x = xn / XS` (`0` if `log x < 1` is not excluded). -/
def logLogLo (xn : Nat) : Nat := logLoQ (logLoQ xn XS) D

/-! ### Euler's constant -/

/-- `Σ_{j=1}^N ⌊D/j⌋`. -/
def harmLo : Nat → Nat
  | 0 => 0
  | N + 1 => harmLo N + D / (N + 1)

/-- Tail-recursive `harmLo` (what runs). -/
def harmAux : Nat → Nat → Nat
  | 0, acc => acc
  | N + 1, acc => harmAux N (acc + D / (N + 1))

/-- `γ ≥ H_N − log N − 1/(2N)`, scaled, as an integer (any `N ≥ 1`). -/
def gammaLoOf (N : Nat) : Int :=
  (harmAux N 0 : Int) - (logUpNat N : Int) - (cdiv D (2 * N) : Int)

/-- The lower bound for Euler's constant used everywhere. -/
def Gc : Int := gammaLoOf (2 ^ 20)

/-! ### Sieve -/

/-- Mark `j, j+q, …` below `hi` (array index `j - base`). -/
def markLoop (arr : ByteArray) (j q hi base : Nat) : ByteArray :=
  if j < hi then
    if q = 0 then arr else markLoop (arr.set! (j - base) 1) (j + q) q hi base
  else arr
termination_by hi - j

/-- Sieve with `sp[i], sp[i+1], …` (stopping at the first `q` with `q² ≥ hi`). -/
def sieveLoop (sp : Array Nat) (B hi : Nat) (i : Nat) (arr : ByteArray) : ByteArray :=
  if i < sp.size then
    let q := sp[i]!
    if hi ≤ q * q then arr else
      sieveLoop sp B hi (i + 1)
        (if 2 ≤ q then markLoop arr (max (q * q) (((B + q - 1) / q) * q)) q hi B else arr)
  else arr
termination_by sp.size - i

/-- Sieve `[B, B+h)` with the numbers in `sp` (any numbers; those `< 2` are skipped). -/
def sieveSeg (sp : Array Nat) (B h : Nat) : ByteArray :=
  sieveLoop sp B (B + h) 0 (ByteArray.mk (Array.replicate h 0))

/-- Numbers `2 ≤ q ≤ n` left unmarked by a simple sieve (used as sieving primes). -/
def smallPrimes (n : Nat) : Array Nat := Id.run do
  let arr := sieveSeg ((List.range (Nat.sqrt n + 2)).toArray) 0 (n + 1)
  let mut ps : Array Nat := #[]
  for i in [2:n+1] do
    if arr[i]! == 0 then ps := ps.push i
  return ps

/-! ### Scanning a sieved segment -/

/-- Exact mode: `Σ logUp1(m)` and `Σ logLoNat(m)` over unmarked `m = B + i`, `i < n`. -/
def scanExact (arr : ByteArray) (B : Nat) : Nat → Nat × Nat
  | 0 => (0, 0)
  | n + 1 =>
    let r := scanExact arr B n
    if arr[n]! == 0 then (r.1 + logUpS (B + n) 1, r.2 + logLoNatC (B + n)) else r

/-- Moment mode: count, `Σ i`, `Σ i²` over unmarked `B + i`, `i < n`. -/
def scanMom (arr : ByteArray) : Nat → Nat × Nat × Nat
  | 0 => (0, 0, 0)
  | n + 1 =>
    let r := scanMom arr n
    if arr[n]! == 0 then (r.1 + 1, r.2.1 + n, r.2.2 + n * n) else r

/-- Tail-recursive version of `scanMom` (what actually runs). -/
def scanMomTR (arr : ByteArray) (i n c s1 s2 : Nat) : Nat × Nat × Nat :=
  if i < n then
    if arr[i]! == 0 then scanMomTR arr (i + 1) n (c + 1) (s1 + i) (s2 + i * i)
    else scanMomTR arr (i + 1) n c s1 s2
  else (c, s1, s2)
termination_by n - i

/-- Upper bound for `D · Σ log(1+1/m)` over the segment from the moments: with
`b = 2B + 1`, `log(1 + 1/m) ≤ 2/(2m+1) + (2/3) z_B³/(1 − z_B²)` and
`2/(2m+1) = (2/b)/(1+t) ≤ (2/b)(1 − t + t²)`, `t = 2i/b`. -/
def momA (B c s1 s2 : Nat) : Nat :=
  let b := 2 * B + 1
  cdiv (2 * D * (c * b * b + 4 * s2 - 2 * s1 * b)) (b ^ 3) +
    c * cdiv (2 * D) (3 * b * (b * b - 1))

/-- Lower bound for `D · Σ log m` over the segment: `log(B + i) ≥ log B + i/B − i²/(2B²)`. -/
def momT (B c s1 s2 : Nat) : Nat :=
  c * logLoNatC B + (D * (2 * B * s1 - s2)) / (2 * B * B)

/-! ### State and checkpoints -/

structure St where
  /-- Every `m < B` has been processed. -/
  B : Nat
  /-- `≥ D · Σ_{m ∈ U} log(1 + 1/m)`. -/
  A : Nat
  /-- `≤ D · Σ_{m ∈ U} log m`. -/
  T : Nat
  /-- Robin's inequality holds for `x0 ≤ log n < cov / XS`. -/
  cov : Nat
  deriving DecidableEq, Repr

/-- Segment length at `B`: `2^{⌊log₂ B⌋ − 10}`, between `1` and `2^22`. -/
def segLen (B : Nat) : Nat := 2 ^ (min 22 (Nat.log2 B - 10))

/-- Exact mode below `2^26`. -/
def exactLimit : Nat := 2 ^ 26

/-- Extras for the prime powers: for unmarked `m < Q` (`m ≥ 2`), the positive parts of
`εd · logUp1(a_j) − εn · logLo(m)`, `a_j = m + m² + ⋯ + m^{j+1}`, `j ≥ 1`, stopping at the
first non-positive one (at most 64 terms). Scaled by `D · εd`. -/
def extrasFor (εn εd m : Nat) : Option Nat := go (εn * logLoNatC m) (m + m * m) (m * m) 64 0
where
  go (l a pk : Nat) : Nat → Nat → Option Nat
    | 0, _ => none
    | fuel + 1, acc =>
      let r := εd * logUpS a 1
      if l < r then go l (a + pk * m) (pk * m) fuel (acc + (r - l)) else some acc

def extrasScan (arr : ByteArray) (εn εd : Nat) : Nat → Option Nat
  | 0 => some 0
  | n + 1 =>
    match extrasScan arr εn εd n with
    | none => none
    | some r =>
      if 2 ≤ n ∧ arr[n]! == 0 then (extrasFor εn εd n).map (r + ·) else some r

/-- Tail-recursive `extrasScan` (what runs). Written with `Option.bind` rather than a `match`
with the recursive call inside, which keeps its equation lemmas cheap to generate. -/
def extrasScanTR (arr : ByteArray) (εn εd : Nat) : Nat → Nat → Option Nat
  | 0, acc => some acc
  | n + 1, acc =>
    (if 2 ≤ n ∧ arr[n]! == 0 then (extrasFor εn εd n).map (acc + ·) else some acc).bind
      (fun a => extrasScanTR arr εn εd n a)

def extras (εn εd Q : Nat) : Option Nat :=
  extrasScanTR (sieveSeg ((List.range (Nat.sqrt Q + 2)).toArray) 0 Q) εn εd Q 0

/-- The line check at `x = xn / XS`: `ε x + C < γ + log log x`, all scaled by `D · εd · XS`,
where `C · D · εd = Cn` (an integer) and `G ≤ D γ`. -/
def lineOK (G : Int) (εn εd : Nat) (Cn : Int) (xn : Nat) : Bool :=
  XS ≤ xn && D < logLoQ xn XS &&
  ((εn * xn * D : Nat) : Int) + Cn * (XS : Int) <
    (G + (logLogLo xn : Int)) * ((εd * XS : Nat) : Int)

/-- Largest `Q`-candidate with `1/Q² ≤ ε log Q` roughly: `Q = ⌈√(D εd / (εn ℓ))⌉ + 1`. -/
def chooseQ (εn εd : Nat) (lB : Nat) : Nat :=
  Nat.sqrt (D * εd / (εn * (lB / 2) + 1)) + 2

/-- Checkpoint data that depends only on the boundary `B`: the exponent `ε = εn/εd`, the
cut-off `Q` for prime powers, and the prime-power extras `E` (scaled by `D · εd`). -/
structure CK where
  εn : Nat
  εd : Nat
  Q : Nat
  E : Nat
  deriving Repr, DecidableEq

def ckEps (B : Nat) : Option CK :=
  let e1 := logLoS (B - 1) 1     -- ≤ D log(1 + 1/(B-1))
  let lb := logUpNat (B - 1)     -- ≥ D log(B-1)
  let e2 := logUpS B 1           -- ≥ D log(1 + 1/B)
  let la := logLoNat B           -- ≤ D log B
  -- ε = e1 / lb
  if 3 ≤ B ∧ 0 < lb ∧ 0 < e1 ∧ e2 * lb ≤ e1 * la then
    let Q := chooseQ e1 lb la
    -- validity of Q: D εd ≤ Q² εn logLo(Q), i.e. 1 ≤ Q² ε log Q; and Q ≤ B
    if 2 ≤ Q ∧ Q ≤ B ∧ D * lb ≤ Q * Q * e1 * logLoNat Q then
      match extras e1 lb Q with
      | none => none
      | some E => some ⟨e1, lb, Q, E⟩
    else none
  else none

/-- `C · D · εd` for the state `s`. -/
def cnOf (s : St) (ck : CK) : Int :=
  ((s.A * ck.εd : Nat) : Int) - ((ck.εn * s.T : Nat) : Int) + (ck.E : Int)

/-- Search the largest `hi ∈ [lo, lo + 2^e]` passing `lineOK`, by doubling and bisection. -/
def searchHi (ok : Nat → Bool) (lo : Nat) : Nat :=
  let rec grow (d : Nat) : Nat → Nat
    | 0 => d
    | fuel + 1 => if ok (lo + 2 * d) then grow (2 * d) fuel else d
  let d := grow 1 80
  let rec bis (a b : Nat) : Nat → Nat
    | 0 => a
    | fuel + 1 =>
      if b ≤ a + 1 then a else
      let c := (a + b) / 2
      if ok (lo + c) then bis c b fuel else bis a c fuel
  lo + bis d (2 * d) 80

/-- Apply checkpoint data: if the line passes at `lo = cov` and at the found `hi`, extend `cov`. -/
def applyCk (G : Int) (s : St) (ck : CK) : St :=
  let ok := lineOK G ck.εn ck.εd (cnOf s ck)
  if ok s.cov then
    let hi := searchHi ok s.cov
    if ok hi ∧ s.cov < hi then { s with cov := hi } else s
  else s

def checkpoint (G : Int) (s : St) : St :=
  match ckEps s.B with
  | none => s
  | some ck => applyCk G s ck

/-- Checkpoint spacing `2^{⌊(3/4) log₂ B⌋}`, below the width `≈ 1.2 x^{3/4}` of the interval a
checkpoint covers (heuristic only: the proofs do not care where checkpoints are). -/
def ckStep (B : Nat) : Nat := 2 ^ (3 * Nat.log2 B / 4)

def wantCk (B : Nat) : Bool := B < 2 ^ 12 || B % ckStep B == 0

/-- Process the segment `[B, B + segLen B)`. -/
def segStep (sp : Array Nat) (s : St) : St :=
  let B := s.B
  let h := segLen B
  let arr := sieveSeg sp B h
  if B + h ≤ exactLimit then
    let r := scanExact arr B h
    { s with B := B + h, A := s.A + r.1, T := s.T + r.2 }
  else
    let r := scanMomTR arr 0 h 0 0 0
    { s with B := B + h, A := s.A + momA B r.1 r.2.1 r.2.2, T := s.T + momT B r.1 r.2.1 r.2.2 }

/-- Run segments until `B ≥ Bend` (`fuel` bounds the number of segments). -/
def run (G : Int) (sp : Array Nat) (Bend : Nat) : Nat → St → St
  | 0, s => s
  | fuel + 1, s =>
    if s.B < Bend then
      let s1 := segStep sp s
      let s2 := if wantCk s1.B then checkpoint G s1 else s1
      run G sp Bend fuel s2
    else s

/-- The chunk computation from `s` to `Bend`, with sieving numbers up to `√Bend`. -/
def runChunk (G : Int) (s : St) (Bend : Nat) : St :=
  run G (smallPrimes (Nat.sqrt Bend + 1)) Bend Bend s

/-! ### Direct check for small `n` -/

/-- `σ(n)` by trial division. -/
def sigmaNat (n : Nat) : Nat := go n 0
where
  go : Nat → Nat → Nat
    | 0, acc => acc
    | d + 1, acc => go d (if n % (d + 1) = 0 then acc + (d + 1) else acc)

/-- `log σ(n) < log n + γ + log log log n`, certified. -/
def directOK (n : Nat) : Bool :=
  let L1 := logLoNat n
  let L2 := logLoQ L1 D
  let L3 := logLoQ L2 D
  2 ≤ n && D < L1 && D < L2 &&
    (logUpNat (sigmaNat n) : Int) < (L1 : Int) + Gc + (L3 : Int)

end RobinCompute
