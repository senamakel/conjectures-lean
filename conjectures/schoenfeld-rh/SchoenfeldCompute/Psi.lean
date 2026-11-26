/-!
# The PsiCert computation on `(10⁶, 10¹⁰]`: executable part

Lean core only, so that `precompileModules` compiles it to native code for `native_decide`.
Nothing here is trusted; `Schoenfeld/PsiCert/` proves what the output means.

Fixed point: a natural number `v` stands for `v / D`, `D = 2^96`.

* `logLoS r s`, `logUpS r s`: `D · log(1 + s/r)` from below and above (the `artanh` series of
  Mathlib's `Real.hasSum_log_one_add_inv`). These and the sieve loops `markLoop`, `sieveLoop`,
  `sieveSeg` are copied from robin-rh (`RobinCompute/Core.lean` at `343518c`, same authors).
* `basePrimes`: the numbers `2 ≤ q ≤ 131072` left unmarked by a sieve with `0, …, 363`.
* `ppMark`: marks each proper prime power `q^k` (`k ≥ 2`) of a segment with its exponent `k`.
* `segStep`: one segment `(L, L + w]`, cut into blocks `(a, a + B]`. Over a block, the state's
  enclosures of `D ψ(a)` and `D log a` are advanced (`Λ(n) ∈ [log a/k, log b/k]` for `n = p^k`
  in the block) and the two guards `ψ(b) − a ≤ (4/5)√a` and `b − ψ(a) ≤ (4/5)√a` are checked
  in integers, whenever `b > A0 = 10⁶`.
-/

namespace SchoenfeldCompute

/-- Fixed-point scale. -/
def D : Nat := 2 ^ 96

/-- Ceiling division. -/
def cdiv (a b : Nat) : Nat := (a + b - 1) / b

/-! ### Logarithms (from robin-rh) -/

def termNum (p k : Nat) : Nat := 2 * D * p ^ (2 * k + 1)
def termDen (q k : Nat) : Nat := (2 * k + 1) * q ^ (2 * k + 1)

def seriesLo (p q : Nat) : Nat → Nat
  | 0 => 0
  | J + 1 => seriesLo p q J + termNum p J / termDen q J

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

/-! ### Sieve (from robin-rh) -/

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

/-- Sieve `[B, B+h)` with the numbers in `sp` (those `< 2` are skipped). -/
def sieveSeg (sp : Array Nat) (B h : Nat) : ByteArray :=
  sieveLoop sp B (B + h) 0 (ByteArray.mk (Array.replicate h 0))

/-- Bound for the base primes. -/
def baseMax : Nat := 131072

/-- The sieve that produces the base primes. -/
def baseArr : ByteArray := sieveSeg (List.range 364).toArray 0 (baseMax + 1)

/-- The primes up to `baseMax`. -/
def basePrimes : Array Nat :=
  ((List.range (baseMax + 1)).filter (fun i => 2 ≤ i && baseArr[i]! == 0)).toArray

/-! ### Proper prime powers -/

/-- Mark `pk = q^k, q^{k+1}, …` below `hi` (index `pk - base`, when `pk ≥ base`) with their
exponents. -/
def ppLoop (q hi base : Nat) : Nat → Nat → Nat → ByteArray → ByteArray
  | 0, _, _, pw => pw
  | fuel + 1, pk, k, pw =>
    if pk < hi then
      ppLoop q hi base fuel (pk * q) (k + 1)
        (if base ≤ pk then pw.set! (pk - base) (UInt8.ofNat k) else pw)
    else pw

/-- Mark the proper powers of `sp[i], sp[i+1], …` (stopping at the first `q` with `q² ≥ hi`). -/
def ppSieve (sp : Array Nat) (base hi : Nat) (i : Nat) (pw : ByteArray) : ByteArray :=
  if i < sp.size then
    let q := sp[i]!
    if hi ≤ q * q then pw else
      ppSieve sp base hi (i + 1) (if 2 ≤ q then ppLoop q hi base 40 (q * q) 2 pw else pw)
  else pw
termination_by sp.size - i

/-- Exponents of the proper prime powers in `[base, base + h)`. -/
def ppMark (sp : Array Nat) (base h : Nat) : ByteArray :=
  ppSieve sp base (base + h) 0 (ByteArray.mk (Array.replicate h 0))

/-! ### Blocks and segments -/

/-- Enclosures after processing every `n ≤ a`: `plo ≤ D ψ(a) ≤ phi`, `llo ≤ D log a ≤ lhi`. -/
structure PS where
  a : Nat
  plo : Nat
  phi : Nat
  llo : Nat
  lhi : Nat
  deriving DecidableEq, Repr

/-- Add `D Λ(base + t)` bounds over `t, t+1, …, t + c − 1`, with `llo ≤ D log` and
`lhi ≥ D log` of every number in the range. -/
def scanBlk (arr pw : ByteArray) (llo lhi : Nat) : Nat → Nat → Nat → Nat → Nat × Nat
  | _, 0, plo, phi => (plo, phi)
  | t, c + 1, plo, phi =>
    if arr[t]! == 0 then scanBlk arr pw llo lhi (t + 1) c (plo + llo) (phi + lhi)
    else
      let k := pw[t]!.toNat
      if k == 0 then scanBlk arr pw llo lhi (t + 1) c plo phi
      else scanBlk arr pw llo lhi (t + 1) c (plo + llo / k) (phi + cdiv lhi k)

/-- The two guards on `[a, b]`: `ψ(b) − a ≤ (4/5)√a` and `b − ψ(a) ≤ (4/5)√a`. -/
def guardOK (a b plo phi' : Nat) : Bool :=
  (phi' ≤ a * D || 25 * ((phi' - a * D) * (phi' - a * D)) ≤ 16 * a * (D * D)) &&
    (b * D ≤ plo || 25 * ((b * D - plo) * (b * D - plo)) ≤ 16 * a * (D * D))

/-- Start of the checked range. -/
def A0 : Nat := 1000000

/-- One block `(a, a + B]` of the segment whose sieve arrays start at `base`. -/
def blockStep (arr pw : ByteArray) (base B : Nat) (st : PS) : Option PS :=
  let a := st.a
  let b := a + B
  let lhiB := st.lhi + logUpS a B
  let lloB := st.llo + logLoS a B
  let r := scanBlk arr pw st.llo lhiB (a + 1 - base) B st.plo st.phi
  if b ≤ A0 || guardOK a b st.plo r.2 then some ⟨b, r.1, r.2, lloB, lhiB⟩ else none

/-- `n` blocks of length `B`. -/
def blkLoop (arr pw : ByteArray) (base B : Nat) : Nat → PS → Option PS
  | 0, st => some st
  | n + 1, st => (blockStep arr pw base B st).bind (blkLoop arr pw base B n)

/-- Segment length at `L`: up to `10⁶` first, then `2^20`. -/
def segLen (L : Nat) : Nat := if L < A0 then A0 - L else 2 ^ 20

/-- Block length at `L`: `1` below `2^18`, then `2^{⌊log₂ L⌋/2 − 8}` (about `√L/256`). -/
def blkLen (L : Nat) : Nat := if L < 2 ^ 18 then 1 else 2 ^ (Nat.log2 L / 2 - 8)

/-- One segment `(L, L + w]` starting from the state at `L`. -/
def segStep (sp : Array Nat) (st : PS) : Option PS :=
  let L := st.a
  let w := segLen L
  let B := blkLen L
  if 1 ≤ L && 0 < B && w % B == 0 && L + w + 1 ≤ (baseMax + 1) * (baseMax + 1) &&
      L + w + 1 ≤ 2 ^ 40 then
    let arr := sieveSeg sp (L + 1) w
    let pw := ppMark sp (L + 1) w
    blkLoop arr pw (L + 1) B (w / B) st
  else none

/-- `n` segments. -/
def runSegs (sp : Array Nat) : Nat → PS → Option PS
  | 0, st => some st
  | n + 1, st => (segStep sp st).bind (runSegs sp n)

/-- The initial state at `a = 1`: `ψ(1) = 0`, `log 1 = 0`. -/
def init : PS := ⟨1, 0, 0, 0, 0⟩

end SchoenfeldCompute
