import AnkenyCheck

/-!
# Executable checker for Bach's constant `2` (core Lean only)

Everything here is core Lean (exact rational arithmetic with `Rat`), so the library can be
precompiled and run by `native_decide`. Nothing in it is trusted: `LLS/Bach2/Sound.lean` proves
that `checkChunk m w lo hi = true` implies, for every `lo ≤ q < hi`, either that the units of
residue `≤ x` generate `(ZMod q)ˣ` for some `x ≤ 2 log² q` (ankeny-grh's search
`Ankeny.Checker.checkGen`), or that the GRH budget of `LLS/Bach2/Budget.lean` is positive at
some `64 ≤ x ≤ 2 log² q`.

For each block `[a, b)` of moduli the checker computes rational bounds `La ≤ log a`,
`Lb ≥ log b`, `x = ⌊2 La²⌋`, bounds for `√x`, `log x` and `log p` (by comparing powers of `2`
with `n^m`), and a lower bound `Pc` for the Cesàro sum `Σ_{n ≤ x} Λ(n)/n (1 − n/x)` (summed
exactly with the lower bounds for `log p`). If the budget uniform in `q` is positive the block
is done; otherwise each `q` is tried with its own prime factors, and failing that by the search.
-/

namespace LLS.Check

/-- `log 2 > 0.6931471803`. -/
def lg2lo : Rat := 6931471803 / 10000000000
/-- `log 2 < 0.6931471808`. -/
def lg2hi : Rat := 6931471808 / 10000000000

/-- `⌊log₂ (n^m)⌋/m · 0.6931471803 ≤ log n`. -/
def logLo (n m : Nat) : Rat := ((Nat.log2 (n ^ m) : Nat) : Rat) / (m : Rat) * lg2lo
/-- `log n ≤ (⌊log₂ (n^m)⌋ + 1)/m · 0.6931471808`. -/
def logHi (n m : Nat) : Rat := ((Nat.log2 (n ^ m) + 1 : Nat) : Rat) / (m : Rat) * lg2hi

/-- Primality by trial division. -/
def isPrimeB (p : Nat) : Bool := 2 ≤ p && (List.range' 2 (p - 2)).all fun d => p % d != 0

/-- Size of the prime table. -/
def NP : Nat := 2000
/-- Precision of the logarithms of the tabulated primes. -/
def MP : Nat := 1024

/-- A prime with bounds for its logarithm. -/
structure PE where
  p : Nat
  lo : Rat
  hi : Rat

/-- The primes below `NP`. -/
def primesL : List Nat := (List.range NP).filter isPrimeB

/-- The table entry of `p`: `lo ≤ log p ≤ hi`. -/
def mkPE (p : Nat) : PE := ⟨p, logLo p MP, logHi p MP⟩

/-- The primes below `NP`, with bounds for their logarithms. -/
def tab : List PE := primesL.map mkPE

/-- Is `n` a positive power of `p`? -/
def isPowOf (p : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, n => n == p || (n % p == 0 && p < n && isPowOf p fuel (n / p))

/-- A lower bound for `Λ(n)`. -/
def lamLo (n : Nat) : Rat :=
  match tab.find? (fun e => n % e.p == 0) with
  | some e => if isPowOf e.p n n then e.lo else 0
  | none => 0

/-- A lower bound for `Σ_{n ≤ x} Λ(n) (1/n)(1 − n/x)`. -/
def cesLo (x : Nat) : Rat :=
  ((List.range (x + 1)).map fun n => lamLo n * (1 / (n : Rat) * (1 - (n : Rat) / (x : Rat)))).sum

/-! ### The budget in rational arithmetic (the formulas of `LLS.Numerics.Interval`) -/

section
variable (x s1 s2 l1 l2 : Rat)

def K1 : Rat := (s1 + 1 + l1 / 2) / (1 + 1 / x - 2 / s2)
def K2 : Rat := (s2 + 1 + l2 / 2) / (1 + 1 / x - 2 / s1)
def k1 : Rat := K1 x s1 s2 l1 * (1 - 1 / x) + l1 / 2
def k2 : Rat := K2 x s1 s2 l2 * (1 - 1 / x) + l2 / 2
def Es : Rat := -(1 / 2) * (1 - 1 / x) * (11364 / 10000) - 57688 / 100000 / 2 * (1 - 1 / x)
  + (l2 + 2) / x

/-- Lower bound for `base2 x Pc`. -/
def baseLo (Pc : Rat) : Rat :=
  x - 3 / 20 * s2 - 3 * l2 - 3 + 2 * K1 x s1 s2 l1 * Pc - 2 * K1 x s1 s2 l1 * Es x l2
    + 1 / 2 * (11364 / 10000) * l1 - ((31416 / 10000) ^ 2 / 6 - 57688 / 100000 / 2 * l1)

/-- Upper bound for `A_p(x)`. -/
def Aup (lo hi p : Rat) : Rat := (l2 - lo / 2) ^ 2 / 2 + 2 * K2 x s1 s2 l2 * (hi / (p - 1))

/-- `max 0 t`. -/
def pos (t : Rat) : Rat := if 0 ≤ t then t else 0

/-- Upper bound for `W_p(x)`. -/
def Wup (lo hi p : Rat) : Rat :=
  Aup x s1 s2 l2 lo hi p + pos (Aup x s1 s2 l2 lo hi p - k1 x s1 s2 l1 * lo)

end

/-- Bounds for `β(x, P₀)`; `lP ≤ log P₀ ≤ hP`. -/
def betLo (x s1 s2 l1 hP P0 : Rat) : Rat := l1 ^ 2 / (2 * hP) + 2 * K1 x s1 s2 l1 / (P0 - 1)
def betHi (x s1 s2 l2 lP P0 : Rat) : Rat := l2 ^ 2 / (2 * lP) + 2 * K2 x s1 s2 l2 / (P0 - 1)

/-- The cut-off `P₀ = 53` of the uniform budget. -/
def P0 : Nat := 53

/-! ### One block of moduli -/

/-- The data of a block `[a, b)`. -/
structure BD where
  x : Nat
  s1 : Rat
  s2 : Rat
  l1 : Rat
  l2 : Rat
  La : Rat
  Lb : Rat
  Pc : Rat

/-- Scale for the integer form of the per-modulus budget. -/
def SC : Nat := 2 ^ 32

def mkBD (m a b : Nat) : BD :=
  let La := logLo a m
  let x := (2 * La * La).floor.toNat
  let r := Nat.sqrt (x * 4 ^ 20)
  let l1 := logLo x MP
  { x, s1 := (r : Rat) / (2 ^ 20 : Nat), s2 := ((r + 1 : Nat) : Rat) / (2 ^ 20 : Nat), l1,
    l2 := logHi x MP, La, Lb := logHi b m, Pc := if x < NP then cesLo x else l1 - 2 }

/-- Side conditions for the interval bounds. -/
def sideOK (d : BD) : Bool :=
  decide (64 ≤ d.x) && decide (0 < d.s1) && decide (d.s1 * d.s1 ≤ (d.x : Rat)) &&
  decide ((d.x : Rat) ≤ d.s2 * d.s2) && decide (0 < 1 + 1 / (d.x : Rat) - 2 / d.s1) &&
  decide (0 ≤ d.l1) && decide (0 ≤ d.Pc) && decide (0 ≤ d.Lb) && decide (Es d.x d.l2 ≤ 0)

/-- The lower bound for `base2 x Pc − κ(x) log q`. -/
def Bq (d : BD) : Rat := baseLo d.x d.s1 d.s2 d.l1 d.l2 d.Pc - k2 d.x d.s1 d.s2 d.l2 * d.Lb

def wOf (d : BD) (e : PE) : Rat := Wup d.x d.s1 d.s2 d.l1 d.l2 e.lo e.hi (e.p : Rat)

/-- The prime is usable: `0 ≤ lo`, `hi/2 ≤ l₁`. -/
def peOK (d : BD) (e : PE) : Bool := decide (0 ≤ e.lo) && decide (e.hi / 2 ≤ d.l1)

/-- The uniform budget is positive on the whole block. -/
def unifOK (d : BD) : Bool :=
  let lP := logLo P0 MP
  let hP := logHi P0 MP
  let bl := betLo d.x d.s1 d.s2 d.l1 hP (P0 : Rat)
  let bh := betHi d.x d.s1 d.s2 d.l2 lP (P0 : Rat)
  let small := primesL.filter (· < P0)
  decide (0 < lP) && decide (bh ≤ k1 d.x d.s1 d.s2 d.l1) && small.all (fun p => peOK d (mkPE p)) &&
  decide (0 < Bq d - bh * d.Lb
    - (small.map fun p => pos (wOf d (mkPE p) - bl * (mkPE p).lo)).sum)

/-- The cost of `p`, scaled to an integer. -/
def Wn (d : BD) (p : Nat) : Nat := ((wOf d (mkPE p)) * (SC : Rat)).ceil.toNat

/-- The per-prime costs `(p, W_p)` for the primes `p ≤ x`. -/
def wList (d : BD) : List (Nat × Nat) := (primesL.filter (· ≤ d.x)).map fun p => (p, Wn d p)

def wListOK (d : BD) : Bool :=
  (primesL.filter (· ≤ d.x)).all fun p =>
    peOK d (mkPE p) && decide (wOf d (mkPE p) ≤ (Wn d p : Rat) / (SC : Rat))

/-- `acc + Σ_{(p, w) ∈ l, p ∣ q} w`. -/
def sumDiv (q : Nat) : List (Nat × Nat) → Nat → Nat
  | [], acc => acc
  | pw :: l, acc => sumDiv q l (if q % pw.1 == 0 then acc + pw.2 else acc)

/-- `f q` for every `a ≤ q < a + n`. -/
def allQ (f : Nat → Bool) : Nat → Nat → Bool
  | _, 0 => true
  | a, n + 1 => f a && allQ f (a + 1) n

def blockOK (m a b : Nat) : Bool :=
  let d := mkBD m a b
  decide (0 ≤ d.La) && decide ((d.x : Rat) ≤ 2 * d.La * d.La) &&
  (if d.x < 64 then allQ (fun q => Ankeny.Checker.checkGen q d.x) a (b - a)
   else sideOK d && (unifOK d ||
     (decide (d.x < NP) && wListOK d &&
       let Bn := (Bq d * (SC : Rat)).floor.toNat
       decide ((Bn : Rat) / (SC : Rat) ≤ Bq d) &&
       let wl := wList d
       allQ (fun q => decide (sumDiv q wl 0 < Bn) || Ankeny.Checker.checkGen q d.x) a (b - a))))

/-- Blocks `[a, a + max 1 ⌊a/2^w⌋)` up to `hi`. -/
def go (m w hi : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, a =>
    if hi ≤ a then true
    else
      let b := min hi (a + max 1 (a >>> w))
      blockOK m a b && go m w hi fuel b

/-- The check for `lo ≤ q < hi` (`3 ≤ lo`), log precision `m`, relative block width `2^-w`. -/
def checkChunk (m w lo hi : Nat) : Bool := decide (3 ≤ lo) && decide (1 ≤ m) && go m w hi (hi - lo) lo

end LLS.Check
