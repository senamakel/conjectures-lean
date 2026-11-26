/-!
# The band computation: executable part

Lean core only, compiled with `precompileModules`. Nothing here is trusted:
`Speiser/Band/Sound.lean` proves what a `true` answer means.

Fixed point: an integer `a` stands for `a / D`, `D = 2^64`. A `Disc` `⟨re, im, rad⟩` stands for
the closed disc of radius `rad / D` about `(re + i·im) / D`. Products are rounded down
(`Int` division by a positive number rounds towards `-∞`); every rounding error is added to the
radius, which is always rounded up.
-/

namespace SpeiserCompute

def D : Int := 2 ^ 64

/-- `⌊a b / D⌋`. -/
def fmul (a b : Int) : Int := a * b / D

/-- `⌈a / b⌉` for `b > 0`. -/
def cdiv (a b : Int) : Int := (a + b - 1) / b

/-- `⌈a b / D⌉`. -/
def fmulUp (a b : Int) : Int := cdiv (a * b) D

def iabs (a : Int) : Int := if a < 0 then -a else a

structure Disc where
  re : Int
  im : Int
  rad : Int

namespace Disc

def l1 (a : Disc) : Int := iabs a.re + iabs a.im

def add (a b : Disc) : Disc := ⟨a.re + b.re, a.im + b.im, a.rad + b.rad⟩

def neg (a : Disc) : Disc := ⟨-a.re, -a.im, a.rad⟩

def sub (a b : Disc) : Disc := add a (neg b)

def mul (a b : Disc) : Disc :=
  ⟨fmul a.re b.re - fmul a.im b.im, fmul a.re b.im + fmul a.im b.re,
    fmulUp a.l1 b.rad + fmulUp b.l1 a.rad + fmulUp a.rad b.rad + 4⟩

/-- Multiplication by an integer. -/
def smulInt (k : Int) (a : Disc) : Disc := ⟨k * a.re, k * a.im, iabs k * a.rad⟩

/-- Division by a positive integer. -/
def divInt (k : Int) (a : Disc) : Disc := ⟨a.re / k, a.im / k, cdiv a.rad k + 2⟩

/-- `1/(x + iy)` for a point (scaled `x`, `y`, not both 0). -/
def invPt (x y : Int) : Disc :=
  ⟨D * D * x / (x * x + y * y), D * D * (-y) / (x * x + y * y), 2⟩

def pt (x y : Int) : Disc := ⟨x, y, 0⟩

end Disc

/-- `(term, sum)`: `term ∋ w^n/n!`, `sum ∋ Σ_{i<n} w^i/i!` for the point `w ∈ a`. -/
def taylorStep (w : Disc) : Nat → Disc × Disc
  | 0 => (Disc.pt D 0, Disc.pt 0 0)
  | n + 1 =>
    let p := taylorStep w n
    (Disc.divInt (n + 1 : Nat) (p.1.mul w), p.2.add p.1)

def nT : Nat := 16

/-- The factorial (core has none). -/
def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

/-- Scaled upper bound for Mathlib's `Complex.exp_bound` remainder `l^n (n+1)/(n! n)`, `l ≤ 1`
(scaled). Since `l ≤ D`, `l^n / D^(n-1) ≤ l`, so `l · (n+1)/(n! n)` bounds it. -/
def taylorRem (l : Int) : Int := cdiv (l * (nT + 1 : Nat)) ((fact nT * nT : Nat) : Int) + 1

def nSq : Nat := 6

/-- Repeated squaring. -/
def sq (a : Disc) : Nat → Disc
  | 0 => a
  | k + 1 => let b := sq a k; b.mul b

/-- `exp` on a disc `a` with `a.rad ≤ D/2^(nSq+1)`. The centre is split as
`x = 2^nSq·wx + ex`, and `exp(z) = exp(2^nSq w)·exp(z - 2^nSq w)` with
`‖z − 2^nSq w‖ ≤ a.rad + 2·2^nSq`, and `‖exp u − 1‖ ≤ 2‖u‖` for `‖u‖ ≤ 1`. -/
def expDisc (a : Disc) : Disc :=
  let wx := a.re / (2 ^ nSq : Int)
  let wy := a.im / (2 ^ nSq : Int)
  let s := (taylorStep (Disc.pt wx wy) nT).2
  let e0 : Disc := ⟨s.re, s.im, s.rad + taylorRem (iabs wx + iabs wy)⟩
  let u := a.rad + 2 * 2 ^ nSq
  (sq e0 nSq).mul ⟨D, 0, 2 * u⟩

/-- The conditions under which `expDisc` is sound: `‖w‖ ≤ 1` and `‖z - 2^nSq w‖ ≤ 1`. -/
def expOK (a : Disc) : Bool :=
  decide (iabs (a.re / (2 ^ nSq : Int)) + iabs (a.im / (2 ^ nSq : Int)) ≤ D) &&
    decide (a.rad + 2 * 2 ^ nSq ≤ D)

/-! ### `log n` enclosures, `2 ≤ n ≤ 9` (scaled; proved in `Speiser/Band/Logs.lean`) -/

/-- Rational bounds `num/10^12`. -/
def logLoQ : Nat → Int
  | 2 => 693147180557
  | 3 => 1098612288666
  | 5 => 1609437912432
  | 7 => 1945910149053
  | _ => 0

def logHiQ : Nat → Int
  | 2 => 693147180562
  | 3 => 1098612288671
  | 5 => 1609437912437
  | 7 => 1945910149058
  | _ => 0

/-- Scaled, rounded outward. -/
def logLoP (n : Nat) : Int := logLoQ n * D / 1000000000000
def logHiP (n : Nat) : Int := cdiv (logHiQ n * D) 1000000000000

def logLo : Nat → Int
  | 4 => 2 * logLoP 2
  | 6 => logLoP 2 + logLoP 3
  | 8 => 3 * logLoP 2
  | 9 => 2 * logLoP 3
  | n => logLoP n

def logHi : Nat → Int
  | 4 => 2 * logHiP 2
  | 6 => logHiP 2 + logHiP 3
  | 8 => 3 * logHiP 2
  | 9 => 2 * logHiP 3
  | n => logHiP n

def logD (n : Nat) : Disc := ⟨(logLo n + logHi n) / 2, 0, cdiv (logHi n - logLo n) 2 + 1⟩

/-- The exponent `-c log n`. -/
def npowArg (n : Nat) (x y : Int) : Disc := (Disc.pt (-x) (-y)).mul (logD n)

/-- `n^{-c} = exp(-c log n)` at the point `c = (x + iy)/D`. -/
def npow (n : Nat) (x y : Int) : Disc := expDisc (npowArg n x y)

/-- All exponentials used at the point `(x, y)` and at the real point `sg` are sound. -/
def argsOK (x y sg : Int) : Bool :=
  (List.range 8).all fun k => expOK (npowArg (k + 2) x y) && expOK (npowArg (k + 2) sg 0)

/-- `ζ'`'s Euler–Maclaurin main part `M₁(c)`, `N = 9`, at the point `c`. -/
def M1 (x y : Int) : Disc :=
  let e9 := npow 9 x y
  let l9 := logD 9
  let iv := Disc.invPt (x - D) y
  let s8 := (List.range 7).foldl (fun acc k =>
    acc.add (((logD (k + 2)).mul (npow (k + 2) x y)).neg)) (Disc.pt 0 0)
  let le9 := l9.mul e9
  let t1 := (Disc.divInt 2 le9).neg
  let t2 := (Disc.smulInt 9 (le9.mul iv)).neg
  let t3 := (Disc.smulInt 9 (e9.mul (iv.mul iv))).neg
  let t4 := Disc.divInt 108 (e9.sub ((Disc.pt x y).mul le9))
  ((((s8.add t1).add t2).add t3).add t4)

/-- Upper bound (scaled) for `n^{-σ'}`. -/
def npowRe (n : Nat) (sg : Int) : Int := let e := npow n sg 0; e.l1 + e.rad

/-- Scaled upper bound for `‖M₂(w)‖` on `‖w - c‖ ≤ r`, from `σ' ≤ Re w`, `A ≥ ‖w‖`,
`0 < d ≤ ‖w - 1‖`. -/
def BM (sg A d : Int) : Int :=
  let e9 := npowRe 9 sg
  let h9 := logHi 9
  let s8 := (List.range 7).foldl (fun acc k =>
    acc + fmulUp (fmulUp (logHi (k + 2)) (logHi (k + 2))) (npowRe (k + 2) sg)) 0
  let h92 := fmulUp h9 h9
  let id := cdiv (D * D) d
  let id2 := fmulUp id id
  let id3 := fmulUp id2 id
  s8 + cdiv (fmulUp h92 e9) 2 +
    9 * fmulUp e9 (fmulUp h92 id + 2 * fmulUp h9 id2 + 2 * id3) +
    cdiv (fmulUp e9 (2 * h9 + fmulUp A h92)) 108

/-- The Cauchy radius `ρ = 2/5`, scaled. -/
def rho : Int := 2 * D / 5

/-- Scaled upper bound for `‖T'(s)‖`: `A'(A'+1)(A'+2)(A'+3)/(147456 ρ)`, `A' ≥ ‖s‖ + ρ`. -/
def Tb (A' : Int) : Int :=
  let p := fmulUp (fmulUp (fmulUp A' (A' + D)) (A' + 2 * D)) (A' + 3 * D)
  cdiv (p * D) (147456 * rho)

/-- The test on one box `[s0, s1] × [t0, t1]` (scaled, all multiples of `2`). -/
def cellOK (s0 s1 t0 t1 : Int) : Bool :=
  let x := (s0 + s1) / 2
  let y := (t0 + t1) / 2
  let r := cdiv (s1 - s0) 2 + cdiv (t1 - t0) 2 + 2
  let A := iabs x + iabs y + r
  let d := iabs y - r
  let side := decide (-(D / 10) ≤ x - r) && decide (x + r ≤ D) && decide (0 < d) &&
    ((decide (D < y - r - rho) && decide (y + r + rho < 10 * D)) ||
     (decide (-10 * D < y - r - rho) && decide (y + r + rho < -D)))
  let m := M1 x y
  let e := m.rad + fmulUp r (BM (x - r) A d) + Tb (A + rho)
  side && argsOK x y (x - r) && decide (0 ≤ e) && decide (e * e < m.re * m.re + m.im * m.im)

/-- Bisect until every box passes, at most `depth` levels. -/
def coverOK (s0 s1 t0 t1 : Int) : Nat → Bool
  | 0 => cellOK s0 s1 t0 t1
  | k + 1 =>
    cellOK s0 s1 t0 t1 ||
      (if t1 - t0 ≤ s1 - s0 then
        coverOK s0 ((s0 + s1) / 2) t0 t1 k && coverOK ((s0 + s1) / 2) s1 t0 t1 k
      else
        coverOK s0 s1 t0 ((t0 + t1) / 2) k && coverOK s0 s1 ((t0 + t1) / 2) t1 k)

/-- Number of accepted boxes (for sizing only). -/
def countCells (s0 s1 t0 t1 : Int) : Nat → Nat
  | 0 => if cellOK s0 s1 t0 t1 then 1 else 1000000000
  | k + 1 =>
    if cellOK s0 s1 t0 t1 then 1 else
      if t1 - t0 ≤ s1 - s0 then
        countCells s0 ((s0 + s1) / 2) t0 t1 k + countCells ((s0 + s1) / 2) s1 t0 t1 k
      else
        countCells s0 s1 t0 ((t0 + t1) / 2) k + countCells s0 s1 ((t0 + t1) / 2) t1 k

end SpeiserCompute
