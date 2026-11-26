/-!
# The cell checks, in Lean core only

These are the computational definitions behind `Cramer.CMS.chk`: natural-number and integer
arithmetic on lists, with no Mathlib, so that the data modules can be checked by `decide`
in the kernel without loading Mathlib. `Cramer.CMS.CellsCore` proves that each agrees with
the Mathlib-side definition it replaces.
-/

namespace CramerCompute

/-- `Σ_{i < n} f i` over `List.range`. -/
def lsum (n : Nat) (f : Nat → Int) : Int := ((List.range n).map f).foldr (· + ·) 0
/-- Natural-number version. -/
def lsumN (n : Nat) (f : Nat → Nat) : Nat := ((List.range n).map f).foldr (· + ·) 0

def fact : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * fact n

def chooseC : Nat → Nat → Nat
  | _, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k + 1 => chooseC n k + chooseC n (k + 1)

def D0 : Nat := 1048576
def SS : Nat := 18446744073709551616
def PIL : Nat := 314159265358979323846
def PIH : Nat := 314159265358979323847
def TE : Nat := 100000000000000000000

def cosNum (n : Nat) (p : Int) (q : Nat) : Int :=
  lsum n fun i => (-1) ^ i * p ^ (2 * i) * ((q : Int) ^ (2 * (n - 1) - 2 * i)) *
    ((fact (2 * (n - 1)) / fact (2 * i) : Nat) : Int)

def cosDen (n : Nat) (q : Nat) : Nat := q ^ (2 * (n - 1)) * fact (2 * (n - 1))

def tNum (N k : Nat) : Int := (N : Int) * TE - 2 * k * PIH * D0

def endOK (N k : Nat) (cl cu : Int) : Bool :=
  let p := tNum N k
  let q := D0 * TE
  let n14 := cosNum 14 p q
  let d14 := cosDen 14 q
  let n13 := cosNum 13 p q
  let d13 := cosDen 13 q
  decide (cl * d14 * TE ≤ (n14 * TE - 2 * k * d14) * SS) &&
    decide ((n13 * TE + 2 * k * d13) * SS ≤ cu * d13 * TE)

structure Ent where
  N : Nat
  k : Nat
  cl : Int
  cu : Int
  j : Nat
  fl : Nat
  tg : Nat
  Gn : Nat
  en : Nat
  r : Int
  deriving Inhabited

def cLo (e e' : Ent) : Int :=
  if e.fl = 0 then min e.cl e'.cl else if e.j % 2 = 0 then min e.cl e'.cl else -(SS : Int)
def cHi (e e' : Ent) : Int :=
  if e.fl = 0 then max e.cu e'.cu else if e.j % 2 = 0 then (SS : Int) else max e.cu e'.cu

def posOK (e e' : Ent) : Bool :=
  decide (e.N ≤ e'.N) && decide (e'.N * TE ≤ (e.j + 1) * PIL * D0) &&
    (if e.fl = 0 then decide (e.j * PIH * D0 ≤ e.N * TE)
      else decide (1 ≤ e.j) && decide ((e.j - 1) * PIH * D0 ≤ e.N * TE))

def Qp (qs : List Int) (A : Int) (T : Nat) (i : Nat) : Int :=
  lsum qs.length fun j => if i ≤ j then qs.getD j 0 * (chooseC j i : Int) * A ^ (j - i) *
    ((T : Int) ^ (qs.length - 1 - j)) else 0

def Ub (qs : List Int) (A : Int) (T R : Nat) : Nat :=
  lsumN qs.length fun i => (Qp qs A T i).natAbs * R ^ i

def boundOK (qs : List Int) (GD : Nat) (e e' : Ent) : Bool :=
  let lo := cLo e e'
  let hi := cHi e e'
  let U := Ub qs (lo + hi) (2 * SS) (hi - lo).toNat
  let K := qs.length - 1
  decide (lo ≤ hi) &&
  (if e.tg = 0 then
    decide (e'.N ^ 2 ≤ 15 * D0 ^ 2) &&
      decide ((360 * D0 ^ 4 + e.N ^ 4 - 30 * e.N ^ 2 * D0 ^ 2) * U * GD ≤
        e.Gn * 360 * D0 ^ 4 * (2 * SS) ^ K) &&
      decide (30 * e.N ^ 2 * D0 ^ 2 ≤ 360 * D0 ^ 4 + e.N ^ 4)
  else
    decide (0 < e.N) &&
      decide ((2 * (SS : Int) - 2 * lo) * U * GD * D0 ^ 2 ≤ e.Gn * e.N ^ 2 * SS * (2 * SS) ^ K))

def chk (qs : List Int) (GD : Nat) : List Ent → Bool
  | [] => true
  | [e] => endOK e.N e.k e.cl e.cu
  | e :: e' :: rest => endOK e.N e.k e.cl e.cu && posOK e e' && boundOK qs GD e e' &&
      chk qs GD (e' :: rest)

/-- The error check on a cell: `e(θ) ≤ en/D₀` on `[θ_a, θ_b]` (`e₁` if `θ_b ≤ 1`, else `e₂`). -/
def eOK (c1a c1b c2a c2b : Nat) (e e' : Ent) : Bool :=
  if e'.N ≤ D0 then decide (c1a * D0 + 2 * e'.N * c1b ≤ e.en)
  else decide (0 < e.N) && decide ((2 * c2a * D0 ^ 2 + 2 * e.N * c2b * D0) * D0 ≤ e.en * e.N ^ 2)

/-- The log check: `log θ_b ≤ (r/4) log 2`. -/
def rOK (e e' : Ent) : Bool :=
  decide (0 < e'.N) &&
  (if 0 ≤ e.r then decide (e'.N ^ 4 ≤ D0 ^ 4 * 2 ^ e.r.toNat)
    else decide (e'.N ^ 4 * 2 ^ (-e.r).toNat ≤ D0 ^ 4))

/-- A Boolean check on consecutive pairs. -/
def chainB (P : Ent → Ent → Bool) : List Ent → Bool
  | [] => true
  | [_] => true
  | a :: b :: l => P a b && chainB P (b :: l)

/-- A sum over consecutive pairs. -/
def pairSum (f : Ent → Ent → Nat) : List Ent → Nat
  | [] => 0
  | [_] => 0
  | a :: b :: l => f a b + pairSum f (b :: l)

/-- The summands of the certified constants. -/
def fA1G (e e' : Ent) : Nat := e.Gn * (e'.N - e.N)
def fA1e (e e' : Ent) : Nat := e.en * (e'.N - e.N)
def fA2Gp (e e' : Ent) : Nat := if 0 ≤ e.r then e.Gn * (e'.N - e.N) * e.r.toNat else 0
def fA2Gn (e e' : Ent) : Nat := if 0 ≤ e.r then 0 else e.Gn * (e'.N - e.N) * (-e.r).toNat
def fA2ep (e e' : Ent) : Nat := if 0 ≤ e.r then e.en * (e'.N - e.N) * e.r.toNat else 0
def fA2en (e e' : Ent) : Nat := if 0 ≤ e.r then 0 else e.en * (e'.N - e.N) * (-e.r).toNat
def fTVG (e e' : Ent) : Nat := ((e'.Gn : Int) - e.Gn).natAbs
def fTVe (e e' : Ent) : Nat := ((e'.en : Int) - e.en).natAbs

/-- The partial sums of one window. -/
structure WSums where
  a1G : Nat
  a1e : Nat
  a2Gp : Nat
  a2Gn : Nat
  a2ep : Nat
  a2en : Nat
  tvG : Nat
  tve : Nat

/-- The whole check of one window. -/
def winOK (qs : List Int) (GD c1a c1b c2a c2b : Nat) (w : List Ent) (v : WSums) : Bool :=
  chk qs GD w && chainB (eOK c1a c1b c2a c2b) w && chainB rOK w &&
    decide (pairSum fA1G w = v.a1G) && decide (pairSum fA1e w = v.a1e) &&
    decide (pairSum fA2Gp w = v.a2Gp) && decide (pairSum fA2Gn w = v.a2Gn) &&
    decide (pairSum fA2ep w = v.a2ep) && decide (pairSum fA2en w = v.a2en) &&
    decide (pairSum fTVG w = v.tvG) && decide (pairSum fTVe w = v.tve)

end CramerCompute
