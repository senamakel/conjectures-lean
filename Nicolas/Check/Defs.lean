import Robin.Lagarias.Bounds

/-!
# The finite check: computable part

For `n = 1, 2, …, B` the state carries `R ≤ ∏_{p≤n} p/(p−1)`, `T ≥ θ(n)` and a flag. At each prime
`n ≥ 3` the flag records `EU · logUp T < R`, where `EU ≥ e^γ` and `logUp T ≥ log T ≥ log θ(n)`.
All arithmetic is in `ℚ`; `R` is rounded down and `logUp` up to multiples of `2^{-64}` so that
denominators stay bounded. Soundness is proved in `Nicolas/Check/Sound.lean`.
-/

namespace Nicolas.Check

open Finset

/-- Working precision (bits). -/
def prec : ℕ := 64

/-- Round down to a multiple of `2^{-prec}`. -/
def rdDown (q : ℚ) : ℚ := (⌊q * 2 ^ prec⌋ : ℚ) / 2 ^ prec

/-- Round up to a multiple of `2^{-prec}`. -/
def rdUp (q : ℚ) : ℚ := (⌈q * 2 ^ prec⌉ : ℚ) / 2 ^ prec

/-- Number of terms of the series `log r = Σ_{i≥1} y^i / i`, `y = 1 − 1/r`. -/
def nTerms : ℕ := 40

/-- `Σ_{i<K} y^{i+1}/(i+1)`. -/
def logSeries (y : ℚ) : ℚ := ∑ i ∈ range nTerms, y ^ (i + 1) / (i + 1)

/-- Upper bound for `log r`, `1 ≤ r ≤ 2`: series plus the tail `y^{K+1}/(1 − y)`. -/
def logUpR (r : ℚ) : ℚ :=
  let y := 1 - 1 / r
  logSeries y + y ^ (nTerms + 1) / (1 - y)

/-- Rational upper bound for `log 2` (`Real.log_two_lt_d9`). -/
def l2U : ℚ := 6931471808 / 10 ^ 10

/-- Upper bound for `log q`, `q ≥ 1`: write `q = 2^e r` with `e = ⌊log₂ ⌊q⌋⌋`, `1 ≤ r < 2`. -/
def logUp (q : ℚ) : ℚ :=
  let e := Nat.log 2 ⌊q⌋₊
  rdUp (e * l2U + logUpR (q / 2 ^ e))

/-- Upper bound for `e^γ`: `γ < 0.5774` (erdos-985) and robin-rh's `expUpper`. -/
def EU : ℚ := Robin.Lagarias.expUpper (5774 / 10000)

/-- Primality test used by the checker (`Nat.prime_def_minFac`). -/
def isPrime (n : ℕ) : Bool := 2 ≤ n && n.minFac == n

/-- The state after processing `1, …, n`. -/
structure St where
  R : ℚ
  T : ℚ
  ok : Bool

/-- Process `n`. -/
def step (st : St) (n : ℕ) : St :=
  if isPrime n then
    let R' := rdDown (st.R * n / (n - 1))
    let T' := st.T + logUp n
    ⟨R', T', st.ok && (decide (n < 3) || decide (EU * logUp T' < R'))⟩
  else st

def init : St := ⟨1, 0, true⟩

/-- `run m` processes `1, …, m`. -/
def run : ℕ → St
  | 0 => init
  | m + 1 => step (run m) (m + 1)

/-- Tail-recursive form: `loop k n st` processes `n, …, n + k − 1`. -/
def loop : ℕ → ℕ → St → St
  | 0, _, st => st
  | k + 1, n, st => loop k (n + 1) (step st n)

lemma loop_run (k m : ℕ) : loop k (m + 1) (run m) = run (m + k) := by
  induction k generalizing m with
  | zero => rfl
  | succ k ih =>
    simp only [loop]
    have : step (run m) (m + 1) = run (m + 1) := rfl
    rw [this, ih (m + 1)]
    congr 1; omega

/-- The bound of the finite range. -/
def bound : ℕ := 100000

end Nicolas.Check
