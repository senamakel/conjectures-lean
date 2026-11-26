import Mathlib

/-!
# Computable rational bounds for `exp` and `log`

Rational functions `expUpper`, `expLower`, `logLo` with real-valued correctness lemmas, used to
certify the finite range of Lagarias's inequality.
-/

namespace Robin.Lagarias

open Finset

/-- Taylor partial sum `∑_{i<N} x^i / i!`. -/
def taylor (x : ℚ) (N : ℕ) : ℚ := ∑ i ∈ range N, x ^ i / (i.factorial : ℚ)

/-- Rational upper bound for `e` (`Real.exp_one_lt_d9`). -/
def eUp : ℚ := 27182818286 / 10 ^ 10

/-- Rational upper bound for `exp x` (valid for `0 ≤ x`): `e^⌊x⌋ · exp(frac x)`, the latter via
a Taylor polynomial with remainder. -/
def expUpper (x : ℚ) : ℚ :=
  eUp ^ ⌊x⌋.toNat * (taylor (x - ⌊x⌋.toNat) 20 +
    (x - ⌊x⌋.toNat) ^ 20 * (21 / ((Nat.factorial 20 : ℚ) * 20)))

/-- Rational lower bound for `exp x` (valid for `0 ≤ x`). -/
def expLower (x : ℚ) : ℚ := taylor x 20

/-- Bisection helper for `logLo`. -/
def logLoAux : ℕ → ℚ → ℚ → ℚ → ℚ
  | 0, _, lo, _ => lo
  | k + 1, y, lo, hi =>
    if expUpper ((lo + hi) / 2) ≤ y then logLoAux k y ((lo + hi) / 2) hi
    else logLoAux k y lo ((lo + hi) / 2)

/-- A rational approximation from below to `log y` (its correctness is *not* assumed: users check
`expUpper (logLo y) ≤ y` directly). -/
def logLo (y : ℚ) : ℚ := logLoAux 18 y 0 10

lemma taylor_cast (x : ℚ) (N : ℕ) :
    ((taylor x N : ℚ) : ℝ) = ∑ i ∈ range N, (x : ℝ) ^ i / (i.factorial : ℝ) := by
  simp [taylor]

lemma expLower_le_exp {x : ℚ} (hx : 0 ≤ x) : ((expLower x : ℚ) : ℝ) ≤ Real.exp x := by
  rw [expLower, taylor_cast]
  exact Real.sum_le_exp_of_nonneg (by exact_mod_cast hx) 20

lemma exp_le_expUpper {x : ℚ} (hx : 0 ≤ x) : Real.exp x ≤ ((expUpper x : ℚ) : ℝ) := by
  set m : ℕ := ⌊x⌋.toNat with hm
  have hfl : (0 : ℤ) ≤ ⌊x⌋ := Int.floor_nonneg.mpr hx
  have hmz : ((m : ℤ)) = ⌊x⌋ := Int.toNat_of_nonneg hfl
  have hmq : ((m : ℚ)) = (⌊x⌋ : ℚ) := by exact_mod_cast hmz
  set f : ℚ := x - m with hf
  have hf0 : 0 ≤ f := by rw [hf, hmq]; linarith [Int.floor_le x]
  have hf1 : f ≤ 1 := by rw [hf, hmq]; linarith [Int.lt_floor_add_one x]
  have hfR0 : (0 : ℝ) ≤ f := by exact_mod_cast hf0
  have hfR1 : (f : ℝ) ≤ 1 := by exact_mod_cast hf1
  have hxsplit : (x : ℝ) = m + f := by rw [hf]; push_cast; ring
  have hb := Real.exp_bound (x := (f : ℝ)) (by rw [abs_of_nonneg hfR0]; exact hfR1)
    (n := 20) (by norm_num)
  rw [abs_of_nonneg hfR0] at hb
  have hexpf : Real.exp f ≤ ∑ i ∈ range 20, (f : ℝ) ^ i / (i.factorial : ℝ) +
      (f : ℝ) ^ 20 * (21 / ((Nat.factorial 20 : ℝ) * 20)) := by
    have := (abs_le.mp hb).2
    push_cast at this ⊢
    linarith
  have hexpm : Real.exp (m : ℝ) ≤ (eUp : ℝ) ^ m := by
    rw [← Real.exp_one_pow]
    apply pow_le_pow_left₀ (Real.exp_pos 1).le
    have := Real.exp_one_lt_d9
    simp only [eUp]; push_cast; linarith
  have hcast : ((expUpper x : ℚ) : ℝ) = (eUp : ℝ) ^ m * (∑ i ∈ range 20,
      (f : ℝ) ^ i / (i.factorial : ℝ) + (f : ℝ) ^ 20 * (21 / ((Nat.factorial 20 : ℝ) * 20))) := by
    rw [expUpper, ← hm, ← hf]
    push_cast [taylor_cast]
    rfl
  rw [hcast, hxsplit, Real.exp_add]
  exact mul_le_mul hexpm hexpf (Real.exp_pos _).le (pow_nonneg (by simp [eUp]; norm_num) _)

/-- If `0 ≤ L` and `expUpper L ≤ y` then `L ≤ log y`. -/
lemma le_log_of_expUpper_le {L : ℚ} {y : ℝ} (hL : 0 ≤ L) (h : ((expUpper L : ℚ) : ℝ) ≤ y) :
    (L : ℝ) ≤ Real.log y := by
  have hy : 0 < y := lt_of_lt_of_le (Real.exp_pos _) ((exp_le_expUpper hL).trans h)
  rw [Real.le_log_iff_exp_le hy]
  exact (exp_le_expUpper hL).trans h

end Robin.Lagarias
