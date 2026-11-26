import Erdos985.Bach
import Erdos985.Numerics

/-!
# An executable criterion for Bach's inequality at `x = ⌊√p⌋ - 2`

MTT, Algorithm 1, line 10: "choose `p` large enough so that, with `x = √p - 2`,
`2 c(p,x) (2 + (s-1)/δ) 2^{n-s} log p < x`". We replace this by a rational, executable test
`crit K Y0` and prove (`crit_sound`) that it implies, for every `p ≥ (Y0² + 2)²` and
`x = Nat.sqrt p - 2`,

`K · (c(p, x) √x log p) < x/2 - (√x/20 + 3)`,

which is exactly what contradicts the sieve inequality together with Bach's principal bound.

Write `y = √x ≥ Y0`. Then `p < (x + 3)²`, so `log p ≤ 4 log y + 6/Y0²`, and the tangent line
`log y ≤ log a + y/a - 1` (any `a > 0`) makes the left side, divided by `y`, at most `α + β y`
with explicit rational `α, β` (using `log 2 < 0.6931471808` and the alternating series for
`log(1 + u)` with its remainder). The right side divided by `y` is at least
`y/2 - 1/20 - 3/Y0`. So `β ≤ 1/2` and the inequality at `y = Y0` suffice.
-/

namespace Grosswald.Crit

open Real Erdos985

/-- A rational upper bound for `log 2` (`Real.log_two_lt_d9`). -/
def log2Up : ℚ := 6931471808 / 10 ^ 10

/-- A rational upper bound for `log (1 + u)`, `0 ≤ u < 1`: `N` terms of the alternating series
plus the remainder bound of `Real.abs_log_sub_add_sum_range_le`. -/
def log1pUp (u : ℚ) (N : ℕ) : ℚ :=
  -(∑ i ∈ Finset.range N, (-u) ^ (i + 1) / (i + 1)) + u ^ (N + 1) / (1 - u)

lemma log_one_add_le (u : ℚ) (N : ℕ) (hu0 : 0 ≤ u) (hu1 : u < 1) :
    Real.log (1 + u) ≤ (log1pUp u N : ℝ) := by
  have hu0' : (0 : ℝ) ≤ u := by exact_mod_cast hu0
  have hu1' : (u : ℝ) < 1 := by exact_mod_cast hu1
  have habs : |(-(u : ℝ))| < 1 := by rw [abs_neg, abs_of_nonneg hu0']; exact hu1'
  have h := Real.abs_log_sub_add_sum_range_le habs N
  rw [abs_neg, abs_of_nonneg hu0', sub_neg_eq_add] at h
  have h2 := (abs_le.mp h).2
  unfold log1pUp
  push_cast
  linarith

/-- The real-variable core: a bound for `c(p,x) √x log p` with `y = √x`. -/
lemma bracket_le (p x : ℕ) (Y0 y T : ℝ) (hY0 : 1 ≤ Y0) (hy : Y0 ≤ y) (hx : (x : ℝ) = y ^ 2)
    (hp1 : 1 < p) (hpx : (p : ℝ) < ((x : ℝ) + 3) ^ 2) (hT : Real.log y ≤ T) :
    bachC p x * √(x : ℝ) * Real.log p
      ≤ y * ((2 / 3) * (1 + 2 / Y0 + 3 / Y0 ^ 3) * (4 * T + 6 / Y0 ^ 2 + 5 / 3)
        + (2 * T + 2) / y) := by
  have hy0 : 0 < y := by linarith
  have hsx : √(x : ℝ) = y := by rw [hx, Real.sqrt_sq hy0.le]
  have hx32 : (x : ℝ) ^ (3 / 2 : ℝ) = y ^ 3 := by
    rw [hx, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add (by positivity),
      Real.rpow_one, ← Real.sqrt_eq_rpow, Real.sqrt_sq hy0.le]
    ring
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp1
  have hlogp : 0 < Real.log p := Real.log_pos hpR
  have hlogx : Real.log x = 2 * Real.log y := by rw [hx, Real.log_pow]; norm_num
  -- `log p ≤ 4 log y + 6 / Y0²`
  have hlp : Real.log p ≤ 4 * Real.log y + 6 / Y0 ^ 2 := by
    have h1 : Real.log p ≤ 2 * Real.log ((x : ℝ) + 3) := by
      rw [← Real.log_rpow (by positivity)]
      apply Real.log_le_log (by linarith)
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact hpx.le
    have h2 : (x : ℝ) + 3 = y ^ 2 * (1 + 3 / y ^ 2) := by
      rw [hx]; field_simp
    have h3 : Real.log (1 + 3 / y ^ 2) ≤ 3 / y ^ 2 := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + 3 / y ^ 2 by positivity)
      linarith
    have h4 : 6 / y ^ 2 ≤ 6 / Y0 ^ 2 := by
      gcongr
    have h5 : 2 * (3 / y ^ 2) = 6 / y ^ 2 := by ring
    rw [h2, Real.log_mul (by positivity) (by positivity), Real.log_pow] at h1
    push_cast at h1
    linarith
  have hG0 : 0 ≤ 1 + 2 / y + 3 / y ^ 3 := by positivity
  have hG : 1 + 2 / y + 3 / y ^ 3 ≤ 1 + 2 / Y0 + 3 / Y0 ^ 3 := by
    have : 2 / y ≤ 2 / Y0 := by gcongr
    have : 3 / y ^ 3 ≤ 3 / Y0 ^ 3 := by gcongr
    linarith
  have hL0 : 0 ≤ Real.log p + 5 / 3 := by linarith
  have hL : Real.log p + 5 / 3 ≤ 4 * T + 6 / Y0 ^ 2 + 5 / 3 := by linarith
  have hexp : bachC p x * √(x : ℝ) * Real.log p
      = y * ((2 / 3) * (1 + 2 / y + 3 / y ^ 3) * (Real.log p + 5 / 3)) + (2 * Real.log y + 2) := by
    unfold bachC
    rw [hsx, hx32, hlogx]
    field_simp
  have e : y * ((2 / 3) * (1 + 2 / Y0 + 3 / Y0 ^ 3) * (4 * T + 6 / Y0 ^ 2 + 5 / 3)
      + (2 * T + 2) / y) = y * ((2 / 3) * (1 + 2 / Y0 + 3 / Y0 ^ 3) * (4 * T + 6 / Y0 ^ 2 + 5 / 3))
      + (2 * T + 2) := by field_simp
  rw [hexp, e]
  have : (1 + 2 / y + 3 / y ^ 3) * (Real.log p + 5 / 3)
      ≤ (1 + 2 / Y0 + 3 / Y0 ^ 3) * (4 * T + 6 / Y0 ^ 2 + 5 / 3) :=
    mul_le_mul hG hL hL0 (hG0.trans hG)
  nlinarith

/-- The real form of the criterion. -/
lemma core (K Y0 a La : ℝ) (hK : 0 ≤ K) (hY0 : 1 ≤ Y0) (ha : 0 < a) (hLa0 : 0 ≤ La)
    (hLa : Real.log a ≤ La)
    (hβ : 8 * K * (1 + 2 / Y0 + 3 / Y0 ^ 3) / (3 * a) ≤ 1 / 2)
    (hα : K * ((2 / 3) * (1 + 2 / Y0 + 3 / Y0 ^ 3) * (4 * La - 4 + 6 / Y0 ^ 2 + 5 / 3)
        + 2 * La / Y0 + 2 / a) + 8 * K * (1 + 2 / Y0 + 3 / Y0 ^ 3) / (3 * a) * Y0
        < Y0 / 2 - 1 / 20 - 3 / Y0)
    (p x : ℕ) (y : ℝ) (hy : Y0 ≤ y) (hx : (x : ℝ) = y ^ 2) (hp1 : 1 < p)
    (hpx : (p : ℝ) < ((x : ℝ) + 3) ^ 2) :
    K * (bachC p x * √(x : ℝ) * Real.log p) < x / 2 - (√(x : ℝ) / 20 + 3) := by
  set g := 1 + 2 / Y0 + 3 / Y0 ^ 3 with hg
  have hy0 : 0 < y := by linarith
  have hT : Real.log y ≤ La + y / a - 1 := by
    have := log_le_tangent y a hy0 ha
    linarith
  have hb := bracket_le p x Y0 y (La + y / a - 1) hY0 hy hx hp1 hpx hT
  rw [← hg] at hb
  have hsx : √(x : ℝ) = y := by rw [hx, Real.sqrt_sq hy0.le]
  rw [hsx, show (x : ℝ) / 2 = y ^ 2 / 2 by rw [hx]]
  -- the bracket is at most `(α + β y)/K`
  have hbr : (2 / 3) * g * (4 * (La + y / a - 1) + 6 / Y0 ^ 2 + 5 / 3)
      + (2 * (La + y / a - 1) + 2) / y
      ≤ ((2 / 3) * g * (4 * La - 4 + 6 / Y0 ^ 2 + 5 / 3) + 2 * La / Y0 + 2 / a)
        + 8 * g / (3 * a) * y := by
    have e : (2 * (La + y / a - 1) + 2) / y = 2 * La / y + 2 / a := by field_simp; ring
    have h1 : 2 * La / y ≤ 2 * La / Y0 := by
      apply div_le_div_of_nonneg_left (by linarith) (by linarith) hy
    rw [e]
    have e2 : (2 / 3) * g * (4 * (La + y / a - 1) + 6 / Y0 ^ 2 + 5 / 3)
        = (2 / 3) * g * (4 * La - 4 + 6 / Y0 ^ 2 + 5 / 3) + 8 * g / (3 * a) * y := by
      field_simp; ring
    rw [e2]
    linarith
  have hlin : K * (((2 / 3) * g * (4 * La - 4 + 6 / Y0 ^ 2 + 5 / 3) + 2 * La / Y0 + 2 / a)
        + 8 * g / (3 * a) * y) < y / 2 - 1 / 20 - 3 / y := by
    have h3 : 3 / y ≤ 3 / Y0 := by gcongr
    have e : K * (8 * g / (3 * a) * y) = 8 * K * g / (3 * a) * y := by ring
    have : 8 * K * g / (3 * a) * y ≤ 8 * K * g / (3 * a) * Y0 + (y - Y0) / 2 := by
      nlinarith
    rw [mul_add, e]
    linarith
  have hKb : K * (bachC p x * y * Real.log p) ≤ y * (K * (((2 / 3) * g * (4 * La - 4
      + 6 / Y0 ^ 2 + 5 / 3) + 2 * La / Y0 + 2 / a) + 8 * g / (3 * a) * y)) := by
    rw [hsx] at hb
    have := mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hbr hy0.le)) hK
    linarith
  have : y * (K * (((2 / 3) * g * (4 * La - 4 + 6 / Y0 ^ 2 + 5 / 3) + 2 * La / Y0 + 2 / a)
      + 8 * g / (3 * a) * y)) < y * (y / 2 - 1 / 20 - 3 / y) :=
    mul_lt_mul_of_pos_left hlin hy0
  have e : y * (y / 2 - 1 / 20 - 3 / y) = y ^ 2 / 2 - (y / 20 + 3) := by field_simp; ring
  linarith

/-! ### The executable test -/

/-- Number of series terms for `log (1 + u)`. -/
def nTerms : ℕ := 20

/-- Heuristic choice of the tangent point `a = 2^m (1 + u)` with `u ∈ [0, 1/2]` near `Y0`.
Soundness does not depend on it. -/
def tangentParams (Y0 : ℕ) : ℕ × ℚ :=
  let m := Nat.log 2 Y0
  let r : ℚ := (Y0 : ℚ) / 2 ^ m
  if r ≤ 3 / 2 then (m, ((⌊64 * (r - 1)⌋.toNat : ℕ) : ℚ) / 64) else (m + 1, 0)

/-- The criterion for given tangent parameters. -/
def critCore (K : ℚ) (Y0 : ℕ) (m : ℕ) (u : ℚ) : Bool :=
  let Y : ℚ := Y0
  let a : ℚ := 2 ^ m * (1 + u)
  let La : ℚ := m * log2Up + log1pUp u nTerms
  let g : ℚ := 1 + 2 / Y + 3 / Y ^ 3
  let β : ℚ := 8 * K * g / (3 * a)
  let α : ℚ := K * ((2 / 3) * g * (4 * La - 4 + 6 / Y ^ 2 + 5 / 3) + 2 * La / Y + 2 / a)
  decide (0 ≤ K) && decide (1 ≤ Y0) && decide (0 ≤ u) && decide (u ≤ 1 / 2) &&
    decide (β ≤ 1 / 2) && decide (α + β * Y < Y / 2 - 1 / 20 - 3 / Y)

/-- The criterion. -/
def crit (K : ℚ) (Y0 : ℕ) : Bool :=
  critCore K Y0 (tangentParams Y0).1 (tangentParams Y0).2

lemma critCore_sound {K : ℚ} {Y0 m : ℕ} {u : ℚ} (h : critCore K Y0 m u = true)
    (p : ℕ) (hp : (Y0 ^ 2 + 2) ^ 2 ≤ p) :
    (K : ℝ) * (bachC p (Nat.sqrt p - 2 : ℕ) * √((Nat.sqrt p - 2 : ℕ) : ℝ) * Real.log p)
      < ((Nat.sqrt p - 2 : ℕ) : ℝ) / 2 - (√((Nat.sqrt p - 2 : ℕ) : ℝ) / 20 + 3) := by
  simp only [critCore, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hK, hY0⟩, hu0⟩, hu1⟩, hβ⟩, hα⟩ := h
  set x := Nat.sqrt p - 2 with hxdef
  have hsq : Y0 ^ 2 + 2 ≤ Nat.sqrt p := Nat.le_sqrt'.mpr hp
  have hxY : Y0 ^ 2 ≤ x := by omega
  have hY0R : (1 : ℝ) ≤ Y0 := by exact_mod_cast hY0
  have hxR : ((Y0 : ℝ)) ^ 2 ≤ x := by exact_mod_cast hxY
  set y := √(x : ℝ) with hy
  have hYy : (Y0 : ℝ) ≤ y := Real.le_sqrt_of_sq_le hxR
  have hxy : (x : ℝ) = y ^ 2 := by rw [hy, Real.sq_sqrt (by positivity)]
  have hp1 : 1 < p := by nlinarith
  have hpx : (p : ℝ) < ((x : ℝ) + 3) ^ 2 := by
    have h1 := Nat.lt_succ_sqrt' p
    have h2 : Nat.succ (Nat.sqrt p) = x + 3 := by omega
    rw [h2] at h1
    exact_mod_cast h1
  -- tangent point
  have hu0R : (0 : ℝ) ≤ u := by exact_mod_cast hu0
  have hu1R : (u : ℝ) ≤ 1 / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hu1; simpa using this
  have ha : (0 : ℝ) < 2 ^ m * (1 + u) := by positivity
  have hlog1p := log_one_add_le u nTerms hu0 (by linarith [show u ≤ 1 / 2 from hu1])
  have hLa : Real.log (2 ^ m * (1 + u)) ≤ ((m * log2Up + log1pUp u nTerms : ℚ) : ℝ) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    have hm : (m : ℝ) * Real.log 2 ≤ m * (6931471808 / 10 ^ 10) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      norm_num at this ⊢; linarith
    unfold log2Up
    push_cast
    linarith
  have hLa0 : (0 : ℝ) ≤ ((m * log2Up + log1pUp u nTerms : ℚ) : ℝ) := by
    refine le_trans ?_ hLa
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ 2 ^ m := one_le_pow₀ (by norm_num)
    nlinarith
  have hβR := (show ((8 * K * (1 + 2 / (Y0 : ℚ) + 3 / (Y0 : ℚ) ^ 3) / (3 * (2 ^ m * (1 + u))) : ℚ)
    : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) by exact_mod_cast hβ)
  have hαR := (show ((K * ((2 / 3) * (1 + 2 / (Y0 : ℚ) + 3 / (Y0 : ℚ) ^ 3)
      * (4 * (m * log2Up + log1pUp u nTerms) - 4 + 6 / (Y0 : ℚ) ^ 2 + 5 / 3)
      + 2 * (m * log2Up + log1pUp u nTerms) / Y0 + 2 / (2 ^ m * (1 + u)))
      + 8 * K * (1 + 2 / (Y0 : ℚ) + 3 / (Y0 : ℚ) ^ 3) / (3 * (2 ^ m * (1 + u))) * Y0 : ℚ) : ℝ)
      < (((Y0 : ℚ) / 2 - 1 / 20 - 3 / Y0 : ℚ) : ℝ) by exact_mod_cast hα)
  push_cast at hβR hαR
  exact core K Y0 (2 ^ m * (1 + u)) _ (by exact_mod_cast hK) hY0R ha hLa0 (by exact_mod_cast hLa)
    hβR hαR p x y hYy hxy hp1 hpx

theorem crit_sound {K : ℚ} {Y0 : ℕ} (h : crit K Y0 = true) (p : ℕ) (hp : (Y0 ^ 2 + 2) ^ 2 ≤ p) :
    (K : ℝ) * (bachC p (Nat.sqrt p - 2 : ℕ) * √((Nat.sqrt p - 2 : ℕ) : ℝ) * Real.log p)
      < ((Nat.sqrt p - 2 : ℕ) : ℝ) / 2 - (√((Nat.sqrt p - 2 : ℕ) : ℝ) / 20 + 3) :=
  critCore_sound h p hp

end Grosswald.Crit
