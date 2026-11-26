import SunPrimeDensity.Analytic

/-!
# The range `n^k ≥ 10¹⁰`, every `k ≥ 4`, from Schoenfeld's bound

Let `x = n^k`, `y = (n+1)^k`, `k ≥ 4`. Bernoulli gives `y/x = (1 + 1/n)^k ≥ 1 + k/n`, so
`1 − x/y ≥ k/(n+k) ≥ 4/(n+4) ≥ 4/(s+4)` with `s = x^{1/4} ≥ n`. With Schoenfeld's
`E(t) = √t log t/(8π)`, `E(y)/y ≤ E(x)/x` (`log t/√t` decreases), so it is enough that

`2 E(x) (s + 4) < 4 ((x − 2)/log² x − 2.886)`,

an inequality in `x` alone (`tail_core`). Put `w = x^{1/32}`: `log x = 32 log w ≤ 32 w/e`, and the
inequality becomes polynomial in `w`, true for `w ≥ 2.053` (`w^5 ≥ 36.4` against the needed
`32.5`). `x ≥ 10¹⁰` gives `w > 2.053`.
-/

namespace SunPrimeDensity

open Real Schoenfeld

/-- `log w ≤ w/e` for `w > 0`. -/
lemma log_le_div_exp_one {w : ℝ} (hw : 0 < w) : Real.log w ≤ w / Real.exp 1 := by
  have h := Real.add_one_le_exp (Real.log w - 1)
  rw [Real.exp_sub, Real.exp_log hw] at h
  linarith

/-- The polynomial inequality behind the tail. -/
lemma tail_poly {w : ℝ} (hw : 2.053 ≤ w) :
    46.18 * π * (11.773 * w) ^ 2 + (w ^ 8) ^ 2 * (11.773 * w) ^ 3 * (w ^ 8 + 4)
      < 16 * π * (w ^ 32 - 2) := by
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hw0 : 0 ≤ w := by linarith
  have h2 : (4.2148 : ℝ) ≤ w ^ 2 := by nlinarith
  have h4 : (17.764 : ℝ) ≤ w ^ 4 := by nlinarith
  have h5 : (36.4 : ℝ) ≤ w ^ 5 := by
    have : w ^ 5 = w ^ 4 * w := by ring
    rw [this]; nlinarith
  have h8 : (315 : ℝ) ≤ w ^ 8 := by
    have : w ^ 8 = w ^ 4 * w ^ 4 := by ring
    rw [this]; nlinarith
  have h19 : (1 : ℝ) ≤ w ^ 19 := one_le_pow₀ (by linarith)
  have hw2 : w ^ 2 ≤ w ^ 19 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h19p : 0 ≤ w ^ 19 := by positivity
  have h27p : 0 ≤ w ^ 27 := by positivity
  have e32 : w ^ 32 = w ^ 5 * w ^ 27 := by ring
  have e27 : w ^ 27 = w ^ 8 * w ^ 19 := by ring
  have hA : 36.4 * w ^ 27 ≤ w ^ 32 := by rw [e32]; exact mul_le_mul_of_nonneg_right h5 h27p
  have hB : 315 * w ^ 19 ≤ w ^ 27 := by rw [e27]; exact mul_le_mul_of_nonneg_right h8 h19p
  have eL : 46.18 * π * (11.773 * w) ^ 2 + (w ^ 8) ^ 2 * (11.773 * w) ^ 3 * (w ^ 8 + 4)
      = 46.18 * 11.773 ^ 2 * π * w ^ 2 + 11.773 ^ 3 * w ^ 27 + 4 * 11.773 ^ 3 * w ^ 19 := by ring
  rw [eL]
  nlinarith

/-- **The tail inequality.** For `x ≥ 10¹⁰`,
`2 (√x log x/(8π)) (x^{1/4} + 4) < 4 ((x − 2)/log² x − 2.886)`. -/
theorem tail_core {x : ℝ} (hx : 10 ^ 10 ≤ x) :
    2 * (1 / (8 * π) * (√x * Real.log x)) * (√(√x) + 4)
      < 4 * ((x - 2) / Real.log x ^ 2 - 2.886) := by
  have hx0 : 0 < x := by linarith
  set s := √(√x) with hs
  set w := √(√(√s)) with hw
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hsx : s ^ 2 = √x := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hx4 : s ^ 4 = x := by
    rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, hsx, Real.sq_sqrt hx0.le]
  have hws : w ^ 8 = s := by
    have a1 : w ^ 2 = √(√s) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have a2 : (√(√s)) ^ 2 = √s := Real.sq_sqrt (Real.sqrt_nonneg _)
    have a3 : (√s) ^ 2 = s := Real.sq_sqrt hs0
    rw [show w ^ 8 = ((w ^ 2) ^ 2) ^ 2 by ring, a1, a2, a3]
  have hxw : x = w ^ 32 := by rw [← hx4, ← hws]; ring
  -- `s > 316`, so `w > 2.053`
  have hs316 : 316 < s := by
    by_contra h; push Not at h
    have : s ^ 4 ≤ (316 : ℝ) ^ 4 := pow_le_pow_left₀ hs0 h 4
    rw [hx4] at this; norm_num at this; linarith
  have hw2 : 2.053 ≤ w := by
    by_contra h; push Not at h
    have : w ^ 8 ≤ (2.053 : ℝ) ^ 8 := pow_le_pow_left₀ hw0 h.le 8
    rw [hws] at this; norm_num at this; linarith
  have hwpos : 0 < w := by linarith
  -- `log x ≤ 11.773 w`
  have hLw : Real.log x = 32 * Real.log w := by rw [hxw, Real.log_pow]; push_cast; ring
  have he := Real.exp_one_gt_d9
  have hL : Real.log x ≤ 11.773 * w := by
    have h1 := log_le_div_exp_one hwpos
    have h2 : w / Real.exp 1 ≤ w / 2.7182818283 :=
      div_le_div_of_nonneg_left hw0 (by norm_num) he.le
    rw [hLw]; nlinarith
  have hL0 : 0 < Real.log x := Real.log_pos (by linarith)
  set L := Real.log x
  set Λ := 11.773 * w with hΛ
  have hΛ0 : 0 < Λ := by positivity
  have hpi := Real.pi_pos
  -- replace `L` by `Λ` on both sides
  have hlhs : 2 * (1 / (8 * π) * (√x * L)) * (s + 4) ≤ 2 * (1 / (8 * π) * (√x * Λ)) * (s + 4) := by
    have : √x * L ≤ √x * Λ := mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg _)
    have h8 : 0 ≤ 1 / (8 * π) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h8]
  have hrhs : (x - 2) / Λ ^ 2 ≤ (x - 2) / L ^ 2 :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) (pow_le_pow_left₀ hL0.le hL 2)
  have hP := tail_poly hw2
  -- the polynomial inequality, divided by `4π Λ²`
  have hmain : 2 * (1 / (8 * π) * (√x * Λ)) * (s + 4) < 4 * ((x - 2) / Λ ^ 2 - 2.886) := by
    rw [← hsx, ← hws]
    rw [← hws] at hxw
    have hq : (x - 2) / Λ ^ 2 * Λ ^ 2 = x - 2 := by field_simp
    set q := (x - 2) / Λ ^ 2
    rw [hxw] at hq
    rw [← hΛ] at hP
    have hΛ2 : 0 < Λ ^ 2 := by positivity
    have e : 2 * (1 / (8 * π) * ((w ^ 8) ^ 2 * Λ)) * (w ^ 8 + 4)
        = (w ^ 8) ^ 2 * Λ * (w ^ 8 + 4) / (4 * π) := by field_simp; ring
    rw [e, div_lt_iff₀ (by positivity)]
    have key : ((w ^ 8) ^ 2 * Λ * (w ^ 8 + 4)) * Λ ^ 2 < (4 * (q - 2.886) * (4 * π)) * Λ ^ 2 := by
      have : (4 * (q - 2.886) * (4 * π)) * Λ ^ 2 = 16 * π * (q * Λ ^ 2) - 46.18 * π * Λ ^ 2 - 0.000 * π * Λ ^ 2 := by ring
      rw [this, hq]
      nlinarith
    exact lt_of_mul_lt_mul_right key hΛ2.le
  calc 2 * (1 / (8 * π) * (√x * L)) * (s + 4) ≤ _ := hlhs
    _ < _ := hmain
    _ ≤ 4 * ((x - 2) / L ^ 2 - 2.886) := by linarith

/-- `1 − n^k/(n+1)^k ≥ k/(n+k)` (Bernoulli). -/
lemma one_sub_ratio_ge (n k : ℕ) (hn : 1 ≤ n) :
    (k : ℝ) / (n + k) ≤ 1 - (n : ℝ) ^ k / ((n : ℝ) + 1) ^ k := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hB : 1 + (k : ℝ) * (1 / n) ≤ (1 + 1 / n) ^ k :=
    one_add_mul_le_pow (by have : 0 ≤ 1 / (n : ℝ) := by positivity
                           linarith) k
  have hy : ((n : ℝ) + 1) ^ k = (n : ℝ) ^ k * (1 + 1 / n) ^ k := by
    rw [← mul_pow]; congr 1; field_simp
  have hxk : (0 : ℝ) < (n : ℝ) ^ k := by positivity
  have hpos : (0 : ℝ) < 1 + k * (1 / n) := by positivity
  have hle : (n : ℝ) ^ k / ((n : ℝ) + 1) ^ k ≤ 1 / (1 + k * (1 / n)) := by
    rw [hy, div_le_div_iff₀ (by positivity) hpos]
    nlinarith
  have e : 1 / (1 + (k : ℝ) * (1 / n)) = 1 - k / (n + k) := by
    field_simp; ring
  linarith

/-- **The tail.** For `k ≥ 4`, `n ≥ 2` and `n^k ≥ 10¹⁰`, Schoenfeld's bound gives
`π((n+1)^k)/(n+1)^k < π(n^k)/n^k`. -/
theorem tail (hS : SchoenfeldPi) {k n : ℕ} (hk : 4 ≤ k) (hn : 2 ≤ n) (hx : 10 ^ 10 ≤ n ^ k) :
    (Nat.primeCounting ((n + 1) ^ k) : ℝ) / (((n + 1) ^ k : ℕ) : ℝ) <
      (Nat.primeCounting (n ^ k) : ℝ) / ((n ^ k : ℕ) : ℝ) := by
  set x : ℝ := ((n ^ k : ℕ) : ℝ) with hxdef
  set y : ℝ := (((n + 1) ^ k : ℕ) : ℝ) with hydef
  have hxR : (10 : ℝ) ^ 10 ≤ x := by rw [hxdef]; exact_mod_cast hx
  have hx0 : 0 < x := by linarith
  have hxy : x < y := by
    rw [hxdef, hydef]; exact_mod_cast Nat.pow_lt_pow_left (by omega) (by omega)
  have hy0 : 0 < y := by linarith
  have hfx : ⌊x⌋₊ = n ^ k := Nat.floor_natCast _
  have hfy : ⌊y⌋₊ = (n + 1) ^ k := Nat.floor_natCast _
  have hSx := hS x (by linarith)
  have hSy := hS y (by linarith)
  rw [hfx] at hSx
  rw [hfy] at hSy
  have hlx : 2 ≤ Real.log x := by
    have := Real.add_one_le_exp (2 : ℝ)
    have h7 : Real.exp 2 ≤ x := by
      have : Real.exp 2 < 8 := by
        have := Real.exp_one_lt_d9
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith [Real.exp_pos 1]
      linarith
    rw [← Real.log_exp 2]; exact Real.log_le_log (Real.exp_pos 2) h7
  set Ex := 1 / (8 * π) * (√x * Real.log x)
  set Ey := 1 / (8 * π) * (√y * Real.log y)
  set Dl := (x - 2) / Real.log x ^ 2 - 2.886
  have hpi := Real.pi_pos
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
  have hsy : 0 < √y := Real.sqrt_pos.mpr hy0
  -- `Ey/y ≤ Ex/x`
  have hEx : Ex / x = 1 / (8 * π) * (Real.log x / √x) := by
    have : √x * √x = x := Real.mul_self_sqrt hx0.le
    simp only [Ex]; field_simp; rw [← this]; ring
  have hEy : Ey / y = 1 / (8 * π) * (Real.log y / √y) := by
    have : √y * √y = y := Real.mul_self_sqrt hy0.le
    simp only [Ey]; field_simp; rw [← this]; ring
  have hmono : Ey / y ≤ Ex / x := by
    rw [hEx, hEy]
    exact mul_le_mul_of_nonneg_left (log_div_sqrt_anti hx0 hlx hxy.le) (by positivity)
  -- `1 − x/y ≥ 4/(s + 4)`
  set s := √(√x)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hns : (n : ℝ) ≤ s := by
    have h4 : (n : ℝ) ^ 4 ≤ x := by
      rw [hxdef]; push_cast
      exact pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ n by omega)) hk
    have hsx4 : s ^ 4 = x := by
      have : s ^ 2 = √x := Real.sq_sqrt (Real.sqrt_nonneg _)
      rw [show s ^ 4 = (s ^ 2) ^ 2 by ring, this, Real.sq_sqrt hx0.le]
    rw [← hsx4] at h4
    exact (pow_le_pow_iff_left₀ (by positivity) hs0 (by norm_num)).mp h4
  have hratio : 4 / (s + 4) ≤ 1 - x / y := by
    have h1 := one_sub_ratio_ge n k (by omega)
    have e : x / y = (n : ℝ) ^ k / ((n : ℝ) + 1) ^ k := by rw [hxdef, hydef]; push_cast; ring
    rw [e]
    refine le_trans ?_ h1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hk4 : (4 : ℝ) ≤ k := by exact_mod_cast hk
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hcore := tail_core hxR
  have hDl : 0 < Dl := by
    have : 0 < 2 * Ex * (s + 4) := by positivity
    simp only [Dl]; nlinarith
  have hkey : Ex / x + Ey / y < (1 - x / y) * Dl / x := by
    have h1 : 2 * Ex * (s + 4) < 4 * Dl := by simpa [mul_assoc] using hcore
    have h2 : 2 * (Ex / x) < 4 / (s + 4) * Dl / x := by
      rw [div_mul_eq_mul_div, div_div, lt_div_iff₀ (by positivity)]
      have e : 2 * (Ex / x) * ((s + 4) * x) = 2 * Ex * (s + 4) := by field_simp
      rw [e]; linarith
    have h3 : 4 / (s + 4) * Dl / x ≤ (1 - x / y) * Dl / x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hratio hDl.le) hx0.le
    linarith
  exact ratio_lt_of_bounds (by linarith) hxy hSx.le hSy.le (logIntegral_sub_ge (by linarith)) hkey

end SunPrimeDensity
