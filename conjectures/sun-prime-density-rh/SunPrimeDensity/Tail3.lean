import SunPrimeDensity.Tail

/-!
# The exponent `k = 3` for `n ≥ 10⁷`, from Schoenfeld's bound

With `x = n³`, `y = (n+1)³`: `1 − x/y ≥ 3/(n+3)` (Bernoulli) and `E(y)/y ≤ E(x)/x`, so it is
enough that `2 E(x) (n + 3) < 3 ((x − 2)/log² x − 2.886)` (`tail3_core`). With `w = n^{1/16}`,
`log x = 48 log w ≤ 48 w/e`, and the inequality is polynomial in `w`, true for `w ≥ 2.738`
(`w^5 ≥ 153` against the needed `146.1`); `n ≥ 10⁷` gives `w > 2.738`.

Below `10⁷` Schoenfeld's bound does not separate the two terms for `k = 3` (the last failure
of this sufficient condition is at `n = 8441232`; with the sharper `li(x) − x/log x ≈ x/log² x
+ 2x/log³ x` it is near `n = 7.33·10⁶`), and the PsiCert bound only reaches `x = 10¹⁰`, that
is `n ≤ 2154`.
-/

namespace SunPrimeDensity

open Real Schoenfeld

/-- The polynomial inequality behind the `k = 3` tail. -/
lemma tail3_poly {w : ℝ} (hw : 2.738 ≤ w) (h16 : 10 ^ 7 ≤ w ^ 16) :
    34.632 * π * (17.659 * w) ^ 2 + w ^ 24 * (17.659 * w) ^ 3 * (w ^ 16 + 3)
      < 12 * π * (w ^ 48 - 2) := by
  have hp1 := Real.pi_gt_d6
  have hp2 := Real.pi_lt_d6
  have hw0 : 0 ≤ w := by linarith
  have h2 : (7.4966 : ℝ) ≤ w ^ 2 := by nlinarith
  have h4 : (56.199 : ℝ) ≤ w ^ 4 := by
    have : w ^ 4 = w ^ 2 * w ^ 2 := by ring
    rw [this]; nlinarith
  have h5 : (153 : ℝ) ≤ w ^ 5 := by
    have : w ^ 5 = w ^ 4 * w := by ring
    rw [this]; nlinarith
  have h27 : (1 : ℝ) ≤ w ^ 27 := one_le_pow₀ (by linarith)
  have hw2 : w ^ 2 ≤ w ^ 27 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have h27p : 0 ≤ w ^ 27 := by positivity
  have h43p : 0 ≤ w ^ 43 := by positivity
  have e48 : w ^ 48 = w ^ 5 * w ^ 43 := by ring
  have e43 : w ^ 43 = w ^ 16 * w ^ 27 := by ring
  have hA : 153 * w ^ 43 ≤ w ^ 48 := by rw [e48]; exact mul_le_mul_of_nonneg_right h5 h43p
  have hB : 10 ^ 7 * w ^ 27 ≤ w ^ 43 := by rw [e43]; exact mul_le_mul_of_nonneg_right h16 h27p
  have eL : 34.632 * π * (17.659 * w) ^ 2 + w ^ 24 * (17.659 * w) ^ 3 * (w ^ 16 + 3)
      = 34.632 * 17.659 ^ 2 * π * w ^ 2 + 17.659 ^ 3 * w ^ 43 + 3 * 17.659 ^ 3 * w ^ 27 := by
    ring
  rw [eL]
  nlinarith

/-- **The `k = 3` tail inequality.** For `m ≥ 10⁷`, with `x = m³`,
`2 (√x log x/(8π)) (m + 3) < 3 ((x − 2)/log² x − 2.886)`. -/
theorem tail3_core {m : ℝ} (hm : 10 ^ 7 ≤ m) :
    2 * (1 / (8 * π) * (√(m ^ 3) * Real.log (m ^ 3))) * (m + 3)
      < 3 * ((m ^ 3 - 2) / Real.log (m ^ 3) ^ 2 - 2.886) := by
  have hm0 : 0 < m := by linarith
  have hm3 : (10 : ℝ) ^ 7 ≤ m ^ 3 :=
    calc (10 : ℝ) ^ 7 ≤ m := hm
      _ = m ^ 1 := (pow_one m).symm
      _ ≤ m ^ 3 := pow_le_pow_right₀ (by linarith) (by norm_num)
  set w := √(√(√(√m))) with hw
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hwm : w ^ 16 = m := by
    have a1 : w ^ 2 = √(√(√m)) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have a2 : (√(√(√m))) ^ 2 = √(√m) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have a3 : (√(√m)) ^ 2 = √m := Real.sq_sqrt (Real.sqrt_nonneg _)
    have a4 : (√m) ^ 2 = m := Real.sq_sqrt hm0.le
    rw [show w ^ 16 = (((w ^ 2) ^ 2) ^ 2) ^ 2 by ring, a1, a2, a3, a4]
  have hx : m ^ 3 = w ^ 48 := by rw [← hwm]; ring
  have hsx : √(m ^ 3) = w ^ 24 := by
    rw [hx, show w ^ 48 = (w ^ 24) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have h16 : (10 : ℝ) ^ 7 ≤ w ^ 16 := by rw [hwm]; exact hm
  have hw2 : 2.738 ≤ w := by
    by_contra h; push Not at h
    have : w ^ 16 ≤ (2.738 : ℝ) ^ 16 := pow_le_pow_left₀ hw0 h.le 16
    norm_num at this; linarith
  have hwpos : 0 < w := by linarith
  have hLw : Real.log (m ^ 3) = 48 * Real.log w := by rw [hx, Real.log_pow]; push_cast; ring
  have he := Real.exp_one_gt_d9
  have hL : Real.log (m ^ 3) ≤ 17.659 * w := by
    have h1 := log_le_div_exp_one hwpos
    have h2 : w / Real.exp 1 ≤ w / 2.7182818283 :=
      div_le_div_of_nonneg_left hw0 (by norm_num) he.le
    have h3 : w / 2.7182818283 ≤ 0.36788 * w := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    rw [hLw]; linarith
  have hL0 : 0 < Real.log (m ^ 3) := Real.log_pos (by linarith)
  set L := Real.log (m ^ 3)
  set Λ := 17.659 * w with hΛ
  have hΛ0 : 0 < Λ := by positivity
  have hpi := Real.pi_pos
  have hlhs : 2 * (1 / (8 * π) * (√(m ^ 3) * L)) * (m + 3)
      ≤ 2 * (1 / (8 * π) * (√(m ^ 3) * Λ)) * (m + 3) := by
    have : √(m ^ 3) * L ≤ √(m ^ 3) * Λ := mul_le_mul_of_nonneg_left hL (Real.sqrt_nonneg _)
    have h8 : 0 ≤ 1 / (8 * π) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left this h8]
  have hrhs : (m ^ 3 - 2) / Λ ^ 2 ≤ (m ^ 3 - 2) / L ^ 2 :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) (pow_le_pow_left₀ hL0.le hL 2)
  have hP := tail3_poly hw2 h16
  rw [hwm, ← hx, ← hΛ] at hP
  have hmain : 2 * (1 / (8 * π) * (√(m ^ 3) * Λ)) * (m + 3)
      < 3 * ((m ^ 3 - 2) / Λ ^ 2 - 2.886) := by
    rw [hsx, ← hwm]
    rw [← hwm] at hP
    have hΛ2 : 0 < Λ ^ 2 := by positivity
    have e1 : 2 * (1 / (8 * π) * (w ^ 24 * Λ)) * (w ^ 16 + 3)
        = w ^ 24 * Λ ^ 3 * (w ^ 16 + 3) / (4 * π * Λ ^ 2) := by
      field_simp; ring
    have e2 : 3 * (((w ^ 16) ^ 3 - 2) / Λ ^ 2 - 2.886)
        = (12 * π * ((w ^ 16) ^ 3 - 2) - 34.632 * π * Λ ^ 2) / (4 * π * Λ ^ 2) := by
      field_simp; ring
    rw [e1, e2]
    apply div_lt_div_of_pos_right _ (by positivity)
    have e3 : (w ^ 16) ^ 3 = w ^ 48 := by ring
    rw [e3]
    rw [show (w ^ 16) ^ 3 = w ^ 48 by ring] at hP
    nlinarith [mul_pos hpi hΛ2]
  calc 2 * (1 / (8 * π) * (√(m ^ 3) * L)) * (m + 3) ≤ _ := hlhs
    _ < _ := hmain
    _ ≤ 3 * ((m ^ 3 - 2) / L ^ 2 - 2.886) := by linarith

/-- **`k = 3`, `n ≥ 10⁷`.** Schoenfeld's bound gives
`π((n+1)³)/(n+1)³ < π(n³)/n³` for every `n ≥ 10⁷`. -/
theorem tail_three (hS : SchoenfeldPi) {n : ℕ} (hn : 10 ^ 7 ≤ n) :
    (Nat.primeCounting ((n + 1) ^ 3) : ℝ) / (((n : ℝ) + 1) ^ 3) <
      (Nat.primeCounting (n ^ 3) : ℝ) / ((n : ℝ) ^ 3) := by
  have hnR : (10 : ℝ) ^ 7 ≤ n := by exact_mod_cast hn
  set m : ℝ := (n : ℝ) with hmdef
  set x : ℝ := m ^ 3 with hxdef
  set y : ℝ := (m + 1) ^ 3 with hydef
  have hm0 : 0 < m := by linarith
  have hx0 : 0 < x := by positivity
  have hxy : x < y := by
    rw [hxdef, hydef]; exact pow_lt_pow_left₀ (by linarith) hm0.le (by norm_num)
  have hy0 : 0 < y := by linarith
  have hx2657 : (2657 : ℝ) ≤ x := by rw [hxdef]; nlinarith
  have hfx : ⌊x⌋₊ = n ^ 3 := by
    rw [hxdef, hmdef, show (n : ℝ) ^ 3 = ((n ^ 3 : ℕ) : ℝ) by push_cast; ring]
    exact Nat.floor_natCast _
  have hfy : ⌊y⌋₊ = (n + 1) ^ 3 := by
    rw [hydef, hmdef, show ((n : ℝ) + 1) ^ 3 = (((n + 1) ^ 3 : ℕ) : ℝ) by push_cast; ring]
    exact Nat.floor_natCast _
  have hSx := hS x hx2657
  have hSy := hS y (by linarith)
  rw [hfx] at hSx
  rw [hfy] at hSy
  have hlx : 2 ≤ Real.log x := by
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
  have hEx : Ex / x = 1 / (8 * π) * (Real.log x / √x) := by
    have h : √x * Real.log x / x = Real.log x / √x := by
      rw [div_eq_div_iff hx0.ne' hsx.ne']
      have := Real.mul_self_sqrt hx0.le
      linear_combination Real.log x * this
    simp only [Ex]; rw [mul_div_assoc, h]
  have hEy : Ey / y = 1 / (8 * π) * (Real.log y / √y) := by
    have h : √y * Real.log y / y = Real.log y / √y := by
      rw [div_eq_div_iff hy0.ne' hsy.ne']
      have := Real.mul_self_sqrt hy0.le
      linear_combination Real.log y * this
    simp only [Ey]; rw [mul_div_assoc, h]
  have hmono : Ey / y ≤ Ex / x := by
    rw [hEx, hEy]
    exact mul_le_mul_of_nonneg_left (log_div_sqrt_anti hx0 hlx hxy.le) (by positivity)
  have hratio : 3 / (m + 3) ≤ 1 - x / y := by
    have h1 := one_sub_ratio_ge n 3 (by omega)
    push_cast at h1
    exact h1
  have hcore := tail3_core hnR
  have hDl : 0 < Dl := by
    have : 0 < 2 * Ex * (m + 3) := by positivity
    simp only [Dl]; nlinarith
  have hkey : Ex / x + Ey / y < (1 - x / y) * Dl / x := by
    have h1 : 2 * Ex * (m + 3) < 3 * Dl := hcore
    have h2 : 2 * (Ex / x) < 3 / (m + 3) * Dl / x := by
      rw [div_mul_eq_mul_div, div_div, lt_div_iff₀ (by positivity)]
      have e : 2 * (Ex / x) * ((m + 3) * x) = 2 * Ex * (m + 3) := by field_simp
      rw [e]; linarith
    have h3 : 3 / (m + 3) * Dl / x ≤ (1 - x / y) * Dl / x :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hratio hDl.le) hx0.le
    linarith
  exact ratio_lt_of_bounds (by linarith) hxy hSx.le hSy.le (logIntegral_sub_ge (by linarith)) hkey

end SunPrimeDensity
