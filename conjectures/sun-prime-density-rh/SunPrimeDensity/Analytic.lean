import Schoenfeld.Rosser
import Schoenfeld.Check.Li

/-!
# The analytic comparison

For `2 ≤ x < y` write `D(x) = li(x) − x/log x`. Since `li(y) − li(x) ≤ (y − x)/log x`,

`li(x)/x − li(y)/y ≥ (1 − x/y) · D(x)/x`,

and `D(x) ≥ (x − 2)/log² x − 2.886` (integration by parts, `li(x) = li(2) + x/log x − 2/log 2 +
∫₂ˣ dt/log² t`, and `|2/log 2 − li(2)| ≤ 2.886`). So if `|π(x) − li(x)| ≤ E_x`,
`|π(y) − li(y)| ≤ E_y` and

`(1 − x/y) · D(x)/x > E_x/x + E_y/y`,

then `π(y)/y < π(x)/x` (`ratio_lt_of_bounds`). Two error terms are used:

* Schoenfeld's `√t log t/(8π)` for `t ≥ 2657` (RH);
* `piErrMid t = 3.9252 √t/log t + 49.886 + 3.9252 · (10.15/6.15) · 2√t/log² t` for
  `4·10⁵ ≤ t ≤ 10¹⁰` (`pi_mid_explicit`), from schoenfeld-rh's PsiCert (an exact computation
  of `ψ` up to `10¹⁰`, no RH). It is the bound inside schoenfeld-rh's `pi_mid`, kept as a
  function of `t`.
-/

namespace SunPrimeDensity

open Real Chebyshev MeasureTheory Schoenfeld

/-- `D(x) = li(x) − x/log x ≥ (x − 2)/log² x − 2.886` for `x ≥ 2`. -/
theorem logIntegral_sub_ge {x : ℝ} (hx : 2 ≤ x) :
    (x - 2) / Real.log x ^ 2 - 2.886 ≤ logIntegral x - x / Real.log x := by
  rw [Schoenfeld.logIntegral_eq hx]
  have hc := abs_le.mp Schoenfeld.pi_const_bound
  have hlx : 0 < Real.log x := Real.log_pos (by linarith)
  have hI : (x - 2) / Real.log x ^ 2 ≤ ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
    have hmono : ∫ t in (2 : ℝ)..x, (1 / Real.log x ^ 2) ≤ ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
      refine intervalIntegral.integral_mono_on hx intervalIntegrable_const
        (Schoenfeld.continuousOn_inv_log le_rfl hx 2).intervalIntegrable (fun t ht => ?_)
      have ht2 : 2 ≤ t := ht.1
      have hlt : 0 < Real.log t := Real.log_pos (by linarith)
      have hle : Real.log t ≤ Real.log x := Real.log_le_log (by linarith) ht.2
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hlt.le hle 2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
    calc (x - 2) / Real.log x ^ 2 = (x - 2) * (1 / Real.log x ^ 2) := by ring
      _ ≤ _ := hmono
  linarith [hc.1, hc.2]

/-- `li(y) − li(x) ≤ (y − x)/log x` for `2 ≤ x ≤ y`. -/
theorem logIntegral_sub_le {x y : ℝ} (hx : 2 ≤ x) (hxy : x ≤ y) :
    logIntegral y - logIntegral x ≤ (y - x) / Real.log x := by
  rw [Schoenfeld.Check.logIntegral_eq_add hx (hx.trans hxy)]
  have := (Schoenfeld.Check.integral_inv_log_bounds (a := x) (b := y) (by linarith) hxy).2
  linarith

/-- **The comparison.** If `π(x)`, `π(y)` are within `Ex`, `Ey` of `li`, `Dl ≤ li(x) − x/log x`
and `(1 − x/y)·Dl/x > Ex/x + Ey/y`, then `π(y)/y < π(x)/x`. -/
theorem ratio_lt_of_bounds {x y Px Py Ex Ey Dl : ℝ} (hx : 2 ≤ x) (hxy : x < y)
    (hPx : |Px - logIntegral x| ≤ Ex) (hPy : |Py - logIntegral y| ≤ Ey)
    (hD : Dl ≤ logIntegral x - x / Real.log x)
    (hkey : Ex / x + Ey / y < (1 - x / y) * Dl / x) :
    Py / y < Px / x := by
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hl : 0 < Real.log x := Real.log_pos (by linarith)
  have hli := logIntegral_sub_le hx hxy.le
  set A := logIntegral x - x / Real.log x with hA
  have hPy' : Py ≤ logIntegral y + Ey := by linarith [(abs_le.mp hPy).2]
  have hPx' : logIntegral x - Ex ≤ Px := by linarith [(abs_le.mp hPx).1]
  -- `Py ≤ y/log x + A + Ey`
  have h1 : Py ≤ y / Real.log x + A + Ey := by
    have : y / Real.log x = x / Real.log x + (y - x) / Real.log x := by ring
    rw [this, hA]; linarith
  -- `Px ≥ x/log x + A − Ex`
  have h2 : x / Real.log x + A - Ex ≤ Px := by rw [hA]; linarith
  have e1 : (y / Real.log x + A + Ey) / y = 1 / Real.log x + A / y + Ey / y := by
    field_simp
  have e2 : (x / Real.log x + A - Ex) / x = 1 / Real.log x + A / x - Ex / x := by
    field_simp
  have hkey' : (1 - x / y) * Dl / x = Dl / x - Dl / y := by field_simp
  have hxy' : 1 / y ≤ 1 / x := one_div_le_one_div_of_le hx0 hxy.le
  have hAD : Dl * (1 / x - 1 / y) ≤ A * (1 / x - 1 / y) :=
    mul_le_mul_of_nonneg_right hD (by linarith)
  have e3 : Dl * (1 / x - 1 / y) = Dl / x - Dl / y := by ring
  have e4 : A * (1 / x - 1 / y) = A / x - A / y := by ring
  calc Py / y ≤ (y / Real.log x + A + Ey) / y := div_le_div_of_nonneg_right h1 hy0.le
    _ = 1 / Real.log x + A / y + Ey / y := e1
    _ < 1 / Real.log x + A / x - Ex / x := by linarith
    _ = (x / Real.log x + A - Ex) / x := e2.symm
    _ ≤ Px / x := div_le_div_of_nonneg_right h2 hx0.le

/-- The explicit error term on `[4·10⁵, 10¹⁰]`. -/
noncomputable def piErrMid (t : ℝ) : ℝ :=
  3.9252 * (√t / Real.log t) + 49.886 + 3.9252 * (10.15 / (10.15 - 4) * (2 * √t / Real.log t ^ 2))

/-- **`|π(x) − li(x)| ≤ piErrMid x` for `4·10⁵ ≤ x ≤ 10¹⁰`**, from PsiCert and
`ThetaSmallRange` (no RH): the bound in schoenfeld-rh's `pi_mid`, before it is weakened to
`√x log x/(8π)`. -/
theorem pi_mid_explicit (hC : PsiCert) (hS : ThetaSmallRange) {x : ℝ} (h1 : 400000 ≤ x)
    (h2 : x ≤ 10 ^ 10) :
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x| ≤ piErrMid x := by
  have hx2 : 2 ≤ x := by linarith
  rw [pi_sub_li_eq hx2]
  have I := fun a b (ha : (2 : ℝ) ≤ a) (hab : a ≤ b) => intervalIntegrable_gfun ha hab
  have hsplit : ∫ t in (2 : ℝ)..x, gfun t = (∫ t in (2 : ℝ)..599, gfun t)
      + (∫ t in (599 : ℝ)..30000, gfun t) + ∫ t in (30000 : ℝ)..x, gfun t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (I 2 599 (by norm_num) (by norm_num))
      (I 599 30000 (by norm_num) (by norm_num)),
      intervalIntegral.integral_add_adjacent_intervals (I 2 30000 (by norm_num) (by norm_num))
      (I 30000 x (by norm_num) (by linarith))]
  rw [hsplit]
  have hI1 := integral_small
  have hI2 := integral_piece2 hS
  have hI3 := integral_piece3 hC (b := x) (by linarith) h2
  have hc := pi_const_bound
  have hθ := theta_mid_abs hC (x := x) (by linarith) h2
  have hu0 : 0 < Real.log x := Real.log_pos (by linarith)
  have hA : |(θ x - x) / Real.log x| ≤ 3.9252 * (√x / Real.log x) := by
    rw [abs_div, abs_of_pos hu0, mul_div_assoc']
    exact div_le_div_of_nonneg_right hθ hu0.le
  set A := (θ x - x) / Real.log x
  set B1 := ∫ t in (2 : ℝ)..599, gfun t
  set B2 := ∫ t in (599 : ℝ)..30000, gfun t
  set B3 := ∫ t in (30000 : ℝ)..x, gfun t
  set C := 2 / Real.log 2 - logIntegralTwo
  have a1 := abs_add_le (A + (B1 + B2 + B3)) C
  have a2 := abs_add_le A (B1 + B2 + B3)
  have a3 := abs_add_le (B1 + B2) B3
  have a4 := abs_add_le B1 B2
  unfold piErrMid
  linarith

/-- `log t/√t` decreases on `[e², ∞)`: `log y/√y ≤ log x/√x` for `x ≤ y`, `log x ≥ 2`. -/
theorem log_div_sqrt_anti {x y : ℝ} (hx0 : 0 < x) (hx : 2 ≤ Real.log x) (hxy : x ≤ y) :
    Real.log y / √y ≤ Real.log x / √x := by
  have hy0 : 0 < y := hx0.trans_le hxy
  set r := y / x with hr
  have hr1 : 1 ≤ r := by rw [hr, le_div_iff₀ hx0]; linarith
  have hyr : y = x * r := by rw [hr]; field_simp
  have hsr : 1 ≤ √r := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hr1
  have hlogr : Real.log r ≤ 2 * (√r - 1) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < √r by linarith)
    have : Real.log r = 2 * Real.log √r := by
      rw [← Real.log_rpow (by linarith), show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num,
        Real.rpow_natCast, Real.sq_sqrt (by linarith)]
    linarith
  have hsx : 0 < √x := Real.sqrt_pos.mpr hx0
  have hsy : √y = √x * √r := by rw [hyr, Real.sqrt_mul hx0.le]
  have hly : Real.log y = Real.log x + Real.log r := by
    rw [hyr, Real.log_mul hx0.ne' (by linarith)]
  rw [hsy, hly, div_le_div_iff₀ (by positivity) hsx]
  have : Real.log r ≤ Real.log x * (√r - 1) := by nlinarith
  have hlx : 0 ≤ Real.log x := by linarith
  nlinarith [mul_le_mul_of_nonneg_left this hsx.le]

end SunPrimeDensity
