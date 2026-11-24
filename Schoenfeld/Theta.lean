import Schoenfeld.Psi

/-!
# `|θ(x) − x| < √x log² x / 2` for `x ≥ 599`, under RH

From the ψ bound and Mathlib's `0 ≤ ψ(x) − θ(x) ≤ 2 √x log x`
(`Chebyshev.psi_sub_theta_le`): `|θ(x) − x| < (1/8 + 2/log x) √x log² x`, and
`2/log x ≤ 3/8` once `log x ≥ 16/3` (`x ≥ 512 > e^{16/3}`).
-/

namespace Schoenfeld

open Real Chebyshev

/-- `|θ(x) − x| < √x log² x / 8 + 2 √x log x` for `x ≥ 73.2`. -/
theorem theta_sub_lt (hRH : RiemannHypothesis) {x : ℝ} (hx : 73.2 ≤ x) :
    |θ x - x| < 1 / 8 * (√x * Real.log x ^ 2) + 2 * √x * Real.log x := by
  have hψ := psiBound_of_RH hRH x hx
  have h1 := theta_le_psi x
  have h2 := psi_sub_theta_le (x := x) (by linarith)
  rw [abs_lt] at hψ ⊢
  constructor <;> linarith [hψ.1, hψ.2]

theorem thetaBound_of_RH (hRH : RiemannHypothesis) : ThetaBound (1 / 2) 599 := by
  intro x hx
  have h := theta_sub_lt hRH (x := x) (by linarith)
  have hl : 16 / 3 ≤ Real.log x := by
    have := log_ge_of_pow_le 9 (show (2 : ℝ) ^ 9 ≤ x by norm_num; linarith)
    have : (2 : ℝ) ^ 9 / x ≤ 1 := by rw [div_le_one (by linarith)]; norm_num; linarith
    norm_num at *; linarith
  have hs : 0 ≤ √x := Real.sqrt_nonneg x
  have : 2 * √x * Real.log x ≤ 3 / 8 * (√x * Real.log x ^ 2) := by
    have := mul_le_mul_of_nonneg_left hl (mul_nonneg hs (by linarith : (0 : ℝ) ≤ Real.log x))
    nlinarith
  linarith

end Schoenfeld
