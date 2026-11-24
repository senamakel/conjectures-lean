import Schoenfeld.Psi

/-!
# `|θ(x) − x| < √x log² x / 4` for `x ≥ 599`, under RH

`0 ≤ ψ(x) − θ(x) ≤ ψ(x^{1/2}) + ψ(x^{1/3}) + ψ(x^{1/5})` (Costa Pereira, in Mathlib) and
Mathlib's `ψ(y) ≤ log 4 · y + 2 √y log y` give `ψ(x) − θ(x) ≤ √x log² x / 8` for `x ≥ 599`
(`psi_sub_theta_le_eighth`; ratio `0.91` at `x = 599`); add the ψ bound. `theta_sub_lt` is the
cruder form with Mathlib's `ψ − θ ≤ 2 √x log x`, valid from `x ≥ 73.2`.
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

/-! ### A sharper `ψ − θ` (Costa Pereira) -/

/-- Twelfth roots: `x = a¹²`. -/
lemma twelfth_root {x : ℝ} (hx : 0 ≤ x) :
    ∃ a : ℝ, 0 ≤ a ∧ x = a ^ 12 ∧ x ^ (2 : ℝ)⁻¹ = a ^ 6 ∧ x ^ (3 : ℝ)⁻¹ = a ^ 4 := by
  refine ⟨x ^ ((1 : ℝ) / 12), by positivity, ?_, ?_, ?_⟩ <;>
  · rw [← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

/-- `ψ(x) − θ(x) ≤ ψ(x^{1/2}) + 2 ψ(x^{1/3})`, then Mathlib's `ψ(y) ≤ log 4 · y + 2 √y log y`:
for `x ≥ 599`, `ψ(x) − θ(x) ≤ (1/8) √x log² x`. -/
theorem psi_sub_theta_le_eighth {x : ℝ} (hx : 599 ≤ x) :
    ψ x - θ x ≤ 1 / 8 * (√x * Real.log x ^ 2) := by
  have hx0 : 0 ≤ x := by linarith
  have hCP := psi_sub_theta_le_psi_add_psi_add_psi x
  have h53 : ψ (x ^ (5 : ℝ)⁻¹) ≤ ψ (x ^ (3 : ℝ)⁻¹) :=
    psi_mono (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  obtain ⟨a, ha0, hxa, h2, h3⟩ := twelfth_root hx0
  rw [h2, h3] at hCP
  rw [h3] at h53
  have ha : 1.7039 ≤ a := by
    by_contra h
    push Not at h
    have : a ^ 12 < 1.7039 ^ 12 := pow_lt_pow_left₀ h ha0 (by norm_num)
    norm_num at this; linarith
  have hlx : 6.38 ≤ Real.log x := by
    have := log_ge_of_pow_le 9 (show (2 : ℝ) ^ 9 ≤ x by norm_num; linarith)
    have : (2 : ℝ) ^ 9 / x ≤ 512 / 599 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; norm_num; linarith
    norm_num at *; linarith
  set ℓ := Real.log a with hℓ
  have hL : Real.log x = 12 * ℓ := by rw [hxa, Real.log_pow]; push_cast; ring
  have hℓ0 : 0.5316 ≤ ℓ := by linarith
  have hsx : √x = a ^ 6 := by
    rw [hxa, show a ^ 12 = (a ^ 6) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hl4 : Real.log 4 ≤ 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
    linarith [Real.log_two_lt_d9]
  -- `ψ(a⁶) ≤ log 4 · a⁶ + 12 a³ ℓ` and `ψ(a⁴) ≤ log 4 · a⁴ + 8 a² ℓ`
  have hp6 := psi_le (x := a ^ 6) (one_le_pow₀ (by linarith))
  have hp4 := psi_le (x := a ^ 4) (one_le_pow₀ (by linarith))
  rw [show a ^ 6 = (a ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.log_pow] at hp6
  rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.log_pow] at hp4
  rw [show (a ^ 3) ^ 2 = a ^ 6 by ring] at hp6
  rw [show (a ^ 2) ^ 2 = a ^ 4 by ring] at hp4
  rw [Real.log_pow] at hp6 hp4
  push_cast at hp6 hp4
  rw [← hℓ] at hp6 hp4
  rw [hsx, hL]
  have ha2 : 2.9032 ≤ a ^ 2 := by nlinarith
  have ha3 : 4.9468 ≤ a ^ 3 := by nlinarith
  have ha4 : 8.4286 ≤ a ^ 4 := by nlinarith
  have ha6 : 0 < a ^ 6 := by positivity
  have e1 : 12 * a ^ 3 * ℓ ≤ 2.4259 * a ^ 6 * ℓ := by
    have : a ^ 6 = a ^ 3 * a ^ 3 := by ring
    rw [this]; nlinarith [mul_le_mul_of_nonneg_left ha3 (by positivity : (0 : ℝ) ≤ a ^ 3 * ℓ)]
  have e2 : 2 * (1.3863 * a ^ 4) ≤ 0.9551 * a ^ 6 := by
    have : a ^ 6 = a ^ 4 * a ^ 2 := by ring
    rw [this]; nlinarith [mul_le_mul_of_nonneg_left ha2 (by positivity : (0 : ℝ) ≤ a ^ 4)]
  have e3 : 16 * a ^ 2 * ℓ ≤ 1.8984 * a ^ 6 * ℓ := by
    have : a ^ 6 = a ^ 2 * a ^ 4 := by ring
    rw [this]; nlinarith [mul_le_mul_of_nonneg_left ha4 (by positivity : (0 : ℝ) ≤ a ^ 2 * ℓ)]
  have hq : 1.3863 + 0.9551 + (2.4259 + 1.8984) * ℓ ≤ 18 * ℓ ^ 2 := by nlinarith
  have hq' := mul_le_mul_of_nonneg_left hq ha6.le
  have hψ4 : 0 ≤ Real.log 4 * a ^ 4 := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hl4 ha6.le, mul_le_mul_of_nonneg_right hl4
    (by positivity : (0 : ℝ) ≤ a ^ 4)]

/-- `|θ(x) − x| < √x log² x / 4` for `x ≥ 599`. -/
theorem theta_sub_lt_quarter (hRH : RiemannHypothesis) {x : ℝ} (hx : 599 ≤ x) :
    |θ x - x| < 1 / 4 * (√x * Real.log x ^ 2) := by
  have hψ := psiBound_of_RH hRH x (by linarith)
  have h1 := theta_le_psi x
  have h2 := psi_sub_theta_le_eighth hx
  rw [abs_lt] at hψ ⊢
  constructor <;> linarith [hψ.1, hψ.2]

/-- **`|θ(x) − x| < √x log² x / 4` for `x ≥ 599`, under RH.** -/
theorem thetaBound_of_RH (hRH : RiemannHypothesis) : ThetaBound (1 / 4) 599 :=
  fun _ hx => theta_sub_lt_quarter hRH hx

end Schoenfeld
