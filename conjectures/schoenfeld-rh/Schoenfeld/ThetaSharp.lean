import Schoenfeld.PsiSharp
import Schoenfeld.Theta
import Schoenfeld.Inputs

/-!
# `|θ(x) − x| < √x log² x / (8π)` for `x ≥ 3·10⁴`, under RH, Rosser's count and PsiCert

`θ = ψ − (ψ − θ)` with Costa Pereira's `0 ≤ ψ(x) − θ(x) ≤ ψ(x^{1/2}) + 2ψ(x^{1/3})` (Mathlib).

* `x ≥ 10¹⁰` (`theta_explicit`): `ψ(y) ≤ 1.0026 y` for `y ≥ 10⁵` and `ψ(z) ≤ 1.0173 z` for
  `z ≥ 2154` (PsiCert below `10¹⁰`, `psi_explicit` above), and `x^{1/3} ≤ 0.02155 √x`, so
  `ψ − θ ≤ 1.047 √x` and `|θ(x) − x| ≤ √x (u²/(8π) − 0.2985 u + 5.667)`.
* `3·10⁴ ≤ x ≤ 10¹⁰` (`theta_mid`): PsiCert for `ψ(x)`, Mathlib's `ψ(y) ≤ log 4 · y + 2√y log y`
  for `ψ − θ`, in the variable `a = x^{1/12} ≥ 2.36`.
-/

namespace Schoenfeld

open Real Chebyshev

/-- `log (q^n) ≤ n q`. -/
lemma log_pow_le {q : ℝ} (hq : 0 < q) (n : ℕ) : Real.log (q ^ n) ≤ n * q := by
  rw [Real.log_pow]
  have := Real.log_le_sub_one_of_pos hq
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

/-- For `y ≥ 10¹⁰`, `ψ(y) ≤ 1.0026 y`. -/
lemma psi_le_large (hRH : RiemannHypothesis) (hR : RosserZeroCount) {y : ℝ} (hy : 10 ^ 10 ≤ y) :
    ψ y ≤ 1.0026 * y := by
  have hp := Real.pi_gt_d4
  have h := (abs_le.mp (psi_explicit hRH hR hy)).2
  have hy0 : 0 < y := by linarith
  set u := Real.log y
  have hu0 : 33 * 0.6931471803 ≤ u := by
    have h1 := Real.log_le_log (by norm_num) (show (2 : ℝ) ^ 33 ≤ y by norm_num; linarith)
    rw [Real.log_pow] at h1; push_cast at h1
    linarith [log_two_bounds.1]
  -- `q = y^{1/16}`
  set q := √(√(√(√y))) with hq
  have hq0 : 0 < q := by positivity
  have hq16 : q ^ 16 = y := by
    have h1 : √y ^ 2 = y := Real.sq_sqrt hy0.le
    have h2 : √(√y) ^ 2 = √y := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h3 : √(√(√y)) ^ 2 = √(√y) := Real.sq_sqrt (Real.sqrt_nonneg _)
    have h4 : q ^ 2 = √(√(√y)) := Real.sq_sqrt (Real.sqrt_nonneg _)
    calc q ^ 16 = (((q ^ 2) ^ 2) ^ 2) ^ 2 := by ring
      _ = y := by rw [h4, h3, h2, h1]
  have hsy : √y = q ^ 8 := by
    rw [← hq16, show q ^ 16 = (q ^ 8) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hq4 : 4.2 ≤ q := by
    by_contra hc; push Not at hc
    have : q ^ 16 < 4.2 ^ 16 := pow_lt_pow_left₀ hc hq0.le (by norm_num)
    rw [hq16] at this; norm_num at this; linarith
  have hlu : u ≤ 16 * q := by
    have := log_pow_le hq0 16; rw [hq16] at this; push_cast at this; exact this
  have hlu0 : 0 ≤ u := by linarith
  have hneg : -0.2985 * u + 4.62 ≤ 0 := by linarith
  have hu2 : u ^ 2 ≤ 256 * q ^ 2 := by nlinarith
  have h8 : u ^ 2 / (8 * π) ≤ u ^ 2 / 25.13 :=
    div_le_div_of_nonneg_left (sq_nonneg u) (by norm_num) (by linarith)
  have hkey : √y * (u ^ 2 / (8 * π) - 0.2985 * u + 4.62) ≤ 0.0026 * y := by
    rw [hsy, ← hq16]
    have hq8 : 0 < q ^ 8 := by positivity
    have e1 : q ^ 8 * (u ^ 2 / (8 * π) - 0.2985 * u + 4.62) ≤ q ^ 8 * (u ^ 2 / 25.13) :=
      mul_le_mul_of_nonneg_left (by linarith) hq8.le
    have e2 : q ^ 8 * (u ^ 2 / 25.13) ≤ q ^ 8 * (256 * q ^ 2 / 25.13) :=
      mul_le_mul_of_nonneg_left (by gcongr) hq8.le
    have e3 : q ^ 8 * (256 * q ^ 2 / 25.13) ≤ 0.0026 * q ^ 16 := by
      have : 256 / 25.13 ≤ 0.0026 * q ^ 6 := by
        have : (4.2 : ℝ) ^ 6 ≤ q ^ 6 := pow_le_pow_left₀ (by norm_num) hq4 6
        nlinarith
      have e : q ^ 8 * (256 * q ^ 2 / 25.13) = q ^ 10 * (256 / 25.13) := by ring
      rw [e, show (0.0026 : ℝ) * q ^ 16 = q ^ 10 * (0.0026 * q ^ 6) by ring]
      exact mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  linarith

/-- `ψ(y) ≤ y + 0.8√y` on `[1500, 10¹⁰]` (PsiCert). -/
lemma psi_le_cert (hC : PsiCert) {y : ℝ} (h1 : 1500 ≤ y) (h2 : y ≤ 10 ^ 10) :
    ψ y ≤ y + 0.8 * √y := by
  have := (abs_le.mp (hC y h1 h2)).2; linarith

/-- `ψ(y) ≤ (1 + c) y` once PsiCert's `0.8/√y ≤ c` and `c ≥ 0.0026`. -/
lemma psi_le_ratio (hRH : RiemannHypothesis) (hR : RosserZeroCount) (hC : PsiCert) {y c : ℝ}
    (hy : 1500 ≤ y) (hc : 0.0026 ≤ c) (hcy : 0.8 ≤ c * √y) : ψ y ≤ (1 + c) * y := by
  rcases le_or_gt y (10 ^ 10) with h | h
  · have := psi_le_cert hC hy h
    have hsy : √y * √y = y := Real.mul_self_sqrt (by linarith)
    have h3 := mul_le_mul_of_nonneg_right hcy (Real.sqrt_nonneg y)
    have : c * √y * √y = c * y := by rw [mul_assoc, hsy]
    linarith
  · have := psi_le_large hRH hR h.le
    nlinarith

/-- **`|θ(x) − x| ≤ √x (u²/(8π) − 0.2985 u + 5.667)` for `x ≥ 10¹⁰`.** -/
theorem theta_explicit (hRH : RiemannHypothesis) (hR : RosserZeroCount) (hC : PsiCert) {x : ℝ}
    (hx : 10 ^ 10 ≤ x) :
    |θ x - x| ≤ √x * (Real.log x ^ 2 / (8 * π) - 0.2985 * Real.log x + 5.667) := by
  have hx0 : 0 ≤ x := by linarith
  have hψ := abs_le.mp (psi_explicit hRH hR hx)
  have h1 := theta_le_psi x
  have hCP := psi_sub_theta_le_psi_add_psi_add_psi x
  have h53 : ψ (x ^ (5 : ℝ)⁻¹) ≤ ψ (x ^ (3 : ℝ)⁻¹) :=
    psi_mono (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  obtain ⟨a, ha0, hxa, h2, h3⟩ := twelfth_root hx0
  rw [h2, h3] at hCP
  rw [h3] at h53
  have hsx : √x = a ^ 6 := by
    rw [hxa, show a ^ 12 = (a ^ 6) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have ha2 : 46.41 ≤ a ^ 2 := by
    by_contra hc; push Not at hc
    have : (a ^ 2) ^ 6 < 46.41 ^ 6 := pow_lt_pow_left₀ hc (by positivity) (by norm_num)
    rw [← pow_mul] at this; norm_num at this; linarith
  have ha6 : 100000 ≤ a ^ 6 := by
    by_contra hc; push Not at hc
    have : (a ^ 6) ^ 2 < 100000 ^ 2 := pow_lt_pow_left₀ hc (by positivity) (by norm_num)
    rw [← pow_mul] at this; norm_num at this; linarith
  have ha4 : 2153 ≤ a ^ 4 := by
    have : (46.41 : ℝ) ^ 2 ≤ (a ^ 2) ^ 2 := pow_le_pow_left₀ (by norm_num) ha2 2
    rw [← pow_mul] at this; norm_num at this; linarith
  have hsa6 : √(a ^ 6) = a ^ 3 := by
    rw [show a ^ 6 = (a ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hsa4 : √(a ^ 4) = a ^ 2 := by
    rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have ha3 : 316 ≤ a ^ 3 := by
    by_contra hc; push Not at hc
    have : (a ^ 3) ^ 2 < 316 ^ 2 := pow_lt_pow_left₀ hc (by positivity) (by norm_num)
    rw [← pow_mul] at this; norm_num at this; linarith
  have hp6 : ψ (a ^ 6) ≤ (1 + 0.0026) * a ^ 6 :=
    psi_le_ratio hRH hR hC (by linarith) le_rfl (by rw [hsa6]; linarith)
  have hp4 : ψ (a ^ 4) ≤ (1 + 0.0173) * a ^ 4 :=
    psi_le_ratio hRH hR hC (by linarith) (by norm_num) (by rw [hsa4]; linarith)
  have hz : a ^ 4 ≤ 0.02155 * a ^ 6 := by
    have : a ^ 6 = a ^ 4 * a ^ 2 := by ring
    rw [this]; nlinarith [pow_nonneg ha0 4]
  have hD : ψ x - θ x ≤ 1.047 * √x := by rw [hsx]; linarith
  rw [abs_le]
  have e : √x * (Real.log x ^ 2 / (8 * π) - 0.2985 * Real.log x + 5.667)
      = √x * (Real.log x ^ 2 / (8 * π) - 0.2985 * Real.log x + 4.62) + 1.047 * √x := by ring
  rw [e]
  have hs0 : 0 ≤ √x := Real.sqrt_nonneg x
  constructor <;> nlinarith [hψ.1, hψ.2]

/-- **`|θ(x) − x| < √x log² x/(8π)` for `x ≥ 10¹⁰`.** -/
theorem theta_sharp_large (hRH : RiemannHypothesis) (hR : RosserZeroCount) (hC : PsiCert)
    {x : ℝ} (hx : 10 ^ 10 ≤ x) : |θ x - x| < 1 / (8 * π) * (√x * Real.log x ^ 2) := by
  have h := theta_explicit hRH hR hC hx
  have hu0 : 33 * 0.6931471803 ≤ Real.log x := by
    have h1 := Real.log_le_log (by norm_num) (show (2 : ℝ) ^ 33 ≤ x by norm_num; linarith)
    rw [Real.log_pow] at h1; push_cast at h1
    linarith [log_two_bounds.1]
  have hs : 0 < √x := Real.sqrt_pos.mpr (by linarith)
  have : √x * (Real.log x ^ 2 / (8 * π) - 0.2985 * Real.log x + 5.667)
      < 1 / (8 * π) * (√x * Real.log x ^ 2) := by
    have e : 1 / (8 * π) * (√x * Real.log x ^ 2) = √x * (Real.log x ^ 2 / (8 * π)) := by ring
    rw [e]
    apply mul_lt_mul_of_pos_left _ hs
    linarith
  linarith

/-- `|θ(x) − x| ≤ 3.9252 √x` for `3·10⁴ ≤ x ≤ 10¹⁰`, from PsiCert. -/
theorem theta_mid_abs (hC : PsiCert) {x : ℝ} (hx1 : 30000 ≤ x) (hx2 : x ≤ 10 ^ 10) :
    |θ x - x| ≤ 3.9252 * √x := by
  have hx0 : 0 ≤ x := by linarith
  have hψ := abs_le.mp (hC x (by linarith) hx2)
  have h1 := theta_le_psi x
  have hCP := psi_sub_theta_le_psi_add_psi_add_psi x
  have h53 : ψ (x ^ (5 : ℝ)⁻¹) ≤ ψ (x ^ (3 : ℝ)⁻¹) :=
    psi_mono (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  obtain ⟨a, ha0, hxa, h2, h3⟩ := twelfth_root hx0
  rw [h2, h3] at hCP
  rw [h3] at h53
  have hsx : √x = a ^ 6 := by
    rw [hxa, show a ^ 12 = (a ^ 6) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have ha : 2.36 ≤ a := by
    by_contra hc; push Not at hc
    have : a ^ 12 < 2.36 ^ 12 := pow_lt_pow_left₀ hc ha0 (by norm_num)
    norm_num at this; linarith
  have ha1 : 1 ≤ a := by linarith
  set ℓ := Real.log a with hℓ
  have hL : Real.log x = 12 * ℓ := by rw [hxa, Real.log_pow]; push_cast; ring
  have hℓlo : 0.8456 ≤ ℓ := by
    have e : Real.log 2.36 = Real.log 2 + Real.log 1.18 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1.18 by norm_num)
    have h2 := Real.log_le_log (by norm_num) ha
    have := log_two_bounds.1
    rw [e, ← hℓ] at h2
    have : (0.1525 : ℝ) ≤ 1 - (1.18 : ℝ)⁻¹ := by norm_num
    linarith
  have hℓhi : ℓ ≤ a / 2.718 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < a / Real.exp 1 by positivity)
    rw [Real.log_div (by linarith) (Real.exp_pos 1).ne', Real.log_exp] at h1
    have : a / Real.exp 1 ≤ a / 2.718 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith [Real.exp_one_gt_d9])
    linarith
  have hl4 : Real.log 4 ≤ 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
    linarith [Real.log_two_lt_d9]
  have hp6 := psi_le (x := a ^ 6) (one_le_pow₀ ha1)
  have hp4 := psi_le (x := a ^ 4) (one_le_pow₀ ha1)
  rw [show a ^ 6 = (a ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.log_pow] at hp6
  rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.log_pow] at hp4
  rw [show (a ^ 3) ^ 2 = a ^ 6 by ring] at hp6
  rw [show (a ^ 2) ^ 2 = a ^ 4 by ring] at hp4
  rw [Real.log_pow] at hp6 hp4
  push_cast at hp6 hp4
  rw [← hℓ] at hp6 hp4
  have ha2 : 5.5696 ≤ a ^ 2 := by nlinarith
  have ha3 : 13.144 ≤ a ^ 3 := by nlinarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  -- each lower-order term against `a⁶`
  have h42 : a ^ 4 * 5.5696 ≤ a ^ 6 := by
    have := mul_le_mul_of_nonneg_left ha2 (pow_nonneg ha0 4)
    have e : a ^ 4 * a ^ 2 = a ^ 6 := by ring
    linarith
  have h33 : a ^ 3 * 13.144 ≤ a ^ 6 := by
    have := mul_le_mul_of_nonneg_left ha3 (pow_nonneg ha0 3)
    have e : a ^ 3 * a ^ 3 = a ^ 6 := by ring
    linarith
  have e1 : 2 * a ^ 3 * (6 * ℓ) ≤ 0.793 * a ^ 6 := by
    have s1 := mul_le_mul_of_nonneg_left hℓhi (pow_nonneg ha0 3)
    have e : a ^ 3 * (a / 2.718) = a ^ 4 / 2.718 := by ring
    have e' : 2 * a ^ 3 * (6 * ℓ) = 12 * (a ^ 3 * ℓ) := by ring
    rw [e'] at ⊢; rw [e] at s1
    have h6 := pow_nonneg ha0 6
    have h42' := h42
    norm_num at s1 h42' ⊢
    linarith
  have e2 : 2 * (Real.log 4 * a ^ 4) ≤ 0.4979 * a ^ 6 := by
    have := mul_le_mul_of_nonneg_right hl4 (pow_nonneg ha0 4)
    have := pow_nonneg ha0 6
    linarith
  have e3 : 2 * (2 * a ^ 2 * (4 * ℓ)) ≤ 0.448 * a ^ 6 := by
    have s1 := mul_le_mul_of_nonneg_left hℓhi (pow_nonneg ha0 2)
    have e : a ^ 2 * (a / 2.718) = a ^ 3 / 2.718 := by ring
    have e' : 2 * (2 * a ^ 2 * (4 * ℓ)) = 16 * (a ^ 2 * ℓ) := by ring
    rw [e']; rw [e] at s1
    have h6 := pow_nonneg ha0 6
    have h33' := h33
    norm_num at s1 h33' ⊢
    linarith
  have hD : ψ x - θ x ≤ (1.3863 + 0.793 + 0.4979 + 0.448) * a ^ 6 := by
    have := mul_le_mul_of_nonneg_right hl4 (pow_nonneg ha0 6)
    linarith
  rw [hsx]
  rw [hsx] at hψ
  rw [abs_le]
  have ha6 : 0 ≤ a ^ 6 := by positivity
  constructor <;> linarith [hψ.1, hψ.2]

/-- **`|θ(x) − x| < √x log² x/(8π)` for `3·10⁴ ≤ x ≤ 10¹⁰`**, from PsiCert. -/
theorem theta_mid (hC : PsiCert) {x : ℝ} (hx1 : 30000 ≤ x) (hx2 : x ≤ 10 ^ 10) :
    |θ x - x| < 1 / (8 * π) * (√x * Real.log x ^ 2) := by
  have hx0 : 0 ≤ x := by linarith
  have hψ := abs_le.mp (hC x (by linarith) hx2)
  have h1 := theta_le_psi x
  have hCP := psi_sub_theta_le_psi_add_psi_add_psi x
  have h53 : ψ (x ^ (5 : ℝ)⁻¹) ≤ ψ (x ^ (3 : ℝ)⁻¹) :=
    psi_mono (Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num))
  obtain ⟨a, ha0, hxa, h2, h3⟩ := twelfth_root hx0
  rw [h2, h3] at hCP
  rw [h3] at h53
  have hsx : √x = a ^ 6 := by
    rw [hxa, show a ^ 12 = (a ^ 6) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have ha : 2.36 ≤ a := by
    by_contra hc; push Not at hc
    have : a ^ 12 < 2.36 ^ 12 := pow_lt_pow_left₀ hc ha0 (by norm_num)
    norm_num at this; linarith
  have ha1 : 1 ≤ a := by linarith
  set ℓ := Real.log a with hℓ
  have hL : Real.log x = 12 * ℓ := by rw [hxa, Real.log_pow]; push_cast; ring
  have hℓlo : 0.8456 ≤ ℓ := by
    have e : Real.log 2.36 = Real.log 2 + Real.log 1.18 := by
      rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
    have h1 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1.18 by norm_num)
    have h2 := Real.log_le_log (by norm_num) ha
    have := log_two_bounds.1
    rw [e, ← hℓ] at h2
    have : (0.1525 : ℝ) ≤ 1 - (1.18 : ℝ)⁻¹ := by norm_num
    linarith
  have hℓhi : ℓ ≤ a / 2.718 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < a / Real.exp 1 by positivity)
    rw [Real.log_div (by linarith) (Real.exp_pos 1).ne', Real.log_exp] at h1
    have : a / Real.exp 1 ≤ a / 2.718 :=
      div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith [Real.exp_one_gt_d9])
    linarith
  have hl4 : Real.log 4 ≤ 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
    linarith [Real.log_two_lt_d9]
  have hp6 := psi_le (x := a ^ 6) (one_le_pow₀ ha1)
  have hp4 := psi_le (x := a ^ 4) (one_le_pow₀ ha1)
  rw [show a ^ 6 = (a ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.log_pow] at hp6
  rw [show a ^ 4 = (a ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity), Real.log_pow] at hp4
  rw [show (a ^ 3) ^ 2 = a ^ 6 by ring] at hp6
  rw [show (a ^ 2) ^ 2 = a ^ 4 by ring] at hp4
  rw [Real.log_pow] at hp6 hp4
  push_cast at hp6 hp4
  rw [← hℓ] at hp6 hp4
  have ha2 : 5.5696 ≤ a ^ 2 := by nlinarith
  have ha3 : 13.144 ≤ a ^ 3 := by nlinarith
  have hℓ0 : 0 ≤ ℓ := by linarith
  -- each lower-order term against `a⁶`
  have h42 : a ^ 4 * 5.5696 ≤ a ^ 6 := by
    have := mul_le_mul_of_nonneg_left ha2 (pow_nonneg ha0 4)
    have e : a ^ 4 * a ^ 2 = a ^ 6 := by ring
    linarith
  have h33 : a ^ 3 * 13.144 ≤ a ^ 6 := by
    have := mul_le_mul_of_nonneg_left ha3 (pow_nonneg ha0 3)
    have e : a ^ 3 * a ^ 3 = a ^ 6 := by ring
    linarith
  have e1 : 2 * a ^ 3 * (6 * ℓ) ≤ 0.793 * a ^ 6 := by
    have s1 := mul_le_mul_of_nonneg_left hℓhi (pow_nonneg ha0 3)
    have e : a ^ 3 * (a / 2.718) = a ^ 4 / 2.718 := by ring
    have e' : 2 * a ^ 3 * (6 * ℓ) = 12 * (a ^ 3 * ℓ) := by ring
    rw [e'] at ⊢; rw [e] at s1
    have h6 := pow_nonneg ha0 6
    have h42' := h42
    norm_num at s1 h42' ⊢
    linarith
  have e2 : 2 * (Real.log 4 * a ^ 4) ≤ 0.4979 * a ^ 6 := by
    have := mul_le_mul_of_nonneg_right hl4 (pow_nonneg ha0 4)
    have := pow_nonneg ha0 6
    linarith
  have e3 : 2 * (2 * a ^ 2 * (4 * ℓ)) ≤ 0.448 * a ^ 6 := by
    have s1 := mul_le_mul_of_nonneg_left hℓhi (pow_nonneg ha0 2)
    have e : a ^ 2 * (a / 2.718) = a ^ 3 / 2.718 := by ring
    have e' : 2 * (2 * a ^ 2 * (4 * ℓ)) = 16 * (a ^ 2 * ℓ) := by ring
    rw [e']; rw [e] at s1
    have h6 := pow_nonneg ha0 6
    have h33' := h33
    norm_num at s1 h33' ⊢
    linarith
  have hD : ψ x - θ x ≤ (1.3863 + 0.793 + 0.4979 + 0.448) * a ^ 6 := by
    have := mul_le_mul_of_nonneg_right hl4 (pow_nonneg ha0 6)
    linarith
  -- the target
  have hp' := Real.pi_lt_d4
  have hT : (0.8 + 1.3863 + 0.793 + 0.4979 + 0.448) * a ^ 6
      < 1 / (8 * π) * (a ^ 6 * (12 * ℓ) ^ 2) := by
    have hπ : 1 / (8 * π) * (a ^ 6 * (12 * ℓ) ^ 2) = a ^ 6 * (144 * ℓ ^ 2 / (8 * π)) := by ring
    rw [hπ, mul_comm]
    have ha6 : 0 < a ^ 6 := by positivity
    apply mul_lt_mul_of_pos_left _ ha6
    rw [lt_div_iff₀ (by positivity)]
    have : 0.8456 ^ 2 ≤ ℓ ^ 2 := pow_le_pow_left₀ (by norm_num) hℓlo 2
    nlinarith
  rw [hsx, hL]
  rw [hsx] at hψ
  rw [abs_lt]
  have ha6 : 0 ≤ a ^ 6 := by positivity
  constructor <;> linarith [hψ.1, hψ.2]

end Schoenfeld
