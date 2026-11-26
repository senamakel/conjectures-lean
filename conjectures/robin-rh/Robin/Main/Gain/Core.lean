import Robin.Main.Gain.Integrals
import Robin.Main.Gain.Errors
import Robin.Main.Gain.Y
import Robin.Main.Gain.Abel

/-!
# The gain bound for an abstract `Ψ₁`

`gain_bound_of` proves the gain bound for any continuous `P` with right derivative `ψ` and
`|P t − t²/2| ≤ t^{3/2}/20 + 4t` for `t ≥ 16`: gain `≥ ∫_Y^x θ v = ∫ t v + ∫ (ψ − t) v − ∫ (ψ − θ) v`,
and the three integrals are bounded in `Integrals.lean` and `Errors.lean`.
-/

namespace Robin.Gain

open Real Chebyshev

theorem gain_bound_of (P : ℝ → ℝ) (hPc : Continuous P)
    (hPd : ∀ t, HasDerivWithinAt P (ψ t) (Set.Ioi t) t)
    (hPb : ∀ t : ℝ, 16 ≤ t → |P t - t ^ 2 / 2| ≤ t ^ ((3 : ℝ) / 2) / 20 + 4 * t)
    {x : ℝ} (hx : Real.exp 30 ≤ x) :
    (2.67 - 60 * x ^ (-(1 : ℝ) / 4)) / (√x * Real.log x) ≤ gainSum x := by
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 30) hx
  have hL : 30 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hbig : (10 : ℝ) ^ 12 ≤ x := by
    calc (10 : ℝ) ^ 12 ≤ 2.7182818283 ^ 30 := by norm_num
      _ ≤ Real.exp 1 ^ 30 := pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 30
      _ = Real.exp 30 := by rw [Real.exp_one_pow]; norm_num
      _ ≤ x := hx
  have hsx : (10 : ℝ) ^ 6 ≤ √x := (Real.le_sqrt (by norm_num) hx0.le).2 (by nlinarith)
  obtain ⟨Y, hYs, hYx, hYeq, hlY, hlY2, hr⟩ := exists_Y hx
  have hY6 : (10 : ℝ) ^ 6 ≤ Y := hsx.trans hYs
  have hY1 : 1 < Y := by linarith
  have hY0 : 0 < Y := by linarith
  have heps : 0 < epsR x := by
    unfold epsR
    apply div_pos (Real.log_pos _) (by linarith)
    have : 0 < 1 / x := by positivity
    linarith
  have hG := gain_ge_integral hY1 hYx hYeq heps
  -- integrability
  have hsub : Set.uIcc Y x ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hYx]; intro t ht; exact lt_of_lt_of_le hY1 ht.1
  have hv : ContinuousOn vW (Set.uIcc Y x) := continuousOn_vW.mono hsub
  have hψ : IntervalIntegrable ψ MeasureTheory.volume Y x := psi_mono.intervalIntegrable
  have hθ : IntervalIntegrable θ MeasureTheory.volume Y x := theta_mono.intervalIntegrable
  have hid : IntervalIntegrable (fun t : ℝ => t) MeasureTheory.volume Y x :=
    intervalIntegral.intervalIntegrable_id
  have i1 : IntervalIntegrable (fun t => t * vW t) MeasureTheory.volume Y x :=
    hid.mul_continuousOn hv
  have i2 : IntervalIntegrable (fun t => (ψ t - t) * vW t) MeasureTheory.volume Y x :=
    (hψ.sub hid).mul_continuousOn hv
  have i3 : IntervalIntegrable (fun t => (ψ t - θ t) * vW t) MeasureTheory.volume Y x :=
    (hψ.sub hθ).mul_continuousOn hv
  have hsplit : ∫ t in Y..x, θ t * vW t = (∫ t in Y..x, t * vW t) +
      (∫ t in Y..x, (ψ t - t) * vW t) - ∫ t in Y..x, (ψ t - θ t) * vW t := by
    rw [← intervalIntegral.integral_add i1 i2, ← intervalIntegral.integral_sub (i1.add i2) i3]
    apply intervalIntegral.integral_congr
    intro t _
    ring
  have hM := main_integral hY1 hYx hL hlY
  have hE1 := (abs_le.mp (psi_t_integral P hPc hPd hPb hY6 hYx hL hlY)).1
  have hE2 := psi_theta_integral hY1 hYx hL hlY
  -- name the pieces
  set L := Real.log x with hLdef
  set lY := Real.log Y with hlYdef
  set a := √x with hadef
  set w := Y ^ (-(3 : ℝ) / 2) with hwdef
  set s := x ^ (-(1 : ℝ) / 4) with hsdef
  set k := 1 + L / (L + 2) with hkdef
  set M := (1 / (Y * lY) - 1 / (x * L)) * k with hMdef
  have hL0 : 0 < L := by linarith
  have hlY0 : 0 < lY := by linarith
  have ha : 0 < a := by linarith
  have hax : a ^ 2 = x := Real.sq_sqrt hx0.le
  have hgain : M - 46 / L * w ≤ gainSum x := by
    have : M - 46 / L * w = M - 1 / L * w - 45 / L * w := by ring
    rw [this]
    have := hsplit ▸ hG
    linarith
  -- rpow facts
  have hs_eq : a ^ (-(1 : ℝ) / 2) = s := by
    rw [hadef, Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]; norm_num [hsdef]
  have hs0 : 0 ≤ s := by rw [hsdef]; positivity
  have haw : a * w ≤ s := by
    have h1 : w ≤ a ^ (-(3 : ℝ) / 2) := Real.rpow_le_rpow_of_nonpos ha hYs (by norm_num)
    have h2 : a * a ^ (-(3 : ℝ) / 2) = a ^ (-(1 : ℝ) / 2) := by
      conv_lhs => arg 1; rw [← Real.rpow_one a]
      rw [← Real.rpow_add ha]; norm_num
    calc a * w ≤ a * a ^ (-(3 : ℝ) / 2) := mul_le_mul_of_nonneg_left h1 ha.le
      _ = s := by rw [h2, hs_eq]
  have hinv : 1 / a ≤ s := by
    rw [← hs_eq, one_div, ← Real.rpow_neg_one]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  -- main term
  have hq : 2 * L / (L + 0.6933) ≤ L / lY := by
    rw [div_le_div_iff₀ (by linarith) hlY0]; nlinarith
  have hk1 : 0 ≤ k := by rw [hkdef]; positivity
  have hk2 : k ≤ 2 := by
    rw [hkdef]; have : L / (L + 2) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    linarith
  have hqk : 3.776 ≤ L / lY * k := by
    have e : 2 * L / (L + 0.6933) * k = 2 * L * (2 * L + 2) / ((L + 0.6933) * (L + 2)) := by
      rw [hkdef]; field_simp; ring
    have : 3.776 ≤ 2 * L / (L + 0.6933) * k := by
      rw [e, le_div_iff₀ (by positivity)]; nlinarith
    exact this.trans (mul_le_mul_of_nonneg_right hq hk1)
  have hmain : 2.67 - 2 * s ≤ a * L * M := by
    have e : a * L * M = a / Y * (L / lY * k) - 1 / a * k := by
      rw [hMdef, ← hax]; field_simp
    rw [e]
    have h1 : 2.67 ≤ a / Y * (L / lY * k) := by
      calc (2.67 : ℝ) ≤ 0.7071 * 3.776 := by norm_num
        _ ≤ a / Y * (L / lY * k) := mul_le_mul hr hqk (by norm_num) (by positivity)
    have h2 : 1 / a * k ≤ 2 * s := by
      calc 1 / a * k ≤ s * 2 := mul_le_mul hinv hk2 hk1 hs0
        _ = 2 * s := by ring
    linarith
  -- conclude
  rw [div_le_iff₀ (by positivity)]
  have e : (M - 46 / L * w) * (a * L) = a * L * M - 46 * (a * w) := by field_simp
  have h3 : (M - 46 / L * w) * (a * L) ≤ gainSum x * (a * L) :=
    mul_le_mul_of_nonneg_right hgain (by positivity)
  rw [e] at h3
  linarith

end Robin.Gain
