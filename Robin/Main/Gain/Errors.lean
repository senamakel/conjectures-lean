import Robin.Main.Gain.Basic

/-! # Error integrals `∫ (ψ − t) v` and `∫ (ψ − θ) v` -/

namespace Robin.Gain

open Real Chebyshev

theorem integral_rpow_le {x Y : ℝ} (hY : 0 < Y) (hYx : Y ≤ x) :
    ∫ t in Y..x, t ^ (-(5 : ℝ) / 2) ≤ 2 / 3 * Y ^ (-(3 : ℝ) / 2) := by
  have h0 : (0 : ℝ) ∉ Set.uIcc Y x := by
    rw [Set.uIcc_of_le hYx]; intro h; exact absurd h.1 (not_le.mpr hY)
  rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
  have hx : 0 < x := lt_of_lt_of_le hY hYx
  have e : (-(5 : ℝ) / 2 + 1) = -(3 : ℝ) / 2 := by norm_num
  rw [e]
  have := Real.rpow_nonneg hx.le (-(3 : ℝ) / 2)
  have h2 : (x ^ (-(3 : ℝ) / 2) - Y ^ (-(3 : ℝ) / 2)) / (-(3 : ℝ) / 2)
      = 2 / 3 * Y ^ (-(3 : ℝ) / 2) - 2 / 3 * x ^ (-(3 : ℝ) / 2) := by ring
  rw [h2]; linarith

theorem psi_theta_integral {x Y : ℝ} (hY1 : 1 < Y) (hYx : Y ≤ x) (hL : 30 ≤ Real.log x)
    (hlY : Real.log x / 2 ≤ Real.log Y) :
    ∫ t in Y..x, (ψ t - θ t) * vW t ≤ 45 / Real.log x * Y ^ (-(3 : ℝ) / 2) := by
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hY0 : 0 < Y := by linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc Y x := by
    rw [Set.uIcc_of_le hYx]; intro h; exact absurd h.1 (not_le.mpr hY0)
  have hsub : Set.uIcc Y x ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hYx]; intro t ht; exact lt_of_lt_of_le hY1 ht.1
  have hint : IntervalIntegrable (fun t => (ψ t - θ t) * vW t) MeasureTheory.volume Y x :=
    (psi_mono.intervalIntegrable.sub theta_mono.intervalIntegrable).mul_continuousOn
      (continuousOn_vW.mono hsub)
  have hint2 : IntervalIntegrable (fun t => 67 / L * t ^ (-(5 : ℝ) / 2))
      MeasureTheory.volume Y x :=
    (intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).const_mul _
  have hlog4 : Real.log 4 < 1.3863 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith [Real.log_two_lt_d9]
  have hpt : ∀ t ∈ Set.Icc Y x, (ψ t - θ t) * vW t ≤ 67 / L * t ^ (-(5 : ℝ) / 2) := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hY1 ht.1
    have ht0 : 0 < t := by linarith
    have hlt : L / 2 ≤ Real.log t := le_trans hlY (Real.log_le_log hY0 ht.1)
    obtain ⟨hv0, hv1⟩ := vW_bounds ht1 hL hlt
    have hps : ∀ r : ℝ, 0 ≤ r → ψ (t ^ r) ≤ (Real.log 4 + 4) * t ^ r := fun r _ =>
      psi_le_const_mul_self (Real.rpow_nonneg ht0.le r)
    have e3 : t ^ (3 : ℝ)⁻¹ ≤ t ^ (2 : ℝ)⁻¹ :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by norm_num)
    have e5 : t ^ (5 : ℝ)⁻¹ ≤ t ^ (2 : ℝ)⁻¹ :=
      Real.rpow_le_rpow_of_exponent_le ht1.le (by norm_num)
    have hc : 0 < Real.log 4 + 4 := by positivity
    have hdiff : ψ t - θ t ≤ 16.16 * t ^ (2 : ℝ)⁻¹ := by
      have h := psi_sub_theta_le_psi_add_psi_add_psi t
      have h2 := hps (2 : ℝ)⁻¹ (by norm_num)
      have h3 := hps (3 : ℝ)⁻¹ (by norm_num)
      have h5 := hps (5 : ℝ)⁻¹ (by norm_num)
      have hs : 0 ≤ t ^ (2 : ℝ)⁻¹ := Real.rpow_nonneg ht0.le _
      nlinarith [mul_le_mul_of_nonneg_left e3 hc.le, mul_le_mul_of_nonneg_left e5 hc.le]
    have hd0 : 0 ≤ ψ t - θ t := sub_nonneg.mpr (theta_le_psi t)
    have hrp : t ^ (-(5 : ℝ) / 2) = t ^ (2 : ℝ)⁻¹ / t ^ (3 : ℕ) := by
      rw [← Real.rpow_sub_natCast ht0.ne']; norm_num
    have hs : 0 ≤ t ^ (2 : ℝ)⁻¹ := Real.rpow_nonneg ht0.le _
    calc (ψ t - θ t) * vW t ≤ (16.16 * t ^ (2 : ℝ)⁻¹) * (4.14 / (L * t ^ 3)) :=
          mul_le_mul hdiff hv1 hv0 (by positivity)
      _ = 66.9024 / L * (t ^ (2 : ℝ)⁻¹ / t ^ 3) := by field_simp; ring
      _ ≤ 67 / L * (t ^ (2 : ℝ)⁻¹ / t ^ 3) := by gcongr; norm_num
      _ = 67 / L * t ^ (-(5 : ℝ) / 2) := by rw [hrp]
  calc ∫ t in Y..x, (ψ t - θ t) * vW t ≤ ∫ t in Y..x, 67 / L * t ^ (-(5 : ℝ) / 2) :=
        intervalIntegral.integral_mono_on hYx hint hint2 hpt
    _ = 67 / L * ∫ t in Y..x, t ^ (-(5 : ℝ) / 2) := intervalIntegral.integral_const_mul _ _
    _ ≤ 67 / L * (2 / 3 * Y ^ (-(3 : ℝ) / 2)) := by
        gcongr; exact integral_rpow_le hY0 hYx
    _ ≤ 45 / L * Y ^ (-(3 : ℝ) / 2) := by
        have := Real.rpow_nonneg hY0.le (-(3 : ℝ) / 2)
        rw [← mul_assoc]; gcongr
        rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hL0]; norm_num

theorem psi_t_integral (P : ℝ → ℝ) (hPc : Continuous P)
    (hPd : ∀ t, HasDerivWithinAt P (ψ t) (Set.Ioi t) t)
    (hPb : ∀ t : ℝ, 16 ≤ t → |P t - t ^ 2 / 2| ≤ t ^ ((3 : ℝ) / 2) / 20 + 4 * t)
    {x Y : ℝ} (hY : 10 ^ 6 ≤ Y) (hYx : Y ≤ x) (hL : 30 ≤ Real.log x)
    (hlY : Real.log x / 2 ≤ Real.log Y) :
    |∫ t in Y..x, (ψ t - t) * vW t| ≤ 1 / Real.log x * Y ^ (-(3 : ℝ) / 2) := by
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hY0 : 0 < Y := by linarith
  have hY1 : 1 < Y := by linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc Y x := by
    rw [Set.uIcc_of_le hYx]; intro h; exact absurd h.1 (not_le.mpr hY0)
  have hsub : Set.uIcc Y x ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hYx]; intro t ht; exact lt_of_lt_of_le hY1 ht.1
  set E : ℝ → ℝ := fun t => P t - t ^ 2 / 2 with hEdef
  have hEc : Continuous E := hPc.sub (by fun_prop)
  have hvc : ContinuousOn vW (Set.uIcc Y x) := continuousOn_vW.mono hsub
  have hv'c : ContinuousOn vW' (Set.uIcc Y x) := continuousOn_vW'.mono hsub
  have hu'i : IntervalIntegrable (fun t => ψ t - t) MeasureTheory.volume Y x :=
    psi_mono.intervalIntegrable.sub (continuous_id.intervalIntegrable _ _)
  have hIBP := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    (u := E) (v := vW) (u' := fun t => ψ t - t) (v' := vW') hEc.continuousOn hvc
    (fun t _ => by
      have hq : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
        convert (hasDerivAt_pow 2 t).div_const 2 using 1; push_cast; ring
      exact (hPd t).sub hq.hasDerivWithinAt)
    (fun t ht => by
      have : 1 < t := by
        rw [min_eq_left hYx] at ht; exact lt_trans hY1 ht.1
      exact (hasDerivAt_vW this).hasDerivWithinAt)
    hu'i hv'c.intervalIntegrable
  have hI1 : IntervalIntegrable (fun t => (ψ t - t) * vW t) MeasureTheory.volume Y x :=
    hu'i.mul_continuousOn hvc
  have hI2 : IntervalIntegrable (fun t => E t * vW' t) MeasureTheory.volume Y x :=
    (hEc.continuousOn.mul hv'c).intervalIntegrable
  rw [intervalIntegral.integral_add hI1 hI2] at hIBP
  have hsplit : ∫ t in Y..x, (ψ t - t) * vW t
      = E x * vW x - E Y * vW Y - ∫ t in Y..x, E t * vW' t := by linarith
  -- pointwise bound on E
  have hE : ∀ t ∈ Set.Icc Y x, |E t| ≤ 0.054 * t ^ ((3 : ℝ) / 2) := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hr : t ^ ((3 : ℝ) / 2) = t * √t := by
      rw [show (3 : ℝ) / 2 = 1 + 1 / 2 by norm_num, Real.rpow_add ht0, Real.rpow_one,
        Real.sqrt_eq_rpow]
    have hsq : 1000 ≤ √t := (Real.le_sqrt (by norm_num) ht0.le).mpr (by nlinarith [ht.1])
    have := hPb t (by nlinarith [ht.1])
    rw [hr] at this ⊢
    have : 4 * t ≤ 0.004 * (t * √t) := by nlinarith
    show |P t - t ^ 2 / 2| ≤ _
    linarith
  have hbd : ∀ t ∈ Set.Icc Y x, |E t * vW t| ≤ 0.2236 / L * Y ^ (-(3 : ℝ) / 2) := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hY1 ht.1
    have ht0 : 0 < t := by linarith
    have hlt : L / 2 ≤ Real.log t := le_trans hlY (Real.log_le_log hY0 ht.1)
    obtain ⟨hv0, hv1⟩ := vW_bounds ht1 hL hlt
    have hrp : t ^ (-(3 : ℝ) / 2) = t ^ ((3 : ℝ) / 2) / t ^ (3 : ℕ) := by
      rw [← Real.rpow_sub_natCast ht0.ne']; norm_num
    have hmono : t ^ (-(3 : ℝ) / 2) ≤ Y ^ (-(3 : ℝ) / 2) :=
      Real.rpow_le_rpow_of_nonpos hY0 ht.1 (by norm_num)
    have hs : 0 ≤ t ^ ((3 : ℝ) / 2) := Real.rpow_nonneg ht0.le _
    rw [abs_mul, abs_of_nonneg hv0]
    calc |E t| * vW t ≤ (0.054 * t ^ ((3 : ℝ) / 2)) * (4.14 / (L * t ^ 3)) :=
          mul_le_mul (hE t ht) hv1 hv0 (by positivity)
      _ = 0.22356 / L * (t ^ ((3 : ℝ) / 2) / t ^ 3) := by field_simp; ring
      _ = 0.22356 / L * t ^ (-(3 : ℝ) / 2) := by rw [hrp]
      _ ≤ 0.2236 / L * Y ^ (-(3 : ℝ) / 2) := by
          gcongr
          norm_num
  have hpt : ∀ t ∈ Set.Icc Y x, |E t * vW' t| ≤ 0.702 / L * t ^ (-(5 : ℝ) / 2) := by
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hY1 ht.1
    have ht0 : 0 < t := by linarith
    have hlt : L / 2 ≤ Real.log t := le_trans hlY (Real.log_le_log hY0 ht.1)
    have hv1 := abs_vW'_le ht1 hL hlt
    have hrp : t ^ (-(5 : ℝ) / 2) = t ^ ((3 : ℝ) / 2) / t ^ (4 : ℕ) := by
      rw [← Real.rpow_sub_natCast ht0.ne']; norm_num
    have hs : 0 ≤ t ^ ((3 : ℝ) / 2) := Real.rpow_nonneg ht0.le _
    rw [abs_mul]
    calc |E t| * |vW' t| ≤ (0.054 * t ^ ((3 : ℝ) / 2)) * (13 / (L * t ^ 4)) :=
          mul_le_mul (hE t ht) hv1 (abs_nonneg _) (by positivity)
      _ = 0.702 / L * (t ^ ((3 : ℝ) / 2) / t ^ 4) := by field_simp; ring
      _ = 0.702 / L * t ^ (-(5 : ℝ) / 2) := by rw [hrp]
  have hint2 : IntervalIntegrable (fun t => 0.702 / L * t ^ (-(5 : ℝ) / 2))
      MeasureTheory.volume Y x :=
    (intervalIntegral.intervalIntegrable_rpow (Or.inr h0)).const_mul _
  have hJ : |∫ t in Y..x, E t * vW' t| ≤ 0.468 / L * Y ^ (-(3 : ℝ) / 2) := by
    calc |∫ t in Y..x, E t * vW' t| ≤ ∫ t in Y..x, |E t * vW' t| :=
          intervalIntegral.abs_integral_le_integral_abs hYx
      _ ≤ ∫ t in Y..x, 0.702 / L * t ^ (-(5 : ℝ) / 2) :=
          intervalIntegral.integral_mono_on hYx hI2.abs hint2 hpt
      _ = 0.702 / L * ∫ t in Y..x, t ^ (-(5 : ℝ) / 2) := intervalIntegral.integral_const_mul _ _
      _ ≤ 0.702 / L * (2 / 3 * Y ^ (-(3 : ℝ) / 2)) := by
          gcongr; exact integral_rpow_le hY0 hYx
      _ = 0.468 / L * Y ^ (-(3 : ℝ) / 2) := by ring
  have hbx := hbd x ⟨hYx, le_rfl⟩
  have hbY := hbd Y ⟨le_rfl, hYx⟩
  have hw := Real.rpow_nonneg hY0.le (-(3 : ℝ) / 2)
  rw [hsplit]
  calc |E x * vW x - E Y * vW Y - ∫ t in Y..x, E t * vW' t|
      ≤ |E x * vW x| + |E Y * vW Y| + |∫ t in Y..x, E t * vW' t| := by
        have := abs_sub (E x * vW x - E Y * vW Y) (∫ t in Y..x, E t * vW' t)
        have := abs_sub (E x * vW x) (E Y * vW Y)
        linarith
    _ ≤ 0.2236 / L * Y ^ (-(3 : ℝ) / 2) + 0.2236 / L * Y ^ (-(3 : ℝ) / 2)
        + 0.468 / L * Y ^ (-(3 : ℝ) / 2) := by linarith
    _ = 0.9152 / L * Y ^ (-(3 : ℝ) / 2) := by ring
    _ ≤ 1 / L * Y ^ (-(3 : ℝ) / 2) := by gcongr; norm_num

end Robin.Gain
