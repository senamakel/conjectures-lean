import Schoenfeld.Theta

/-!
# `|π(x) − li(x)| < (9/20) √x log x` for `x ≥ 2657`, under RH

Partial summation (Mathlib's `Chebyshev.primeCounting_eq_theta_div_log_add_integral`) and
`li(x) = li(2) + x/log x − 2/log 2 + ∫₂ˣ dt/log² t` (integration by parts, `logIntegral_eq`):

`π(x) − li(x) = (θ(x) − x)/log x + ∫₂ˣ (θ(t) − t)/(t log² t) dt + 2/log 2 − li(2)`.

* `(θ(x) − x)/log x`: `< √x log x / 4` (`theta_sub_lt_quarter`);
* `∫₂^599`: `|θ(t) − t| ≤ t`, so the integrand is `≤ 1/log² t`; nine dyadic pieces give `≤ 33`;
* `∫_599^x`: the integrand is `≤ (1/4)/√t`, integral `≤ √x/2`;
* `0 ≤ li(2) ≤ 2` (formal-conjectures' integrand bounds), so `|2/log 2 − li(2)| ≤ 2.886`.
-/

namespace Schoenfeld

open Real Chebyshev MeasureTheory

lemma logIntegralTwo_nonneg : 0 ≤ logIntegralTwo := by
  have := Real.logIntegral_two_pos; rw [Real.logIntegral_two] at this; exact this.le

lemma logIntegralTwo_le_two : logIntegralTwo ≤ 2 := by
  unfold logIntegralTwo
  calc ∫ u in Set.Ioo (0 : ℝ) 1, (1 / Real.log (1 + u) + 1 / Real.log (1 - u))
      ≤ ∫ u in Set.Ioo (0 : ℝ) 1, (2 : ℝ) :=
        setIntegral_mono_on Real.logIntegralTwo_integrand_integrableOn
          (integrableOn_const (hs := by simp) (hC := by simp)) measurableSet_Ioo
          (fun u hu => Real.logIntegralTwo_integrand_le_two hu.1 hu.2)
    _ = 2 := by simp

lemma log_pos_of_two_le {t : ℝ} (ht : 2 ≤ t) : 0 < Real.log t := Real.log_pos (by linarith)

lemma continuousOn_inv_log {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (n : ℕ) :
    ContinuousOn (fun t : ℝ => 1 / Real.log t ^ n) (Set.uIcc a b) := by
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  have ht0 : t ≠ 0 := by linarith [ht.1]
  have hl : Real.log t ^ n ≠ 0 := pow_ne_zero _ (log_pos_of_two_le (by linarith [ht.1])).ne'
  exact (continuousAt_const.div ((Real.continuousAt_log ht0).pow n) hl).continuousWithinAt

/-- Integration by parts: `li(x) = li(2) + x/log x − 2/log 2 + ∫₂ˣ dt/log² t`. -/
theorem logIntegral_eq {x : ℝ} (hx : 2 ≤ x) :
    logIntegral x = logIntegralTwo + x / Real.log x - 2 / Real.log 2
      + ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 := by
  have i1 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 1) volume 2 x :=
    (continuousOn_inv_log le_rfl hx 1).intervalIntegrable
  have i2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x :=
    (continuousOn_inv_log le_rfl hx 2).intervalIntegrable
  have hFTC : ∫ t in (2 : ℝ)..x, (1 / Real.log t ^ 1 - 1 / Real.log t ^ 2)
      = x / Real.log x - 2 / Real.log 2 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => t / Real.log t)
      (fun t ht => ?_) (i1.sub i2)
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl := (log_pos_of_two_le ht.1).ne'
    have := (hasDerivAt_id' t).div (Real.hasDerivAt_log ht0) hl
    convert this using 1
    field_simp
  rw [intervalIntegral.integral_sub i1 i2] at hFTC
  simp only [pow_one] at hFTC
  unfold logIntegral
  linarith

/-- `g(t) = θ(t)/(t log² t) − 1/log² t = (θ(t) − t)/(t log² t)`. -/
noncomputable def gfun (t : ℝ) : ℝ := θ t / (t * Real.log t ^ 2) - 1 / Real.log t ^ 2

lemma intervalIntegrable_gfun {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable gfun volume a b := by
  have h1 : IntervalIntegrable (fun t => θ t / (t * Real.log t ^ 2)) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact (integrableOn_theta_div_id_mul_log_sq b).mono_set (Set.Icc_subset_Icc ha le_rfl)
  exact h1.sub (continuousOn_inv_log ha hab 2).intervalIntegrable

lemma gfun_eq {t : ℝ} (ht : 2 ≤ t) : gfun t = (θ t - t) / (t * Real.log t ^ 2) := by
  have ht0 : t ≠ 0 := by linarith
  have hl := (log_pos_of_two_le ht).ne'
  unfold gfun; field_simp

lemma abs_gfun_le_small {t : ℝ} (ht : 2 ≤ t) : |gfun t| ≤ 1 / Real.log t ^ 2 := by
  have ht0 : 0 < t := by linarith
  have hl := log_pos_of_two_le ht
  rw [gfun_eq ht, abs_div, abs_of_pos (by positivity : 0 < t * Real.log t ^ 2),
    div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 := theta_nonneg t
  have h2 := theta_le_log4_mul_x ht0.le
  have h4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
    linarith [Real.log_two_lt_d9]
  have : |θ t - t| ≤ t := by rw [abs_le]; constructor <;> nlinarith
  nlinarith [sq_nonneg (Real.log t)]

lemma small_piece {a b ℓ : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (hℓ : 0 < ℓ) (hℓa : ℓ ≤ Real.log a) :
    |∫ t in a..b, gfun t| ≤ (b - a) / ℓ ^ 2 := by
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := a) (b := b) (f := gfun)
    (C := 1 / ℓ ^ 2) (fun t ht => by
      rw [Set.uIoc_of_le hab] at ht
      rw [Real.norm_eq_abs]
      refine (abs_gfun_le_small (by linarith [ht.1])).trans ?_
      have hl : ℓ ≤ Real.log t := hℓa.trans (Real.log_le_log (by linarith) ht.1.le)
      exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hℓ.le hl 2))
  rw [Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ b - a)] at this
  calc _ ≤ 1 / ℓ ^ 2 * (b - a) := this
    _ = (b - a) / ℓ ^ 2 := by ring

lemma piece_k (k : ℕ) (hk : 1 ≤ k) {b : ℝ} (hb : (2 : ℝ) ^ k ≤ b) :
    |∫ t in (2 : ℝ) ^ k..b, gfun t| ≤ (b - 2 ^ k) / (k * 0.6931471803) ^ 2 := by
  refine small_piece ?_ hb (by positivity) ?_
  · calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk
  · rw [Real.log_pow]
    exact mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg k)

/-- `|∫₂^599 g| ≤ 33`. -/
theorem integral_small : |∫ t in (2 : ℝ)..599, gfun t| ≤ 33 := by
  have I := fun a b (ha : (2 : ℝ) ≤ a) (hab : a ≤ b) => intervalIntegrable_gfun ha hab
  have s1 := piece_k 1 le_rfl (b := 4) (by norm_num)
  have s2 := piece_k 2 (by norm_num) (b := 8) (by norm_num)
  have s3 := piece_k 3 (by norm_num) (b := 16) (by norm_num)
  have s4 := piece_k 4 (by norm_num) (b := 32) (by norm_num)
  have s5 := piece_k 5 (by norm_num) (b := 64) (by norm_num)
  have s6 := piece_k 6 (by norm_num) (b := 128) (by norm_num)
  have s7 := piece_k 7 (by norm_num) (b := 256) (by norm_num)
  have s8 := piece_k 8 (by norm_num) (b := 512) (by norm_num)
  have s9 := piece_k 9 (by norm_num) (b := 599) (by norm_num)
  replace s1 := abs_le.mp s1; replace s2 := abs_le.mp s2; replace s3 := abs_le.mp s3
  replace s4 := abs_le.mp s4; replace s5 := abs_le.mp s5; replace s6 := abs_le.mp s6
  replace s7 := abs_le.mp s7; replace s8 := abs_le.mp s8; replace s9 := abs_le.mp s9
  norm_num at s1 s2 s3 s4 s5 s6 s7 s8 s9
  have e : ∫ t in (2 : ℝ)..599, gfun t
      = (∫ t in (2 : ℝ)..4, gfun t) + (∫ t in (4 : ℝ)..8, gfun t) + (∫ t in (8 : ℝ)..16, gfun t)
        + (∫ t in (16 : ℝ)..32, gfun t) + (∫ t in (32 : ℝ)..64, gfun t)
        + (∫ t in (64 : ℝ)..128, gfun t) + (∫ t in (128 : ℝ)..256, gfun t)
        + (∫ t in (256 : ℝ)..512, gfun t) + (∫ t in (512 : ℝ)..599, gfun t) := by
    simp only [intervalIntegral.integral_add_adjacent_intervals (I 2 4 (by norm_num) (by norm_num))
      (I 4 8 (by norm_num) (by norm_num)), intervalIntegral.integral_add_adjacent_intervals
      (I 2 8 (by norm_num) (by norm_num)) (I 8 16 (by norm_num) (by norm_num)),
      intervalIntegral.integral_add_adjacent_intervals (I 2 16 (by norm_num) (by norm_num))
      (I 16 32 (by norm_num) (by norm_num)), intervalIntegral.integral_add_adjacent_intervals
      (I 2 32 (by norm_num) (by norm_num)) (I 32 64 (by norm_num) (by norm_num)),
      intervalIntegral.integral_add_adjacent_intervals (I 2 64 (by norm_num) (by norm_num))
      (I 64 128 (by norm_num) (by norm_num)), intervalIntegral.integral_add_adjacent_intervals
      (I 2 128 (by norm_num) (by norm_num)) (I 128 256 (by norm_num) (by norm_num)),
      intervalIntegral.integral_add_adjacent_intervals (I 2 256 (by norm_num) (by norm_num))
      (I 256 512 (by norm_num) (by norm_num)), intervalIntegral.integral_add_adjacent_intervals
      (I 2 512 (by norm_num) (by norm_num)) (I 512 599 (by norm_num) (by norm_num))]
  rw [e, abs_le]
  constructor <;> linarith [s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2, s5.1, s5.2, s6.1,
    s6.2, s7.1, s7.2, s8.1, s8.2, s9.1, s9.2]

/-- `|∫_599^x g| ≤ √x/2`. -/
theorem integral_large (hRH : RiemannHypothesis) {x : ℝ} (hx : 599 ≤ x) :
    |∫ t in (599 : ℝ)..x, gfun t| ≤ 0.5 * √x := by
  have hb : ∀ t ∈ Set.Ioc (599 : ℝ) x, ‖gfun t‖ ≤ 0.25 / √t := by
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl : 0 < Real.log t := log_pos_of_two_le (by linarith [ht.1])
    have hth := theta_sub_lt_quarter hRH (x := t) ht.1.le
    have hs : 0 < √t := Real.sqrt_pos.mpr ht0
    have hst : √t * √t = t := Real.mul_self_sqrt ht0.le
    rw [Real.norm_eq_abs, gfun_eq (by linarith [ht.1]), abs_div,
      abs_of_pos (by positivity : 0 < t * Real.log t ^ 2),
      div_le_div_iff₀ (by positivity) hs]
    have h1 : |θ t - t| * √t ≤ (1 / 4 * (√t * Real.log t ^ 2)) * √t :=
      mul_le_mul_of_nonneg_right hth.le hs.le
    have h2 : (1 / 4 * (√t * Real.log t ^ 2)) * √t = (√t * √t) * (Real.log t ^ 2 / 4) := by ring
    rw [hst] at h2
    nlinarith
  have hint : IntervalIntegrable (fun t => 0.25 / √t) volume 599 x := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [Set.uIcc_of_le hx] at ht
    exact (continuousAt_const.div Real.continuous_sqrt.continuousAt
      (Real.sqrt_pos.mpr (by linarith [ht.1])).ne').continuousWithinAt
  have hle := intervalIntegral.norm_integral_le_of_norm_le hx
    (ae_of_all _ fun t ht => hb t ht) hint
  have hval : ∫ t in (599 : ℝ)..x, 0.25 / √t = 0.5 * √x - 0.5 * √599 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => 0.5 * √t)
      (fun t ht => ?_) hint
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have := (Real.hasDerivAt_sqrt ht0).const_mul (0.5 : ℝ)
    convert this using 1
    have : 0 < √t := Real.sqrt_pos.mpr (by linarith [ht.1])
    field_simp; norm_num
  rw [hval, Real.norm_eq_abs] at hle
  have : 0 ≤ √(599 : ℝ) := Real.sqrt_nonneg _
  linarith

lemma pi_fin {s L : ℝ} (hs : 51.5 ≤ s) (hL : 7.85 ≤ L) :
    1 / 4 * (s * L) + (33 + 0.5 * s) + 2.886 < 9 / 20 * (s * L) := by
  nlinarith [mul_le_mul hs hL (by norm_num) (by linarith)]

/-- **`|π(x) − li(x)| < (9/20) √x log x` for `x ≥ 2657`, under RH.** -/
theorem piBound_of_RH (hRH : RiemannHypothesis) : PiBound (9 / 20) 2657 := by
  intro x hx
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hl0 := log_pos_of_two_le hx2
  have hpi := Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2
  have hli := logIntegral_eq hx2
  have hI1 : IntervalIntegrable (fun t => θ t / (t * Real.log t ^ 2)) volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hx2]
    exact integrableOn_theta_div_id_mul_log_sq x
  have hI2 : IntervalIntegrable (fun t : ℝ => 1 / Real.log t ^ 2) volume 2 x :=
    (continuousOn_inv_log le_rfl hx2 2).intervalIntegrable
  have hg : ∫ t in (2 : ℝ)..x, gfun t
      = (∫ t in (2 : ℝ)..x, θ t / (t * Real.log t ^ 2)) - ∫ t in (2 : ℝ)..x, 1 / Real.log t ^ 2 :=
    intervalIntegral.integral_sub hI1 hI2
  have hsplit : ∫ t in (2 : ℝ)..x, gfun t
      = (∫ t in (2 : ℝ)..599, gfun t) + ∫ t in (599 : ℝ)..x, gfun t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_gfun le_rfl (by norm_num)) (intervalIntegrable_gfun (by norm_num)
        (by linarith))).symm
  have hdec : (Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x
      = (θ x - x) / Real.log x + (∫ t in (2 : ℝ)..x, gfun t)
        + (2 / Real.log 2 - logIntegralTwo) := by
    rw [hpi, hli, hg, sub_div, div_eq_mul_inv]; ring
  have hS := integral_small
  have hL := integral_large hRH (x := x) (by linarith)
  have hθ := theta_sub_lt_quarter hRH (x := x) (by linarith)
  have hli2 := logIntegralTwo_nonneg
  have hli2' := logIntegralTwo_le_two
  have hlog2 := Real.log_two_gt_d9
  have h2l : 2 / Real.log 2 ≤ 2.886 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have h2l' : 2 ≤ 2 / Real.log 2 := by
    rw [le_div_iff₀ (by linarith)]; linarith [Real.log_two_lt_d9]
  have hsx : 51.5 ≤ √x := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hlx : 7.85 ≤ Real.log x := by
    have := log_ge_of_pow_le 11 (show (2 : ℝ) ^ 11 ≤ x by norm_num; linarith)
    have : (2 : ℝ) ^ 11 / x ≤ 2048 / 2657 := by
      rw [div_le_div_iff₀ hx0 (by norm_num)]; norm_num; linarith
    norm_num at *; linarith
  have hθ' : |(θ x - x) / Real.log x| < 1 / 4 * (√x * Real.log x) := by
    rw [abs_div, abs_of_pos hl0, div_lt_iff₀ hl0]
    calc |θ x - x| < _ := hθ
      _ = _ := by ring
  rw [hdec, hsplit]
  set A := (θ x - x) / Real.log x
  set B1 := ∫ t in (2 : ℝ)..599, gfun t
  set B2 := ∫ t in (599 : ℝ)..x, gfun t
  set C := 2 / Real.log 2 - logIntegralTwo
  have a1 := abs_add_le (A + (B1 + B2)) C
  have a2 := abs_add_le A (B1 + B2)
  have a3 := abs_add_le B1 B2
  have hc : |2 / Real.log 2 - logIntegralTwo| ≤ 2.886 := by
    rw [abs_le]; constructor <;> linarith
  have hfin : 1 / 4 * (√x * Real.log x) + (33 + 0.5 * √x) + 2.886
      < 9 / 20 * (√x * Real.log x) := pi_fin hsx hlx
  linarith

end Schoenfeld
