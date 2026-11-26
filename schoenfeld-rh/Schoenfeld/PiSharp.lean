import Schoenfeld.Sharp
import Schoenfeld.Pi

/-!
# `|π(x) − li(x)| < √x log x / (8π)` for `x ≥ 4·10⁵`

From `π(x) − li(x) = (θ(x) − x)/log x + ∫₂ˣ g + (2/log 2 − li(2))`, `g = (θ(t) − t)/(t log² t)`:

* `∫₂^599 g`: `≤ 33` (`integral_small`);
* `∫_599^{3·10⁴} g`: `ThetaSmallRange` gives `|g(t)| ≤ 1/(8π√t)`, so `≤ 14`;
* `∫_{3·10⁴}^x g`, `x ≤ 10¹⁰`: `theta_mid_abs` gives `|g(t)| ≤ 3.93/(√t log² t)` and
  `∫ dt/(√t log² t) ≤ 1.6504 · 2√x/log² x` (`integral_inv_sqrt_log_sq`);
* `∫_{10¹⁰}^x g`: `theta_explicit` gives `|g(t)| ≤ (1/(8π) − 0.2985/ℓ + 5.667/ℓ²)/√t`, and
  `2√t (1/(8π) − 0.2985/ℓ + 6.2/ℓ²)` is a larger antiderivative for `ℓ ≥ 22` (`integral_rtrick`).

The last step leaves `√x ((2/(8π) − 0.2985) + 5.07/u + 12.4/u²) < 5138`, checked on
`[23.01, 24]`, `[24, 25]`, `[25, 26]` and `[26, ∞)`.
-/

namespace Schoenfeld

open Real Chebyshev MeasureTheory

/-- The decomposition of `π − li`. -/
theorem pi_sub_li_eq {x : ℝ} (hx2 : 2 ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x
      = (θ x - x) / Real.log x + (∫ t in (2 : ℝ)..x, gfun t)
        + (2 / Real.log 2 - logIntegralTwo) := by
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
  rw [hpi, hli, hg, sub_div, div_eq_mul_inv]; ring

lemma pi_const_bound : |2 / Real.log 2 - logIntegralTwo| ≤ 2.886 := by
  have hli2 := logIntegralTwo_nonneg
  have hli2' := logIntegralTwo_le_two
  have hlog2 := Real.log_two_gt_d9
  have h2l : 2 / Real.log 2 ≤ 2.886 := by rw [div_le_iff₀ (by linarith)]; nlinarith
  have h2l' : 2 ≤ 2 / Real.log 2 := by
    rw [le_div_iff₀ (by linarith)]; linarith [Real.log_two_lt_d9]
  rw [abs_le]; constructor <;> linarith

/-- `|∫ₐᵇ g| ≤ ∫ₐᵇ G` when `|g| ≤ G` on `(a, b]`. -/
lemma abs_integral_gfun_le {a b : ℝ} {G : ℝ → ℝ} (hab : a ≤ b)
    (hb : ∀ t ∈ Set.Ioc a b, |gfun t| ≤ G t) (hG : IntervalIntegrable G volume a b) :
    |∫ t in a..b, gfun t| ≤ ∫ t in a..b, G t := by
  have := intervalIntegral.norm_integral_le_of_norm_le hab
    (ae_of_all _ fun t ht => by rw [Real.norm_eq_abs]; exact hb t ht) hG
  rwa [Real.norm_eq_abs] at this

/-- `∫ₐᵇ c/√t = 2c(√b − √a)`. -/
lemma integral_const_div_sqrt (c : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, c / √t = 2 * c * (√b - √a) := by
  have hint : IntervalIntegrable (fun t => c / √t) volume a b := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [Set.uIcc_of_le hab] at ht
    exact (continuousAt_const.div Real.continuous_sqrt.continuousAt
      (Real.sqrt_pos.mpr (by linarith [ht.1])).ne').continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => 2 * c * √t)
    (fun t ht => ?_) hint]
  · ring
  · rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have := (Real.hasDerivAt_sqrt ht0).const_mul (2 * c)
    convert this using 1
    have : 0 < √t := Real.sqrt_pos.mpr (by linarith [ht.1])
    field_simp

/-- `∫ₐᵇ dt/(√t log² t) ≤ (L/(L − 4)) · 2√b/log² b` when `4 < L ≤ log a`. -/
lemma integral_inv_sqrt_log_sq {a b L : ℝ} (ha : 1 < a) (hab : a ≤ b) (hL : 4 < L)
    (hLa : L ≤ Real.log a) :
    ∫ t in a..b, 1 / (√t * Real.log t ^ 2) ≤ L / (L - 4) * (2 * √b / Real.log b ^ 2) := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t ∧ L ≤ Real.log t := fun t ht =>
    ⟨by linarith [ht.1], hLa.trans (Real.log_le_log (by linarith) ht.1)⟩
  set F : ℝ → ℝ := fun t => 2 * √t / Real.log t ^ 2 with hF
  set F' : ℝ → ℝ := fun t => 1 / (√t * Real.log t ^ 2) - 4 / (√t * Real.log t ^ 3) with hF'
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    obtain ⟨ht0, hlt⟩ := hpos t ht
    have hl0 : 0 < Real.log t := by linarith
    have hs := Real.hasDerivAt_sqrt ht0.ne'
    have hl := Real.hasDerivAt_log ht0.ne'
    have h := (hs.const_mul 2).div (hl.pow 2) (pow_pos hl0 2).ne'
    convert h using 1
    obtain ⟨r, hr0, rfl⟩ : ∃ r, 0 < r ∧ t = r ^ 2 :=
      ⟨√t, Real.sqrt_pos.mpr ht0, (Real.sq_sqrt ht0.le).symm⟩
    rw [Real.sqrt_sq hr0.le]
    simp only [hF', Pi.pow_apply]
    rw [Real.sqrt_sq hr0.le]
    generalize Real.log (r ^ 2) = ℓ at *
    field_simp
    ring
  have hcont : ∀ t ∈ Set.uIcc a b, ContinuousAt (fun t => 1 / (√t * Real.log t ^ 2)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    obtain ⟨ht0, hlt⟩ := hpos t ht
    have hl0 : 0 < Real.log t := by linarith
    have hs0 : 0 < √t := Real.sqrt_pos.mpr ht0
    exact continuousAt_const.div (Real.continuous_sqrt.continuousAt.mul
      ((Real.continuousAt_log ht0.ne').pow 2)) (mul_pos hs0 (pow_pos hl0 2)).ne'
  have hcont' : ∀ t ∈ Set.uIcc a b, ContinuousAt F' t := by
    intro t ht
    have hc1 := hcont t ht
    rw [Set.uIcc_of_le hab] at ht
    obtain ⟨ht0, hlt⟩ := hpos t ht
    have hl0 : 0 < Real.log t := by linarith
    have hs0 : 0 < √t := Real.sqrt_pos.mpr ht0
    exact hc1.sub (continuousAt_const.div (Real.continuous_sqrt.continuousAt.mul
      ((Real.continuousAt_log ht0.ne').pow 3)) (mul_pos hs0 (pow_pos hl0 3)).ne')
  have hi1 : IntervalIntegrable (fun t => 1 / (√t * Real.log t ^ 2)) volume a b :=
    ContinuousOn.intervalIntegrable fun t ht => (hcont t ht).continuousWithinAt
  have hi2 : IntervalIntegrable F' volume a b :=
    ContinuousOn.intervalIntegrable fun t ht => (hcont' t ht).continuousWithinAt
  have hle : ∫ t in a..b, 1 / (√t * Real.log t ^ 2) ≤ ∫ t in a..b, L / (L - 4) * F' t := by
    refine intervalIntegral.integral_mono_on hab hi1 (hi2.const_mul _) fun t ht => ?_
    obtain ⟨ht0, hlt⟩ := hpos t ht
    have hl0 : 0 < Real.log t := by linarith
    have hs : 0 < √t := Real.sqrt_pos.mpr ht0
    simp only [hF']
    rw [show 1 / (√t * Real.log t ^ 2) - 4 / (√t * Real.log t ^ 3)
      = 1 / (√t * Real.log t ^ 2) * (1 - 4 / Real.log t) by field_simp]
    have hA : 0 < 1 / (√t * Real.log t ^ 2) := by
      have := mul_pos hs (pow_pos hl0 2); positivity
    have hq : 1 ≤ L / (L - 4) * (1 - 4 / Real.log t) := by
      have h1 : 4 / Real.log t ≤ 4 / L := div_le_div_of_nonneg_left (by norm_num) (by linarith) hlt
      have h4 : L * (4 / L) = 4 := by field_simp
      rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
      nlinarith
    calc 1 / (√t * Real.log t ^ 2) = 1 / (√t * Real.log t ^ 2) * 1 := by ring
      _ ≤ 1 / (√t * Real.log t ^ 2) * (L / (L - 4) * (1 - 4 / Real.log t)) :=
          mul_le_mul_of_nonneg_left hq hA.le
      _ = L / (L - 4) * (1 / (√t * Real.log t ^ 2) * (1 - 4 / Real.log t)) := by ring
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi2] at hle
  have hFa : 0 ≤ F a := by
    have := (hpos a ⟨le_rfl, hab⟩).1
    simp only [hF]; positivity
  have hc : 0 ≤ L / (L - 4) := div_nonneg (by linarith) (by linarith)
  calc _ ≤ L / (L - 4) * (F b - F a) := hle
    _ ≤ L / (L - 4) * F b := by nlinarith
    _ = _ := rfl

/-- The antiderivative `2√t (c₀ − β/ℓ + d/ℓ²)` dominates `(c₀ − β/ℓ + γ/ℓ²)/√t` when
`(d + 2β − γ) ℓ ≥ 4d`. -/
lemma integral_rtrick {a b c₀ β γ d L : ℝ} (ha : 1 < a) (hab : a ≤ b) (hL0 : 0 < L)
    (hLa : L ≤ Real.log a) (hd : 0 ≤ d) (hkey : 4 * d ≤ (d + 2 * β - γ) * L) :
    ∫ t in a..b, (c₀ - β / Real.log t + γ / Real.log t ^ 2) / √t
      ≤ 2 * √b * (c₀ - β / Real.log b + d / Real.log b ^ 2)
        - 2 * √a * (c₀ - β / Real.log a + d / Real.log a ^ 2) := by
  have hpos : ∀ t ∈ Set.Icc a b, 0 < t ∧ L ≤ Real.log t := fun t ht =>
    ⟨by linarith [ht.1], hLa.trans (Real.log_le_log (by linarith) ht.1)⟩
  set F : ℝ → ℝ := fun t => 2 * √t * (c₀ - β / Real.log t + d / Real.log t ^ 2) with hF
  set F' : ℝ → ℝ := fun t =>
    (c₀ - β / Real.log t + (d + 2 * β) / Real.log t ^ 2 - 4 * d / Real.log t ^ 3) / √t with hF'
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    obtain ⟨ht0, hlt⟩ := hpos t ht
    have hl0 : 0 < Real.log t := by linarith
    have hs := Real.hasDerivAt_sqrt ht0.ne'
    have hl := Real.hasDerivAt_log ht0.ne'
    have h := (hs.const_mul 2).mul ((hasDerivAt_const t c₀).sub ((hasDerivAt_const t β).div hl
      hl0.ne') |>.add ((hasDerivAt_const t d).div (hl.pow 2) (pow_pos hl0 2).ne'))
    convert h using 1
    obtain ⟨r, hr0, rfl⟩ : ∃ r, 0 < r ∧ t = r ^ 2 :=
      ⟨√t, Real.sqrt_pos.mpr ht0, (Real.sq_sqrt ht0.le).symm⟩
    simp only [hF', Pi.pow_apply, Pi.sub_apply, Pi.add_apply, Pi.div_apply, Nat.cast_ofNat]
    rw [Real.sqrt_sq hr0.le]
    generalize Real.log (r ^ 2) = ℓ at *
    field_simp
    ring
  have hcont : ∀ t ∈ Set.uIcc a b, 0 < t ∧ 0 < Real.log t ∧ 0 < √t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    obtain ⟨ht0, hlt⟩ := hpos t ht
    exact ⟨ht0, by linarith, Real.sqrt_pos.mpr ht0⟩
  have hi1 : IntervalIntegrable (fun t => (c₀ - β / Real.log t + γ / Real.log t ^ 2) / √t)
      volume a b := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    obtain ⟨ht0, hl0, hs⟩ := hcont t ht
    have hl := Real.continuousAt_log ht0.ne'
    exact ((continuousAt_const.sub (continuousAt_const.div hl hl0.ne')).add
      (continuousAt_const.div (hl.pow 2) (pow_pos hl0 2).ne')).div
      Real.continuous_sqrt.continuousAt hs.ne' |>.continuousWithinAt
  have hi2 : IntervalIntegrable F' volume a b := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    obtain ⟨ht0, hl0, hs⟩ := hcont t ht
    have hl := Real.continuousAt_log ht0.ne'
    exact ((((continuousAt_const.sub (continuousAt_const.div hl hl0.ne')).add
      (continuousAt_const.div (hl.pow 2) (pow_pos hl0 2).ne')).sub
      (continuousAt_const.div (hl.pow 3) (pow_pos hl0 3).ne'))).div
      Real.continuous_sqrt.continuousAt hs.ne' |>.continuousWithinAt
  have hle := intervalIntegral.integral_mono_on hab hi1 hi2 fun t ht => by
    obtain ⟨ht0, hlt⟩ := hpos t ht
    have hl0 : 0 < Real.log t := by linarith
    have hs : 0 < √t := Real.sqrt_pos.mpr ht0
    simp only [hF']
    apply div_le_div_of_nonneg_right _ hs.le
    have hk : 4 * d ≤ (d + 2 * β - γ) * Real.log t := by
      have : 0 ≤ d + 2 * β - γ := by
        by_contra hc; push Not at hc; nlinarith
      nlinarith
    have : 4 * d / Real.log t ^ 3 ≤ (d + 2 * β - γ) / Real.log t ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have : (d + 2 * β - γ) * Real.log t ^ 3 = ((d + 2 * β - γ) * Real.log t) * Real.log t ^ 2 := by
        ring
      rw [this]
      exact mul_le_mul_of_nonneg_right hk (by positivity)
    have e : (d + 2 * β) / Real.log t ^ 2 = γ / Real.log t ^ 2 + (d + 2 * β - γ) / Real.log t ^ 2 := by
      ring
    linarith
  rwa [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hi2] at hle

/-- `|θ(t) − t| ≤ √t K` gives `|g(t)| ≤ K/(√t log² t)`. -/
lemma abs_gfun_le_of {t K : ℝ} (ht : 2 ≤ t) (h : |θ t - t| ≤ √t * K) :
    |gfun t| ≤ K / (√t * Real.log t ^ 2) := by
  have ht0 : 0 < t := by linarith
  have hl := log_pos_of_two_le ht
  have hs : 0 < √t := Real.sqrt_pos.mpr ht0
  have hst : √t * √t = t := Real.mul_self_sqrt ht0.le
  rw [gfun_eq ht, abs_div, abs_of_pos (by positivity : 0 < t * Real.log t ^ 2)]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e : √t * K * (√t * Real.log t ^ 2) = K * (t * Real.log t ^ 2) := by
    rw [show √t * K * (√t * Real.log t ^ 2) = (√t * √t) * (K * Real.log t ^ 2) by ring, hst]; ring
  calc |θ t - t| * (√t * Real.log t ^ 2) ≤ √t * K * (√t * Real.log t ^ 2) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = K * (t * Real.log t ^ 2) := e

lemma log_three_e4 : 10.15 ≤ Real.log 30000 := by
  have := log_ge_of_pow_le 14 (show (2 : ℝ) ^ 14 ≤ 30000 by norm_num)
  norm_num at this ⊢; linarith

lemma log_e10_lo : 23.01 ≤ Real.log (10 ^ 10) := by
  have := log_ge_of_pow_le 33 (show (2 : ℝ) ^ 33 ≤ 10 ^ 10 by norm_num)
  norm_num at this ⊢; linarith

lemma log_e10_hi : Real.log (10 ^ 10) ≤ 23.3 := by
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1.25 by norm_num)
  have e : Real.log (10 ^ 10) = 10 * (3 * Real.log 2 + Real.log 1.25) := by
    rw [Real.log_pow, show (10 : ℝ) = 2 ^ 3 * 1.25 by norm_num,
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]; push_cast; ring
  rw [e]; linarith [log_two_bounds.2]

/-- `|∫_599^{3·10⁴} g| ≤ 14`, from `ThetaSmallRange`. -/
theorem integral_piece2 (hS : ThetaSmallRange) : |∫ t in (599 : ℝ)..30000, gfun t| ≤ 14 := by
  have hp := Real.pi_gt_d4
  have hb : ∀ t ∈ Set.Ioc (599 : ℝ) 30000, |gfun t| ≤ 1 / (8 * π) / √t := by
    intro t ht
    have ht2 : 2 ≤ t := by linarith [ht.1]
    have h := abs_gfun_le_of ht2 (K := Real.log t ^ 2 / (8 * π)) (by
      have := (hS t ht.1.le ht.2).le
      calc |θ t - t| ≤ 1 / (8 * π) * (√t * Real.log t ^ 2) := this
        _ = √t * (Real.log t ^ 2 / (8 * π)) := by ring)
    have hl := log_pos_of_two_le ht2
    have hs : 0 < √t := Real.sqrt_pos.mpr (by linarith)
    calc |gfun t| ≤ _ := h
      _ = 1 / (8 * π) / √t := by field_simp
  have hint : IntervalIntegrable (fun t => 1 / (8 * π) / √t) volume 599 30000 := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [Set.uIcc_of_le (by norm_num)] at ht
    exact (continuousAt_const.div Real.continuous_sqrt.continuousAt
      (Real.sqrt_pos.mpr (by linarith [ht.1])).ne').continuousWithinAt
  refine (abs_integral_gfun_le (by norm_num) hb hint).trans ?_
  rw [integral_const_div_sqrt _ (by norm_num) (by norm_num)]
  have h1 : √(30000 : ℝ) ≤ 173.3 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have h2 : 0 ≤ √(599 : ℝ) := Real.sqrt_nonneg _
  have h3 : 1 / (8 * π) ≤ 0.0398 := by rw [div_le_iff₀ (by positivity)]; nlinarith
  have h4 : 0 ≤ 1 / (8 * π) := by positivity
  nlinarith

/-- `|∫_{3·10⁴}^b g| ≤ 3.9252 · (10.15/6.15) · 2√b/log² b` for `b ≤ 10¹⁰`, from PsiCert. -/
theorem integral_piece3 (hC : PsiCert) {b : ℝ} (hb1 : 30000 ≤ b) (hb2 : b ≤ 10 ^ 10) :
    |∫ t in (30000 : ℝ)..b, gfun t| ≤ 3.9252 * (10.15 / (10.15 - 4) * (2 * √b / Real.log b ^ 2)) := by
  have hb : ∀ t ∈ Set.Ioc (30000 : ℝ) b, |gfun t| ≤ 3.9252 * (1 / (√t * Real.log t ^ 2)) := by
    intro t ht
    have h1 := theta_mid_abs hC ht.1.le (ht.2.trans hb2)
    have h2 : |θ t - t| ≤ √t * 3.9252 := by rw [mul_comm]; exact h1
    have h := abs_gfun_le_of (by linarith [ht.1]) h2
    calc |gfun t| ≤ _ := h
      _ = _ := by ring
  have hc : IntervalIntegrable (fun t => 1 / (√t * Real.log t ^ 2)) volume 30000 b := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [Set.uIcc_of_le hb1] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hs0 : 0 < √t := Real.sqrt_pos.mpr ht0
    exact (continuousAt_const.div (Real.continuous_sqrt.continuousAt.mul
      ((Real.continuousAt_log ht0.ne').pow 2)) (mul_pos hs0 (pow_pos hl0 2)).ne').continuousWithinAt
  have hint : IntervalIntegrable (fun t => 3.9252 * (1 / (√t * Real.log t ^ 2))) volume 30000 b :=
    hc.const_mul 3.9252
  refine (abs_integral_gfun_le hb1 hb hint).trans ?_
  rw [intervalIntegral.integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_inv_sqrt_log_sq (by norm_num) hb1 (by norm_num)
    log_three_e4) (by norm_num)

/-- The `r`-function `1/(8π) − 0.2985/ℓ + 6.2/ℓ²`. -/
noncomputable def rfun (ℓ : ℝ) : ℝ := 1 / (8 * π) - 0.2985 / ℓ + 6.2 / ℓ ^ 2

/-- `|∫_{10¹⁰}^x g| ≤ 2√x r(log x) − 2·10⁵ r(log 10¹⁰)`. -/
theorem integral_piece4 (hRH : RiemannHypothesis) (hR : RosserZeroCount) (hC : PsiCert) {x : ℝ}
    (hx : 10 ^ 10 ≤ x) :
    |∫ t in (10 ^ 10 : ℝ)..x, gfun t|
      ≤ 2 * √x * rfun (Real.log x) - 2 * 100000 * rfun (Real.log (10 ^ 10)) := by
  have hb : ∀ t ∈ Set.Ioc (10 ^ 10 : ℝ) x,
      |gfun t| ≤ (1 / (8 * π) - 0.2985 / Real.log t + 5.667 / Real.log t ^ 2) / √t := by
    intro t ht
    have ht2 : 2 ≤ t := by linarith [ht.1]
    have h := abs_gfun_le_of ht2 (theta_explicit hRH hR hC ht.1.le)
    have hl := log_pos_of_two_le ht2
    have hs : 0 < √t := Real.sqrt_pos.mpr (by linarith)
    calc |gfun t| ≤ _ := h
      _ = _ := by field_simp
  have hint : IntervalIntegrable
      (fun t => (1 / (8 * π) - 0.2985 / Real.log t + 5.667 / Real.log t ^ 2) / √t)
      volume (10 ^ 10) x := by
    refine ContinuousOn.intervalIntegrable fun t ht => ?_
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hl0 : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hs0 : 0 < √t := Real.sqrt_pos.mpr ht0
    have hl := Real.continuousAt_log ht0.ne'
    exact ((continuousAt_const.sub (continuousAt_const.div hl hl0.ne')).add
      (continuousAt_const.div (hl.pow 2) (pow_pos hl0 2).ne')).div
      Real.continuous_sqrt.continuousAt hs0.ne' |>.continuousWithinAt
  refine (abs_integral_gfun_le hx hb hint).trans ?_
  have hL := log_e10_lo
  have h := integral_rtrick (c₀ := 1 / (8 * π)) (β := 0.2985) (γ := 5.667) (d := 6.2) (L := 22)
    (a := 10 ^ 10) (b := x) (by norm_num) hx (by norm_num) ((by norm_num : (22 : ℝ) ≤ 23.01).trans hL)
    (by norm_num) (by norm_num)
  have hs : √((10 : ℝ) ^ 10) = 100000 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]; norm_num
  rw [hs] at h
  unfold rfun
  linarith

lemma sqrt_le_of_log_le {x B : ℝ} {n : ℕ} (hx : 0 < x) (hB : 0 ≤ B) (hn0 : n ≠ 0)
    (hu : Real.log x ≤ n) (hn : (2.7182818286 : ℝ) ^ n ≤ B ^ 2) : √x ≤ B := by
  have h1 : x ≤ Real.exp n := by
    calc x = Real.exp (Real.log x) := (Real.exp_log hx).symm
      _ ≤ Real.exp n := Real.exp_le_exp.mpr hu
  have h2 : Real.exp n < 2.7182818286 ^ n := by
    rw [← Real.exp_one_pow]
    exact pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le hn0
  rw [Real.sqrt_le_left hB]
  linarith

/-- **`|π(x) − li(x)| < √x log x/(8π)` for `4·10⁵ ≤ x ≤ 10¹⁰`.** -/
theorem pi_mid (hC : PsiCert) (hS : ThetaSmallRange) {x : ℝ} (h1 : 400000 ≤ x) (h2 : x ≤ 10 ^ 10) :
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x| < 1 / (8 * π) * (√x * Real.log x) := by
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hp := Real.pi_lt_d4
  have hpi := Real.pi_pos
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
  set s := √x with hsdef
  set u := Real.log x with hudef
  have hs : 632 ≤ s := Real.le_sqrt_of_sq_le (by norm_num; linarith)
  have hu : 12.82 ≤ u := by
    have := log_ge_of_pow_le 18 (show (2 : ℝ) ^ 18 ≤ x by norm_num; linarith)
    have : (2 : ℝ) ^ 18 / x ≤ 262144 / 400000 := by
      rw [div_le_div_iff₀ hx0 (by norm_num)]; norm_num; linarith
    norm_num at *; linarith
  have hu0 : 0 < u := by linarith
  have hA : |(θ x - x) / u| ≤ 3.9252 * (s / u) := by
    rw [abs_div, abs_of_pos hu0, mul_div_assoc']
    exact div_le_div_of_nonneg_right hθ hu0.le
  -- numerics
  have h1u : s / u ≤ s / 12.82 := div_le_div_of_nonneg_left (by linarith) (by norm_num) hu
  have hu2 : 164.35 ≤ u ^ 2 := by nlinarith
  have h2u : 2 * s / u ^ 2 ≤ 2 * s / 164.35 :=
    div_le_div_of_nonneg_left (by linarith) (by norm_num) hu2
  have hR : 0.51 * s ≤ 1 / (8 * π) * (s * u) := by
    rw [show 1 / (8 * π) * (s * u) = s * u / (8 * π) by ring, le_div_iff₀ (by positivity)]
    nlinarith
  set A := (θ x - x) / u
  set B1 := ∫ t in (2 : ℝ)..599, gfun t
  set B2 := ∫ t in (599 : ℝ)..30000, gfun t
  set B3 := ∫ t in (30000 : ℝ)..x, gfun t
  set C := 2 / Real.log 2 - logIntegralTwo
  have a1 := abs_add_le (A + (B1 + B2 + B3)) C
  have a2 := abs_add_le A (B1 + B2 + B3)
  have a3 := abs_add_le (B1 + B2) B3
  have a4 := abs_add_le B1 B2
  have e : A + (B1 + B2 + B3) + C = A + (B1 + B2 + B3) + C := rfl
  have hk : 3.9252 * (10.15 / (10.15 - 4) * (2 * s / u ^ 2)) ≤ 6.479 * (2 * s / 164.35) := by
    have : (3.9252 : ℝ) * (10.15 / (10.15 - 4)) ≤ 6.479 := by norm_num
    have h0 : 0 ≤ 2 * s / u ^ 2 := by positivity
    calc 3.9252 * (10.15 / (10.15 - 4) * (2 * s / u ^ 2))
        = 3.9252 * (10.15 / (10.15 - 4)) * (2 * s / u ^ 2) := by ring
      _ ≤ 6.479 * (2 * s / u ^ 2) := mul_le_mul_of_nonneg_right this h0
      _ ≤ 6.479 * (2 * s / 164.35) := mul_le_mul_of_nonneg_left h2u (by norm_num)
  have hfin : 3.9252 * (s / 12.82) + 33 + 14 + 6.479 * (2 * s / 164.35) + 2.886 < 0.51 * s := by
    norm_num; linarith
  calc |A + (B1 + B2 + B3) + C| ≤ |A| + (|B1| + |B2| + |B3|) + |C| := by linarith
    _ < 1 / (8 * π) * (s * u) := by nlinarith

/-- **`|π(x) − li(x)| < √x log x/(8π)` for `x ≥ 10¹⁰`.** -/
theorem pi_large (hRH : RiemannHypothesis) (hR : RosserZeroCount) (hC : PsiCert)
    (hS : ThetaSmallRange) {x : ℝ} (hx : 10 ^ 10 ≤ x) :
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - logIntegral x| < 1 / (8 * π) * (√x * Real.log x) := by
  have hx2 : 2 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hp := Real.pi_lt_d4
  have hp' := Real.pi_gt_d4
  have hpi := Real.pi_pos
  rw [pi_sub_li_eq hx2]
  have I := fun a b (ha : (2 : ℝ) ≤ a) (hab : a ≤ b) => intervalIntegrable_gfun ha hab
  have hsplit : ∫ t in (2 : ℝ)..x, gfun t = (∫ t in (2 : ℝ)..599, gfun t)
      + (∫ t in (599 : ℝ)..30000, gfun t) + (∫ t in (30000 : ℝ)..10 ^ 10, gfun t)
      + ∫ t in (10 ^ 10 : ℝ)..x, gfun t := by
    rw [intervalIntegral.integral_add_adjacent_intervals (I 2 599 (by norm_num) (by norm_num))
      (I 599 30000 (by norm_num) (by norm_num)),
      intervalIntegral.integral_add_adjacent_intervals (I 2 30000 (by norm_num) (by norm_num))
      (I 30000 (10 ^ 10) (by norm_num) (by norm_num)),
      intervalIntegral.integral_add_adjacent_intervals (I 2 (10 ^ 10) (by norm_num) (by norm_num))
      (I (10 ^ 10) x (by norm_num) hx)]
  rw [hsplit]
  have hI1 := integral_small
  have hI2 := integral_piece2 hS
  have hI3 := integral_piece3 hC (b := 10 ^ 10) (by norm_num) le_rfl
  have hI4 := integral_piece4 hRH hR hC hx
  have hc := pi_const_bound
  have hθ := theta_explicit hRH hR hC hx
  have hlo := log_e10_lo
  have hhi := log_e10_hi
  have hs10 : √((10 : ℝ) ^ 10) = 100000 := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)]; norm_num
  rw [hs10] at hI3
  -- `I3 ≤ 2448`
  have hI3' : 3.9252 * (10.15 / (10.15 - 4) * (2 * 100000 / Real.log (10 ^ 10) ^ 2)) ≤ 2448 := by
    have : (23.01 : ℝ) ^ 2 ≤ Real.log (10 ^ 10) ^ 2 := pow_le_pow_left₀ (by norm_num) hlo 2
    have h0 : 2 * 100000 / Real.log (10 ^ 10) ^ 2 ≤ 2 * 100000 / 23.01 ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) this
    have h3 : (3.9252 : ℝ) * (10.15 / (10.15 - 4)) * (2 * 100000 / (23.01 : ℝ) ^ 2) ≤ 2448 := by
      norm_num
    have h4 : (0 : ℝ) ≤ 3.9252 * (10.15 / (10.15 - 4)) := by norm_num
    calc (3.9252 : ℝ) * (10.15 / (10.15 - 4) * (2 * 100000 / Real.log (10 ^ 10) ^ 2))
        = 3.9252 * (10.15 / (10.15 - 4)) * (2 * 100000 / Real.log (10 ^ 10) ^ 2) := by ring
      _ ≤ 3.9252 * (10.15 / (10.15 - 4)) * (2 * 100000 / (23.01 : ℝ) ^ 2) :=
          mul_le_mul_of_nonneg_left h0 h4
      _ ≤ 2448 := h3
  -- `r(log 10¹⁰) ≥ 0.03823`
  have hr : 0.03823 ≤ rfun (Real.log (10 ^ 10)) := by
    unfold rfun
    set L := Real.log (10 ^ 10)
    have h1 : 0.2985 / L ≤ 0.2985 / 23.01 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlo
    have h2 : 6.2 / 23.3 ^ 2 ≤ 6.2 / L ^ 2 :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ (by linarith) hhi 2)
    have h3 : 0.0397886 ≤ 1 / (8 * π) := by rw [le_div_iff₀ (by positivity)]; nlinarith
    have h1' : 0.2985 / L ≤ 0.012973 := h1.trans (by norm_num)
    have h2' : 0.01142 ≤ 6.2 / L ^ 2 := (show (0.01142 : ℝ) ≤ 6.2 / 23.3 ^ 2 by norm_num).trans h2
    linarith
  set s := √x with hsdef
  set u := Real.log x with hudef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hx0
  have hu : 23.01 ≤ u := hlo.trans (Real.log_le_log (by norm_num) hx)
  have hu0 : 0 < u := by linarith
  -- the θ term
  have hA : |(θ x - x) / u| ≤ s * (u / (8 * π) - 0.2985 + 5.667 / u) := by
    rw [abs_div, abs_of_pos hu0, div_le_iff₀ hu0]
    calc |θ x - x| ≤ s * (u ^ 2 / (8 * π) - 0.2985 * u + 5.667) := hθ
      _ = s * (u / (8 * π) - 0.2985 + 5.667 / u) * u := by field_simp
  -- `s · P(u) ≤ 4100`
  set p := 1 / (8 * π) with hpdef
  set q := 5.07 / u with hqdef
  set r := 12.4 / u ^ 2 with hrdef
  set P := 2 * p - 0.2985 + q + r with hPdef
  have h2c : p ≤ 0.03979 := by rw [hpdef, div_le_iff₀ (by positivity)]; nlinarith
  have hsP : s * P ≤ 4100 := by
    rcases le_or_gt u 24 with h24 | h24
    · have hsb : s ≤ 162756 := sqrt_le_of_log_le (n := 24) hx0 (by norm_num) (by norm_num)
        (by exact_mod_cast h24) (by norm_num)
      have q1 : q ≤ 0.22034 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num) hu).trans
        (by norm_num)
      have q2 : r ≤ 0.02343 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) hu 2)).trans (by norm_num)
      have hP : P ≤ 0.02485 := by rw [hPdef]; linarith
      have := mul_le_mul_of_nonneg_left hP hs0.le
      have := mul_le_mul_of_nonneg_right hsb (show (0 : ℝ) ≤ 0.02485 by norm_num)
      linarith
    rcases le_or_gt u 25 with h25 | h25
    · have hsb : s ≤ 268340 := sqrt_le_of_log_le (n := 25) hx0 (by norm_num) (by norm_num)
        (by exact_mod_cast h25) (by norm_num)
      have q1 : q ≤ 0.21125 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num) h24.le).trans
        (by norm_num)
      have q2 : r ≤ 0.021528 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) h24.le 2)).trans (by norm_num)
      have hP : P ≤ 0.01386 := by rw [hPdef]; linarith
      have := mul_le_mul_of_nonneg_left hP hs0.le
      have := mul_le_mul_of_nonneg_right hsb (show (0 : ℝ) ≤ 0.01386 by norm_num)
      linarith
    rcases le_or_gt u 26 with h26 | h26
    · have hsb : s ≤ 442414 := sqrt_le_of_log_le (n := 26) hx0 (by norm_num) (by norm_num)
        (by exact_mod_cast h26) (by norm_num)
      have q1 : q ≤ 0.2028 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num) h25.le).trans
        (by norm_num)
      have q2 : r ≤ 0.01984 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) h25.le 2)).trans (by norm_num)
      have hP : P ≤ 0.00373 := by rw [hPdef]; linarith
      have := mul_le_mul_of_nonneg_left hP hs0.le
      have := mul_le_mul_of_nonneg_right hsb (show (0 : ℝ) ≤ 0.00373 by norm_num)
      linarith
    · have q1 : q ≤ 0.19501 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num) h26.le).trans
        (by norm_num)
      have q2 : r ≤ 0.018344 := (div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        (pow_le_pow_left₀ (by norm_num) h26.le 2)).trans (by norm_num)
      have hP : P ≤ 0 := by rw [hPdef]; linarith
      have := mul_le_mul_of_nonneg_left hP hs0.le
      linarith
  -- assembly
  have hI4' : |∫ t in (10 ^ 10 : ℝ)..x, gfun t| ≤ 2 * s * rfun u - 2 * 100000 * 0.03823 := by
    have h5 := mul_le_mul_of_nonneg_left hr (show (0 : ℝ) ≤ 2 * 100000 by norm_num)
    exact hI4.trans (sub_le_sub_left h5 _)
  have hkey : s * (u / (8 * π) - 0.2985 + 5.667 / u) + 2 * s * rfun u
      = 1 / (8 * π) * (s * u) + s * P := by
    rw [hPdef, hpdef, hqdef, hrdef]; unfold rfun; field_simp; ring
  set A := (θ x - x) / u
  set B1 := ∫ t in (2 : ℝ)..599, gfun t
  set B2 := ∫ t in (599 : ℝ)..30000, gfun t
  set B3 := ∫ t in (30000 : ℝ)..10 ^ 10, gfun t
  set B4 := ∫ t in (10 ^ 10 : ℝ)..x, gfun t
  set C := 2 / Real.log 2 - logIntegralTwo
  have a1 := abs_add_le (A + (B1 + B2 + B3 + B4)) C
  have a2 := abs_add_le A (B1 + B2 + B3 + B4)
  have a3 := abs_add_le (B1 + B2 + B3) B4
  have a4 := abs_add_le (B1 + B2) B3
  have a5 := abs_add_le B1 B2
  calc |A + (B1 + B2 + B3 + B4) + C| ≤ |A| + (|B1| + |B2| + |B3| + |B4|) + |C| := by linarith
    _ < 1 / (8 * π) * (s * u) := by linarith

/-- **Schoenfeld's Corollary 1**: `|π(x) − li(x)| < √x log x/(8π)` for `x ≥ 2657`, from RH,
Rosser's zero count, PsiCert and the ranges `ThetaSmallRange`, `PiSmallRange`. -/
theorem schoenfeldPi_of_RH_of_inputs (hRH : RiemannHypothesis) (hR : RosserZeroCount) (hC : PsiCert)
    (hSθ : ThetaSmallRange) (hSπ : PiSmallRange) : SchoenfeldPi := by
  intro x hx
  rcases le_or_gt x 400000 with h | h
  · exact hSπ x hx h
  rcases le_or_gt x (10 ^ 10) with h' | h'
  · exact pi_mid hC hSθ h.le h'
  · exact pi_large hRH hR hC hSθ h'.le

/-- **Schoenfeld's Theorem 10 and Corollary 1**, `SchoenfeldStatement`, from RH, Rosser's zero
count (`RosserZeroCount`), PsiCert and the three finite ranges. -/
theorem schoenfeld_of_RH_of_inputs (hRH : RiemannHypothesis) (hR : RosserZeroCount) (hC : PsiCert)
    (hSψ : PsiSmallRange) (hSθ : ThetaSmallRange) (hSπ : PiSmallRange) : SchoenfeldStatement :=
  ⟨schoenfeldPsi_of_RH_of_inputs hRH hR hC hSψ, schoenfeldTheta_of_RH_of_inputs hRH hR hC hSθ,
    schoenfeldPi_of_RH_of_inputs hRH hR hC hSθ hSπ⟩

end Schoenfeld
