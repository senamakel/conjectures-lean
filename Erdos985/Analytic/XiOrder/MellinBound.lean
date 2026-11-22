import Erdos985.Analytic.XiOrder.LogGrowth

/-!
# Growth of `WeakFEPair.Λ₀` for kernels with exponential decay

If the kernels `f - f₀` and `g - g₀` of a weak FE-pair decay like `C exp(-p t)` for `t > 1`, then
`Λ₀ = mellin f_modif` satisfies `‖Λ₀ s‖ ≤ exp(O(‖s‖ log ‖s‖))`.
-/

namespace Erdos985.Analytic.XiOrderAux

open Real Set MeasureTheory
open scoped Nat

lemma exp_neg_le_factorial_mul {y : ℝ} (hy : 0 < y) (m : ℕ) : exp (-y) ≤ m ! * y⁻¹ ^ m := by
  have h := pow_div_factorial_le_exp (x := y) (hx := hy.le) (n := m)
  have hpos : 0 < y ^ m / m ! := by positivity
  rw [exp_neg]
  calc (exp y)⁻¹ ≤ (y ^ m / m !)⁻¹ := inv_anti₀ hpos h
    _ = m ! * y⁻¹ ^ m := by rw [inv_div, inv_pow, div_eq_mul_inv]

/-- The dominating function. -/
noncomputable def domFun : ℝ → ℝ :=
  (Ioc 0 1).indicator (fun _ => (1 : ℝ)) + (Ioi 1).indicator (fun t => t ^ (-2 : ℝ))

lemma integrableOn_domFun : IntegrableOn domFun (Ioi 0) := by
  have h1 : Integrable ((Ioc (0 : ℝ) 1).indicator (fun _ => (1 : ℝ))) :=
    (integrableOn_const (by simp)).integrable_indicator measurableSet_Ioc
  have h2 : Integrable ((Ioi (1 : ℝ)).indicator (fun t : ℝ => t ^ (-2 : ℝ))) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) zero_lt_one).integrable_indicator measurableSet_Ioi
  exact (h1.add h2).integrableOn

/-- Pointwise bound on the Mellin integrand. -/
lemma integrand_bound (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t))
    (s : ℂ) (m : ℕ) (hm : ‖s‖ + P.k + 1 ≤ m) (t : ℝ) (ht : 0 < t) :
    ‖(t : ℂ) ^ (s - 1) • P.f_modif t‖ ≤ (C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m) * domFun t := by
  have hsre : |s.re| ≤ ‖s‖ := Complex.abs_re_le_norm s
  have hk := P.hk
  have hA : 0 ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m := by positivity
  rw [norm_smul, Complex.norm_cpow_eq_rpow_re_of_pos ht, Complex.sub_re, Complex.one_re]
  rcases lt_trichotomy t 1 with h1 | rfl | h1
  · -- `0 < t < 1`: use the functional equation
    have hdom : domFun t = 1 := by
      simp [domFun, indicator, ht, h1.le, not_lt.2 h1.le]
    rw [hdom, mul_one]
    have hfm : P.f_modif t = (P.ε * ((1 / t) ^ P.k : ℝ)) • (P.g (1 / t) - P.g₀) := by
      have hfe := P.h_feq (1 / t) (by simpa using ht)
      rw [one_div_one_div] at hfe
      simp only [WeakFEPair.f_modif, Pi.add_apply, indicator, mem_Ioi, mem_Ioo, ht, h1,
        and_self, ite_true, not_lt.2 h1.le, ite_false, zero_add, hfe, smul_sub]
      congr 2
      rw [one_div, inv_rpow ht.le, rpow_neg ht.le]
    have h1t : 1 < 1 / t := by rw [lt_one_div one_pos ht, div_one]; exact h1
    rw [hfm, norm_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
    have hgb := hg (1 / t) h1t
    have he := exp_neg_le_factorial_mul (show 0 < p * (1 / t) by positivity) m
    rw [neg_mul] at hgb
    have hcalc : t ^ (s.re - 1) * (1 / t) ^ P.k * ((1 / t) ⁻¹ ^ m) ≤ 1 := by
      rw [one_div, inv_inv, inv_rpow ht.le, ← rpow_neg ht.le, ← rpow_natCast,
        ← rpow_add ht, ← rpow_add ht]
      apply rpow_le_one ht.le h1.le
      have := neg_abs_le s.re
      linarith
    calc t ^ (s.re - 1) * (‖P.ε‖ * (1 / t) ^ P.k * ‖P.g (1 / t) - P.g₀‖)
        ≤ t ^ (s.re - 1) * (‖P.ε‖ * (1 / t) ^ P.k * (C * (m ! * (p * (1 / t))⁻¹ ^ m))) := by
          gcongr
          exact hgb.trans (mul_le_mul_of_nonneg_left he hC)
      _ = C * ‖P.ε‖ * m ! * p⁻¹ ^ m * (t ^ (s.re - 1) * (1 / t) ^ P.k * ((1 / t) ⁻¹ ^ m)) := by
          rw [mul_inv, mul_pow]; ring
      _ ≤ C * ‖P.ε‖ * m ! * p⁻¹ ^ m * 1 := by gcongr
      _ ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m := by
          rw [mul_one]; gcongr; exact le_max_right _ _
  · have h0 : P.f_modif 1 = 0 := by simp [WeakFEPair.f_modif]
    rw [h0, norm_zero, mul_zero]
    exact mul_nonneg hA (by simp [domFun])
  · -- `t > 1`
    have hdom : domFun t = t ^ (-2 : ℝ) := by
      simp [domFun, indicator, h1, not_le.2 h1]
    rw [hdom]
    have hfm : P.f_modif t = P.f t - P.f₀ := by
      simp [WeakFEPair.f_modif, indicator, h1, not_lt.2 h1.le]
    rw [hfm]
    have he := exp_neg_le_factorial_mul (show 0 < p * t by positivity) m
    have hfb := hf t h1
    rw [neg_mul] at hfb
    have ht0 : 0 < t := ht
    have hcalc : t ^ (s.re - 1) * t⁻¹ ^ m ≤ t ^ (-2 : ℝ) := by
      rw [inv_pow, ← rpow_natCast, ← rpow_neg ht.le, ← rpow_add ht]
      apply rpow_le_rpow_of_exponent_le h1.le
      have := le_abs_self s.re
      linarith
    calc t ^ (s.re - 1) * ‖P.f t - P.f₀‖
        ≤ t ^ (s.re - 1) * (C * (m ! * (p * t)⁻¹ ^ m)) := by
          gcongr
          exact hfb.trans (mul_le_mul_of_nonneg_left he hC)
      _ = C * 1 * m ! * p⁻¹ ^ m * (t ^ (s.re - 1) * t⁻¹ ^ m) := by
          rw [mul_inv, mul_pow]; ring
      _ ≤ C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m * t ^ (-2 : ℝ) := by
          gcongr
          exact le_max_left _ _

lemma Λ₀_bound (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t))
    (s : ℂ) (m : ℕ) (hm : ‖s‖ + P.k + 1 ≤ m) :
    ‖P.Λ₀ s‖ ≤ (C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m) * ∫ t in Ioi 0, domFun t := by
  rw [← integral_const_mul]
  refine norm_integral_le_of_norm_le (integrableOn_domFun.const_mul _) ?_
  exact ae_restrict_of_forall_mem measurableSet_Ioi
    (fun t ht => integrand_bound P hp hC hf hg s m hm t ht)

/-- `Λ₀` of a weak FE-pair with exponentially decaying kernels lies in the growth class. -/
theorem Λ₀_logGrowth (P : WeakFEPair ℂ) {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C)
    (hf : ∀ t : ℝ, 1 < t → ‖P.f t - P.f₀‖ ≤ C * exp (-p * t))
    (hg : ∀ t : ℝ, 1 < t → ‖P.g t - P.g₀‖ ≤ C * exp (-p * t)) : LogGrowth P.Λ₀ := by
  set I0 := ∫ t in Ioi 0, domFun t
  set Q := max 1 p⁻¹
  have hQ : 1 ≤ Q := le_max_left _ _
  have hk := P.hk
  set b := P.k + 5
  refine ⟨C * max 1 ‖P.ε‖ * I0, 1 + log Q, b, by linarith [log_nonneg hQ], by linarith,
    fun s => ?_⟩
  set m := ⌈‖s‖ + P.k + 1⌉₊
  have hm : ‖s‖ + P.k + 1 ≤ m := Nat.le_ceil _
  have hm' : (m : ℝ) ≤ ‖s‖ + b := by
    have := Nat.ceil_lt_add_one (show 0 ≤ ‖s‖ + P.k + 1 by positivity)
    linarith
  have hm1 : (1 : ℝ) ≤ m := by linarith [norm_nonneg s]
  have hI0 : 0 ≤ I0 := setIntegral_nonneg measurableSet_Ioi (fun t _ => by
    simp only [domFun, Pi.add_apply]
    exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _)
      (indicator_nonneg (fun t ht => rpow_nonneg (le_of_lt (lt_trans zero_lt_one ht)) _) _))
  refine (Λ₀_bound P hp hC hf hg s m hm).trans ?_
  -- `m! p⁻¹^m ≤ (m Q)^m = exp (m log (m Q))`
  have hfac : (m ! : ℝ) * p⁻¹ ^ m ≤ exp ((1 + log Q) * ((‖s‖ + b) * log (‖s‖ + b))) := by
    have h1 : (m ! : ℝ) * p⁻¹ ^ m ≤ ((m : ℝ) * Q) ^ m := by
      rw [mul_pow]
      gcongr
      · exact_mod_cast Nat.factorial_le_pow m
      · exact le_max_right _ _
    have h2 : ((m : ℝ) * Q) ^ m = exp (m * log (m * Q)) := by
      rw [← log_pow, exp_log (by positivity)]
    have hL : 1 ≤ log (‖s‖ + b) := one_le_log_of_three_le (by linarith [norm_nonneg s])
    have hlogQ : 0 ≤ log Q := log_nonneg hQ
    have h3 : (m : ℝ) * log (m * Q) ≤ (1 + log Q) * ((‖s‖ + b) * log (‖s‖ + b)) := by
      rw [log_mul (by positivity) (by positivity)]
      have e1 : (m : ℝ) * log m ≤ (‖s‖ + b) * log (‖s‖ + b) := ulogu_mono hm1 hm'
      have e2 : (m : ℝ) * log Q ≤ (‖s‖ + b) * log (‖s‖ + b) * log Q := by
        have : (m : ℝ) ≤ (‖s‖ + b) * log (‖s‖ + b) := by nlinarith
        exact mul_le_mul_of_nonneg_right this hlogQ
      nlinarith
    rw [h2] at h1
    exact h1.trans (exp_le_exp.2 h3)
  have hE : 0 ≤ C * max 1 ‖P.ε‖ := by positivity
  calc C * max 1 ‖P.ε‖ * m ! * p⁻¹ ^ m * I0 = C * max 1 ‖P.ε‖ * I0 * (m ! * p⁻¹ ^ m) := by ring
    _ ≤ _ := by gcongr

end Erdos985.Analytic.XiOrderAux
