import Mathlib

/-!
# `L(s, χ) = exp(∑ χ(n) Λ(n) / log n · n^{-s})` for `Re s > 1`

`logLCoeff χ n = χ(n) Λ(n) / log n` are the coefficients of `log L(s, χ)`. Both
`L(s, χ)` and `exp(L(logLCoeff χ, s))` have logarithmic derivative `-L(χΛ, s)` on the half-plane
`Re s > 1` (Mathlib's `LSeries_twist_vonMangoldt_eq`), and both tend to `1` as `s → +∞`, so they
are equal (`LSeries_eq_exp_logLCoeff`). This is the argument of artin-grh's
`Artin.Analytic.dedekindZeta_eq_exp`, applied to a Dirichlet character.
-/

namespace AbelianERH

open Complex Filter Topology ArithmeticFunction LSeries
open scoped LSeries.notation

variable {N : ℕ}

/-- The coefficients `χ(n) Λ(n) / log n` of `log L(s, χ)`. -/
noncomputable def logLCoeff (χ : DirichletCharacter ℂ N) (n : ℕ) : ℂ :=
  χ n * ((Λ n / Real.log n : ℝ) : ℂ)

lemma vonMangoldt_div_log_nonneg (n : ℕ) : 0 ≤ Λ n / Real.log n :=
  div_nonneg vonMangoldt_nonneg (Real.log_natCast_nonneg n)

lemma vonMangoldt_div_log_le_one (n : ℕ) : Λ n / Real.log n ≤ 1 := by
  rcases (Real.log_natCast_nonneg n).lt_or_eq with h | h
  · rw [div_le_one h]; exact vonMangoldt_le_log
  · rw [← h, div_zero]; exact zero_le_one

lemma norm_logLCoeff_le (χ : DirichletCharacter ℂ N) (n : ℕ) : ‖logLCoeff χ n‖ ≤ 1 := by
  unfold logLCoeff
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (vonMangoldt_div_log_nonneg n)]
  calc _ ≤ 1 * 1 := mul_le_mul (DirichletCharacter.norm_le_one χ _)
          (vonMangoldt_div_log_le_one n) (vonMangoldt_div_log_nonneg n) zero_le_one
    _ = 1 := one_mul 1

lemma LSeriesSummable_logLCoeff (χ : DirichletCharacter ℂ N) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (logLCoeff χ) s := by
  refine Summable.of_norm_bounded (LSeriesSummable_one_iff.2 hs).norm fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq, ite_eq_right hn, ite_eq_right hn, Pi.one_apply, norm_one]
  gcongr
  exact norm_logLCoeff_le χ n

lemma abscissaOfAbsConv_logLCoeff_le (χ : DirichletCharacter ℂ N) :
    abscissaOfAbsConv (logLCoeff χ) ≤ 1 :=
  abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    LSeriesSummable_logLCoeff χ (by simpa using hy)

lemma logMul_logLCoeff (χ : DirichletCharacter ℂ N) {n : ℕ} (hn : n ≠ 0) :
    logMul (logLCoeff χ) n = (↗χ * ↗Λ) n := by
  simp only [logMul, logLCoeff, Pi.mul_apply]
  rcases eq_or_ne n 1 with rfl | h1
  · simp
  have hlog : Real.log n ≠ 0 := by
    have : (1 : ℝ) < n := by exact_mod_cast (Nat.one_lt_iff_ne_zero_and_ne_one.2 ⟨hn, h1⟩)
    exact (Real.log_pos this).ne'
  have hlog' : ((Real.log n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hlog
  rw [← Complex.natCast_log, Complex.ofReal_div]
  field_simp

/-- **`L(s, χ) = exp(∑ χ(n) Λ(n) / log n · n^{-s})` for `Re s > 1`.** -/
theorem LSeries_eq_exp_logLCoeff [NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ}
    (hs : 1 < s.re) : LSeries ↗χ s = exp (LSeries (logLCoeff χ) s) := by
  set U : Set ℂ := {s | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt 1).isPreconnected
  have habs : ∀ s ∈ U, abscissaOfAbsConv ↗χ < s.re := fun s hs => by
    rw [DirichletCharacter.abscissaOfAbsConv_eq_one (NeZero.ne N)]
    exact_mod_cast hs
  set F : ℂ → ℂ := fun s => LSeries ↗χ s * exp (-LSeries (logLCoeff χ) s)
  have hL : ∀ s ∈ U, HasDerivAt (LSeries ↗χ) (-(LSeries (↗χ * ↗Λ) s * LSeries ↗χ s)) s := by
    intro s hs
    have h := LSeries_hasDerivAt (habs s hs)
    have h0 := DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ (s := s) hs
    rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs, div_mul_cancel₀ _ h0, neg_neg]
    exact h.differentiableAt.hasDerivAt
  have hG : ∀ s ∈ U, HasDerivAt (LSeries (logLCoeff χ)) (-LSeries (↗χ * ↗Λ) s) s := by
    intro s hs
    have h := LSeries_hasDerivAt ((abscissaOfAbsConv_logLCoeff_le χ).trans_lt
      (show ((1 : ℝ) : EReal) < s.re by exact_mod_cast hs))
    rwa [LSeries_congr (fun hn => logMul_logLCoeff χ hn)] at h
  have hF : ∀ s ∈ U, HasDerivAt F 0 s := by
    intro s hs
    have h := (hL s hs).mul ((hG s hs).neg.cexp)
    convert h using 1
    ring
  obtain ⟨c, hc⟩ := hU.exists_is_const_of_deriv_eq_zero hUc
    (fun s hs => (hF s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hF s hs).deriv)
  have hlim : Tendsto (fun x : ℝ => F x) atTop (𝓝 (1 * exp (-0))) := by
    have h1 := LSeries.tendsto_atTop (f := ↗χ)
      ((habs 2 (by norm_num [U])).trans (EReal.coe_lt_top _))
    have h2 := LSeries.tendsto_atTop ((abscissaOfAbsConv_logLCoeff_le χ).trans_lt
      (EReal.coe_lt_top 1))
    simp only [logLCoeff, Nat.cast_one, map_one, vonMangoldt_apply_one, Real.log_one,
      div_zero, Complex.ofReal_zero, mul_zero] at h1 h2
    exact h1.mul (h2.neg.cexp)
  have hc1 : c = 1 := by
    have : Tendsto (fun x : ℝ => F x) atTop (𝓝 c) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_gt_atTop 1] with x hx
      exact (hc x (by simpa [U] using hx)).symm
    rw [tendsto_nhds_unique this hlim]
    simp
  have := hc s hs
  rw [hc1] at this
  calc LSeries ↗χ s = F s * exp (LSeries (logLCoeff χ) s) := by
        simp only [F, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero, mul_one]
    _ = _ := by rw [this, one_mul]

end AbelianERH
