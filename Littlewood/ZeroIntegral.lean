import Mathlib

/-!
# Step 7: one zero, integrated over `σ ∈ [σ₀, 2]`

For a zero `ρ = 1/2 + iγ`, `s(σ) = σ + it` and `b(σ) = ρ - s(σ)`:

    ∫_{σ₀}^{2} Re ((x^{b} - 1)/b²) dσ ≤ Re 1/(s(2) - ρ)        if (σ₀ - 1/2) log x ≥ 1.

The `-1/b²` part integrates exactly to `Re 1/(s(2)-ρ) - Re 1/(s(σ₀)-ρ)` (antiderivative `1/b`),
and the `x^b/b²` part is at most `∫ x^{1/2-σ} dσ / |s(σ₀)-ρ|² ≤ 1/(log x |s(σ₀)-ρ|²)`, which is
`≤ Re 1/(s(σ₀)-ρ) = (σ₀ - 1/2)/|s(σ₀)-ρ|²` exactly when `(σ₀ - 1/2) log x ≥ 1`. This is where
the positivity of `Re 1/(s-ρ)` under RH absorbs the zeros near `t`.
-/

open Complex MeasureTheory intervalIntegral

namespace Littlewood

lemma sub_line_ne_zero {ρ : ℂ} (hρ : ρ.re = 1 / 2) {σ : ℝ} (hσ : 1 / 2 < σ) (t : ℝ) :
    ρ - ((σ : ℂ) + t * I) ≠ 0 := fun h => by
  have := congrArg re h; simp [hρ] at this; linarith

lemma normSq_sub_line_mono {ρ : ℂ} (hρ : ρ.re = 1 / 2) {σ₀ σ : ℝ} (h0 : 1 / 2 ≤ σ₀)
    (h : σ₀ ≤ σ) (t : ℝ) :
    normSq (ρ - ((σ₀ : ℂ) + t * I)) ≤ normSq (ρ - ((σ : ℂ) + t * I)) := by
  simp only [normSq_apply, sub_re, sub_im, add_re, add_im, ofReal_re, ofReal_im, mul_re, mul_im,
    I_re, I_im, hρ]
  nlinarith

/-- `∫_{σ₀}^{2} x^{1/2-σ} dσ ≤ 1 / log x` for `x > 1`. -/
lemma integral_rpow_le {x σ₀ : ℝ} (hx : 1 < x) (h0 : 1 / 2 ≤ σ₀) (_h2 : σ₀ ≤ 2) :
    ∫ σ in σ₀..2, x ^ (1 / 2 - σ) ≤ 1 / Real.log x := by
  have hL : 0 < Real.log x := Real.log_pos hx
  have hx0 : 0 < x := by linarith
  have hd : ∀ σ ∈ Set.uIcc σ₀ 2, HasDerivAt (fun σ : ℝ => -(x ^ (1 / 2 - σ)) / Real.log x)
      (x ^ (1 / 2 - σ)) σ := by
    intro σ _
    have h1 : HasDerivAt (fun σ : ℝ => (1 / 2 : ℝ) - σ) (-1) σ := by
      simpa using (hasDerivAt_id σ).const_sub (1 / 2 : ℝ)
    have h2 := (h1.const_rpow hx0)
    convert (h2.neg).div_const (Real.log x) using 1
    field_simp
  rw [integral_eq_sub_of_hasDerivAt hd]
  · have hp1 : 0 ≤ x ^ (1 / 2 - (2 : ℝ)) := Real.rpow_nonneg hx0.le _
    have hp2 : x ^ (1 / 2 - σ₀) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx.le (by linarith)
    rw [div_sub_div_same, div_le_div_iff_of_pos_right hL]
    linarith
  · exact (continuous_const.rpow (continuous_const.sub continuous_id) fun _ => Or.inl hx0.ne').intervalIntegrable _ _

/-- **One zero, integrated.** -/
theorem integral_zero_term_le {ρ : ℂ} (hρ : ρ.re = 1 / 2) (t : ℝ) {x σ₀ : ℝ} (hx : 1 < x)
    (h0 : 1 / 2 < σ₀) (h2 : σ₀ ≤ 2) (hηL : 1 ≤ (σ₀ - 1 / 2) * Real.log x) :
    ∫ σ in σ₀..2, ((((x : ℂ) ^ (ρ - ((σ : ℂ) + t * I)) - 1) / (ρ - ((σ : ℂ) + t * I)) ^ 2)).re
      ≤ (1 / ((2 : ℂ) + t * I - ρ)).re := by
  have hx0 : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos hx
  set c : ℂ := ρ - t * I with hc
  have hb : ∀ σ : ℝ, ρ - ((σ : ℂ) + t * I) = c - σ := fun σ => by rw [hc]; ring
  have hne : ∀ σ : ℝ, 1 / 2 < σ → c - σ ≠ 0 := fun σ hσ => by
    rw [← hb]; exact sub_line_ne_zero hρ hσ t
  have hsub : Set.uIcc σ₀ 2 ⊆ Set.Ioi (1 / 2) := by
    intro σ hσ; rw [Set.uIcc_of_le h2] at hσ; exact lt_of_lt_of_le h0 hσ.1
  -- continuity of the two pieces on `[σ₀, 2]`
  have hcl : Continuous fun σ : ℝ => c - (σ : ℂ) := continuous_const.sub continuous_ofReal
  have hcl2 : Continuous fun σ : ℝ => (c - (σ : ℂ)) ^ 2 := hcl.pow 2
  have hcp : Continuous fun σ : ℝ => (x : ℂ) ^ (c - (σ : ℂ)) :=
    hcl.const_cpow (Or.inl (by exact_mod_cast hx0.ne'))
  have hcont1 : ContinuousOn (fun σ : ℝ => (1 / (c - σ) ^ 2 : ℂ)) (Set.uIcc σ₀ 2) :=
    ContinuousOn.div (f := fun _ => (1 : ℂ)) (g := fun σ : ℝ => (c - (σ : ℂ)) ^ 2)
      continuousOn_const hcl2.continuousOn fun σ hσ => pow_ne_zero 2 (hne σ (hsub hσ))
  have hcont2 : ContinuousOn (fun σ : ℝ => ((x : ℂ) ^ (c - σ) / (c - σ) ^ 2 : ℂ)) (Set.uIcc σ₀ 2) :=
    ContinuousOn.div (f := fun σ : ℝ => (x : ℂ) ^ (c - (σ : ℂ)))
      (g := fun σ : ℝ => (c - (σ : ℂ)) ^ 2) hcp.continuousOn hcl2.continuousOn
      fun σ hσ => pow_ne_zero 2 (hne σ (hsub hσ))
  have hsplit : ∀ σ : ℝ, ((((x : ℂ) ^ (ρ - ((σ : ℂ) + t * I)) - 1) / (ρ - ((σ : ℂ) + t * I)) ^ 2)).re
      = ((x : ℂ) ^ (c - σ) / (c - σ) ^ 2).re - (1 / (c - σ) ^ 2 : ℂ).re := by
    intro σ; rw [hb, sub_div, sub_re, one_div]
  simp_rw [hsplit]
  have hi1 : IntervalIntegrable (fun σ : ℝ => (1 / (c - σ) ^ 2 : ℂ).re) volume σ₀ 2 :=
    (continuous_re.comp_continuousOn hcont1).intervalIntegrable
  have hi2 : IntervalIntegrable (fun σ : ℝ => ((x : ℂ) ^ (c - σ) / (c - σ) ^ 2).re) volume σ₀ 2 :=
    (continuous_re.comp_continuousOn hcont2).intervalIntegrable
  rw [integral_sub hi2 hi1]
  -- the exact part
  have hexact : ∫ σ in σ₀..2, (1 / (c - σ) ^ 2 : ℂ).re
      = (1 / (c - 2)).re - (1 / (c - σ₀)).re := by
    refine integral_eq_sub_of_hasDerivAt (f := fun σ : ℝ => (1 / (c - σ)).re) (fun σ hσ => ?_) hi1
    have hz : c - (σ : ℂ) ≠ 0 := hne σ (hsub hσ)
    have hd : HasDerivAt (fun z : ℂ => 1 / (c - z)) (1 / (c - σ) ^ 2) (σ : ℂ) := by
      have := ((hasDerivAt_id (σ : ℂ)).const_sub c).inv hz
      convert this using 1
      · funext z; simp
      · simp
    exact hd.real_of_complex
  rw [hexact]
  -- the `x^b` part
  set d0 := normSq (ρ - ((σ₀ : ℂ) + t * I)) with hd0
  have hd0pos : 0 < d0 := normSq_pos.2 (sub_line_ne_zero hρ h0 t)
  have hbound : ∀ σ ∈ Set.Icc σ₀ 2, ((x : ℂ) ^ (c - σ) / (c - σ) ^ 2).re ≤ x ^ (1 / 2 - σ) / d0 := by
    intro σ hσ
    refine (re_le_norm _).trans ?_
    rw [norm_div, norm_pow, norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (c - σ).re = 1 / 2 - σ := by simp [hc, hρ]
    rw [hre, ← hb σ, ← Complex.normSq_eq_norm_sq]
    exact div_le_div_of_nonneg_left (Real.rpow_nonneg hx0.le _) hd0pos
      (normSq_sub_line_mono hρ h0.le hσ.1 t)
  have hint2 : ∫ σ in σ₀..2, ((x : ℂ) ^ (c - σ) / (c - σ) ^ 2).re ≤ 1 / Real.log x / d0 := by
    calc ∫ σ in σ₀..2, ((x : ℂ) ^ (c - σ) / (c - σ) ^ 2).re
        ≤ ∫ σ in σ₀..2, x ^ (1 / 2 - σ) / d0 := by
          refine integral_mono_on h2 hi2 ?_ hbound
          exact ((continuous_const.rpow (continuous_const.sub continuous_id)
            fun _ => Or.inl hx0.ne').div_const _).intervalIntegrable _ _
      _ = (∫ σ in σ₀..2, x ^ (1 / 2 - σ)) / d0 := by rw [intervalIntegral.integral_div]
      _ ≤ 1 / Real.log x / d0 := by
          gcongr; exact integral_rpow_le hx h0.le h2
  -- `Re 1/(c - σ₀) = -(σ₀ - 1/2)/d0`
  have hre0 : (1 / (c - σ₀)).re = -((σ₀ - 1 / 2) / d0) := by
    rw [← hb σ₀, one_div, inv_re]
    simp [hρ, hd0]
    ring
  have hre2 : (1 / (c - 2)).re = -(1 / ((2 : ℂ) + t * I - ρ)).re := by
    rw [show c - 2 = -((2 : ℂ) + t * I - ρ) by rw [hc]; ring, one_div, one_div, inv_neg, neg_re]
  rw [hre0, hre2]
  have key : 1 / Real.log x / d0 ≤ (σ₀ - 1 / 2) / d0 := by
    gcongr
    rw [div_le_iff₀ hL]; linarith
  linarith

end Littlewood
