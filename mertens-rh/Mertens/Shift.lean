import Mathlib

/-!
# Step B: moving a vertical line integral across a strip

If `f` is holomorphic on the closed strip `a ≤ σ ≤ b`, integrable on both edges, and tends to
`0` uniformly in `σ` as `|t| → ∞`, then `∫ f(a + it) dt = ∫ f(b + it) dt`.

Proof: Cauchy's theorem on the rectangle `[a, b] × [-T, T]`
(`Complex.integral_boundary_rect_eq_zero_of_differentiableOn`); the horizontal sides are at most
`η (b - a)` and the vertical sides converge to the line integrals.
-/

namespace Mertens

open Complex MeasureTheory Filter Set Topology
open scoped Interval

theorem integral_vertical_eq_of_strip {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (ha : Integrable fun t : ℝ => f (a + t * I))
    (hb : Integrable fun t : ℝ => f (b + t * I))
    (hdec : ∀ η : ℝ, 0 < η → ∀ᶠ T : ℝ in atTop, ∀ σ : ℝ, a ≤ σ → σ ≤ b →
      ‖f (σ + T * I)‖ ≤ η ∧ ‖f (σ + ((-T : ℝ) : ℂ) * I)‖ ≤ η) :
    ∫ t : ℝ, f (a + t * I) = ∫ t : ℝ, f (b + t * I) := by
  set A := ∫ t : ℝ, f (a + t * I)
  set B := ∫ t : ℝ, f (b + t * I)
  set VA : ℝ → ℂ := fun T => ∫ t in (-T)..T, f (a + t * I)
  set VB : ℝ → ℂ := fun T => ∫ t in (-T)..T, f (b + t * I)
  set H : ℝ → ℂ := fun T =>
    (∫ x : ℝ in a..b, f (x + ((-T : ℝ) : ℂ) * I)) - ∫ x : ℝ in a..b, f (x + T * I)
  have hlimA : Tendsto VA atTop (𝓝 A) :=
    intervalIntegral_tendsto_integral ha tendsto_neg_atTop_atBot tendsto_id
  have hlimB : Tendsto VB atTop (𝓝 B) :=
    intervalIntegral_tendsto_integral hb tendsto_neg_atTop_atBot tendsto_id
  have hrect : ∀ T : ℝ, H T + I • VB T - I • VA T = 0 := by
    intro T
    have hsub : [[((a : ℂ) + ((-T : ℝ) : ℂ) * I).re, ((b : ℂ) + (T : ℂ) * I).re]] ×ℂ
        [[((a : ℂ) + ((-T : ℝ) : ℂ) * I).im, ((b : ℂ) + (T : ℂ) * I).im]] ⊆
        {s : ℂ | a ≤ s.re ∧ s.re ≤ b} := by
      intro s hs
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at hs
      rw [mem_reProdIm, uIcc_of_le hab] at hs
      exact hs.1
    have h := integral_boundary_rect_eq_zero_of_differentiableOn f _ _ (hf.mono hsub)
    simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      add_zero, add_im, mul_im, zero_add] at h
    simpa [H, VA, VB] using h
  have hH : Tendsto H atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro e he
    set η := e / (2 * (b - a) + 2) with hη
    have hη0 : 0 < η := by rw [hη]; apply div_pos he; linarith
    filter_upwards [hdec η hη0] with T hT
    rw [dist_zero_right]
    have h1 : ‖∫ x : ℝ in a..b, f (x + ((-T : ℝ) : ℂ) * I)‖ ≤ η * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => by
        rw [uIoc_of_le hab] at hx
        exact (hT x hx.1.le hx.2).2
    have h2 : ‖∫ x : ℝ in a..b, f (x + T * I)‖ ≤ η * |b - a| :=
      intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => by
        rw [uIoc_of_le hab] at hx
        exact (hT x hx.1.le hx.2).1
    have habs : |b - a| = b - a := abs_of_nonneg (by linarith)
    calc ‖H T‖ ≤ η * |b - a| + η * |b - a| := (norm_sub_le _ _).trans (add_le_add h1 h2)
      _ = 2 * (b - a) * η := by rw [habs]; ring
      _ < e := by
        rw [hη, mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  have h1 : Tendsto (fun T => I • (VB T - VA T)) atTop (𝓝 (I • (B - A))) :=
    (hlimB.sub hlimA).const_smul I
  have h2 : (fun T => I • (VB T - VA T)) = fun T => -H T := by
    funext T
    have := hrect T
    rw [smul_sub]
    linear_combination this
  rw [h2] at h1
  have h3 := tendsto_nhds_unique h1 (by simpa using hH.neg)
  have : B - A = 0 := by
    rcases smul_eq_zero.mp h3 with h | h
    · exact absurd h I_ne_zero
    · exact h
  exact (sub_eq_zero.mp this).symm

end Mertens
