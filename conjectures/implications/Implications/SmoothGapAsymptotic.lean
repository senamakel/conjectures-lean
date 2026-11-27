import Mathlib

/-!
# The asymptotic cutoff for smooth integers in prime gaps

For `L = log x`, set `R = sqrt (L * log L)`, `Y = exp (R / 2)`, and
`δ = log L / (2R)`. The identities below give the balance in Rankin's
argument: `δ L = R / 2`, while the Euler product's exponential weight is
`L ^ (1/4)`. Its logarithmic cost is little-o of `R`.
-/

namespace Implications.SmoothGapAsymptotic

open Filter

/-- The stretched-exponential scale `sqrt (L log L)`. -/
noncomputable def rootScale (L : ℝ) : ℝ := Real.sqrt (L * Real.log L)

/-- The Rankin exponent paired with `rootScale`. -/
noncomputable def rankinDelta (L : ℝ) : ℝ := Real.log L / (2 * rootScale L)

/-- The smoothness cutoff at half the stretched-exponential scale. -/
noncomputable def smoothCutoff (L : ℝ) : ℝ := Real.exp (rootScale L / 2)

/-- The square of the scale, for positive `L` with `log L ≥ 0`. -/
theorem rootScale_sq {L : ℝ} (hL : 0 < L) (hlog : 0 ≤ Real.log L) :
    rootScale L ^ 2 = L * Real.log L := by
  simp [rootScale, Real.sq_sqrt (mul_nonneg hL.le hlog)]

/-- Exact balance between the Rankin exponent and `log x = L`. -/
theorem rankinDelta_mul_self {L : ℝ} (hL : 1 < L) :
    rankinDelta L * L = rootScale L / 2 := by
  have hlog : 0 < Real.log L := Real.log_pos hL
  have hR : 0 < rootScale L := by
    apply Real.sqrt_pos.2
    exact mul_pos (by linarith) hlog
  have hsq := rootScale_sq (by linarith) hlog.le
  rw [rankinDelta]
  field_simp
  nlinarith [hsq]

/-- The Euler-product weight at the chosen cutoff is `L^(1/4)`. -/
theorem exp_rankinDelta_log_smoothCutoff {L : ℝ} (hL : 1 < L) :
    Real.exp (rankinDelta L * Real.log (smoothCutoff L)) = L ^ (1 / 4 : ℝ) := by
  have hlog : 0 < Real.log L := Real.log_pos hL
  have hR : 0 < rootScale L := by
    apply Real.sqrt_pos.2
    exact mul_pos (by linarith) hlog
  rw [smoothCutoff, Real.log_exp, rankinDelta]
  have hmul : Real.log L / (2 * rootScale L) * (rootScale L / 2) =
      Real.log L / 4 := by field_simp
  rw [hmul, Real.rpow_def_of_pos (by linarith : 0 < L)]
  congr 1
  ring

/-- The logarithmic Euler-product cost is negligible compared with the cutoff
scale. -/
theorem eulerCost_div_rootScale_tendsto_zero :
    Tendsto (fun L : ℝ => L ^ (1 / 4 : ℝ) * Real.log L / rootScale L)
      atTop (𝓝 0) := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (1 / 2 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have hratio : Tendsto (fun L : ℝ => Real.log L ^ (1 / 2 : ℝ) /
      L ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hsmall
  have hL : ∀ᶠ L : ℝ in atTop, 1 < L := eventually_gt_atTop 1
  have hlog : ∀ᶠ L : ℝ in atTop, 1 ≤ Real.log L := by
    filter_upwards [hL] with L hL
    exact Real.one_le_log_of_pos (by linarith) hL
  filter_upwards [hL, hlog] with L hL hlog
  have hroot : 0 < rootScale L := by
    apply Real.sqrt_pos.2
    exact mul_pos (by linarith) (by linarith)
  have hrootSq := rootScale_sq (by linarith) (by linarith)
  have hscale : L ^ (1 / 4 : ℝ) * Real.log L / rootScale L =
      (Real.log L ^ (1 / 2 : ℝ)) / (L ^ (1 / 4 : ℝ)) := by
    rw [Real.sqrt_eq_rpow] at hrootSq ⊢
    rw [Real.rpow_mul (by linarith : 0 < L)] at hrootSq
    rw [Real.rpow_mul (by linarith : 0 < Real.log L)] at hrootSq
    have hRpow : rootScale L = L ^ (1 / 2 : ℝ) * Real.log L ^ (1 / 2 : ℝ) := by
      rw [rootScale, Real.sqrt_eq_rpow, Real.rpow_mul (by positivity)]
      rw [Real.rpow_mul (by positivity)]
      congr 1 <;> ring
    rw [hRpow]
    rw [← Real.rpow_sub (by linarith : 0 < L)]
    rw [show (1 / 4 : ℝ) - 1 / 2 = -(1 / 4 : ℝ) by ring]
    rw [Real.rpow_neg (by linarith : 0 < L)]
    field_simp
    rw [Real.rpow_neg (by linarith : 0 < Real.log L)]
    field_simp
    ring
  rw [hscale]
  exact hratio

/-- Eventually the logarithmic Euler-product cost is at most one eighth of
`R`, a convenient single bound for combining with Rankin and the reciprocal
prime product estimates. -/
theorem eventually_eulerCost_le_eighth_rootScale :
    ∀ᶠ L : ℝ in atTop,
      L ^ (1 / 4 : ℝ) * Real.log L ≤ rootScale L / 8 := by
  filter_upwards [eulerCost_div_rootScale_tendsto_zero.eventually
    (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8))] with L hL
  have hroot : 0 < rootScale L := by
    apply Real.sqrt_pos.2
    filter_upwards [eventually_gt_atTop 1] with L h
    exact mul_pos (by linarith) (Real.log_pos h)
  exact (div_lt_iff₀ hroot).mp hL.le

end Implications.SmoothGapAsymptotic

#print axioms Implications.SmoothGapAsymptotic.rankinDelta_mul_self
#print axioms Implications.SmoothGapAsymptotic.exp_rankinDelta_log_smoothCutoff
#print axioms Implications.SmoothGapAsymptotic.eventually_eulerCost_le_eighth_rootScale
