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
  simp only [rankinDelta]
  rw [div_mul_eq_mul_div, ← mul_div_assoc]
  field_simp
  nlinarith [hsq]

/-- The Euler-product weight at the chosen cutoff is `L^(1/4)`. -/
theorem exp_rankinDelta_log_smoothCutoff {L : ℝ} (hL : 1 < L) :
    Real.exp (rankinDelta L * Real.log (smoothCutoff L)) = L ^ (1 / 4 : ℝ) := by
  have hlog : 0 < Real.log L := Real.log_pos hL
  have hR : 0 < rootScale L := by
    apply Real.sqrt_pos.2
    exact mul_pos (by linarith) hlog
  rw [smoothCutoff, Real.log_exp]
  have hsq := rootScale_sq (by linarith) hlog.le
  rw [rankinDelta]
  have hmul : Real.log L / (2 * rootScale L) * (rootScale L / 2) =
      Real.log L / 4 := by field_simp
  rw [hmul]
  rw [Real.rpow_def_of_pos (by linarith : 0 < L)]
  congr 1
  ring

/-- The logarithmic Euler-product cost is negligible compared with the cutoff
scale. -/
theorem eulerCost_div_rootScale_tendsto_zero :
    Tendsto (fun L : ℝ => L ^ (1 / 4 : ℝ) * Real.log L / rootScale L)
      atTop (𝓝 0) := by
  have hsmall := (isLittleO_log_rpow_rpow_atTop (1 / 2 : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 4)).tendsto_div_nhds_zero
  have hlarge : Tendsto (fun L : ℝ => L ^ (1 / 4 : ℝ)) atTop atTop := by
    exact Real.tendsto_rpow_atTop (by norm_num) (by norm_num)
  have hratio : Tendsto (fun L : ℝ => Real.log L / L ^ (1 / 4 : ℝ))
      atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hsmall
  have hL : ∀ᶠ L : ℝ in atTop, 1 < L := eventually_gt_atTop 1
  have hlog : ∀ᶠ L : ℝ in atTop, 0 < Real.log L :=
    hL.mono fun L h => Real.log_pos h
  have hroot : ∀ᶠ L : ℝ in atTop, 0 < rootScale L := by
    filter_upwards [hL] with L hL
    apply Real.sqrt_pos.2
    exact mul_pos (by linarith) (Real.log_pos hL)
  filter_upwards [hL, hlog, hroot] with L hL hlog hroot
  have hsq := rootScale_sq (by linarith) hlog.le
  have hroot_eq : rootScale L = (L * Real.log L) ^ (1 / 2 : ℝ) := by
    simp [rootScale, Real.sqrt_eq_rpow]
  rw [hroot_eq]
  have hratioL : L ^ (1 / 4 : ℝ) * Real.log L /
      (L * Real.log L) ^ (1 / 2 : ℝ) =
      (Real.log L / L ^ (1 / 4 : ℝ)) ^ (1 / 2 : ℝ) := by
    field_simp
    rw [Real.rpow_mul (by linarith : 0 < L), Real.rpow_mul (by linarith : 0 < Real.log L)]
    ring_nf
    rw [Real.sqrt_eq_rpow]
    congr 1
    ring
  rw [h ratioL]
