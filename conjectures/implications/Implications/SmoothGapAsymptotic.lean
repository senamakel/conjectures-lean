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
open scoped Topology

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
      Real.log L / 4 := by field_simp [hR.ne'] <;> ring
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
  have hlog : ∀ᶠ L : ℝ in atTop, 1 ≤ Real.log L :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have heq : ∀ᶠ L : ℝ in atTop,
      L ^ (1 / 4 : ℝ) * Real.log L / rootScale L =
        Real.log L ^ (1 / 2 : ℝ) / L ^ (1 / 4 : ℝ) := by
    filter_upwards [hL, hlog] with L hL hlog
    have hLpos : 0 < L := by linarith
    have hlogpos : 0 < Real.log L := by linarith
    have hsqrt : rootScale L = Real.sqrt L * Real.sqrt (Real.log L) := by
      rw [rootScale, Real.sqrt_mul hLpos.le]
    have hLratio : L ^ (1 / 4 : ℝ) / Real.sqrt L =
        1 / L ^ (1 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      field_simp
      rw [← Real.rpow_mul_natCast hLpos.le (1 / 4 : ℝ) 2]
      norm_num
    have hlogratio : Real.log L / Real.sqrt (Real.log L) =
        Real.log L ^ (1 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      field_simp
      rw [← Real.rpow_mul_natCast hlogpos.le (1 / 2 : ℝ) 2]
      norm_num
    rw [hsqrt]
    calc
      _ = (L ^ (1 / 4 : ℝ) / Real.sqrt L) *
          (Real.log L / Real.sqrt (Real.log L)) := by ring
      _ = _ := by rw [hLratio, hlogratio]; ring
  have heq' : (fun L : ℝ => Real.log L ^ (1 / 2 : ℝ) / L ^ (1 / 4 : ℝ)) =ᶠ[atTop]
      (fun L => L ^ (1 / 4 : ℝ) * Real.log L / rootScale L) :=
    heq.mono fun _ h => h.symm
  exact Filter.Tendsto.congr' heq' hratio

/-- For any fixed multiplicative constant, the logarithmic cost remains
negligible compared with the stretched-exponential scale. -/
theorem eventually_const_mul_eulerCost_le_eighth_rootScale (D : ℝ) (hD : 0 < D) :
    ∀ᶠ L : ℝ in atTop,
      D * (L ^ (1 / 4 : ℝ) * Real.log L) ≤ rootScale L / 8 := by
  have hsmall := eulerCost_div_rootScale_tendsto_zero.eventually
    (Iio_mem_nhds (show 0 < 1 / (8 * D) by positivity))
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with L hcost hL
  have hroot : 0 < rootScale L := by
    apply Real.sqrt_pos.2
    exact mul_pos (by linarith) (Real.log_pos hL)
  have hcost' : L ^ (1 / 4 : ℝ) * Real.log L <
      (1 / (8 * D)) * rootScale L :=
    (div_lt_iff₀ hroot).mp hcost
  have hmul := mul_lt_mul_of_pos_left hcost' hD
  have heq : D * ((1 / (8 * D)) * rootScale L) = rootScale L / 8 := by
    field_simp
  rw [heq] at hmul
  exact hmul.le

/-- Eventually the logarithmic Euler-product cost is at most one eighth of
`R`, a convenient single bound for combining with Rankin and the reciprocal
prime product estimates. -/
theorem eventually_eulerCost_le_eighth_rootScale :
    ∀ᶠ L : ℝ in atTop,
      L ^ (1 / 4 : ℝ) * Real.log L ≤ rootScale L / 8 := by
  filter_upwards [eulerCost_div_rootScale_tendsto_zero.eventually
      (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 8)),
    eventually_gt_atTop (1 : ℝ)] with L hcost hL
  have hroot : 0 < rootScale L := by
    apply Real.sqrt_pos.2
    exact mul_pos (by linarith) (Real.log_pos hL)
  have h := (div_lt_iff₀ hroot).mp hcost
  nlinarith

end Implications.SmoothGapAsymptotic

#print axioms Implications.SmoothGapAsymptotic.rankinDelta_mul_self
#print axioms Implications.SmoothGapAsymptotic.exp_rankinDelta_log_smoothCutoff
#print axioms Implications.SmoothGapAsymptotic.eventually_const_mul_eulerCost_le_eighth_rootScale
#print axioms Implications.SmoothGapAsymptotic.eventually_eulerCost_le_eighth_rootScale
