import Robin.Main.Gain.Basic

/-! # The main integral `∫ t·v`

With `A = ∫ dt/(t² log t)`, `B = ∫ dt/(t² log² t)` we have `A + B = 1/(Y log Y) − 1/(x log x)`
(the integrand is the derivative of `−1/(t log t)`), `B ≤ A / log Y` and `∫ t v = 2A + B`. -/

namespace Robin.Gain

open Real Chebyshev

theorem main_integral {x Y : ℝ} (hY1 : 1 < Y) (hYx : Y ≤ x) (hL : 30 ≤ Real.log x)
    (hlY : Real.log x / 2 ≤ Real.log Y) :
    (1 / (Y * Real.log Y) - 1 / (x * Real.log x)) * (1 + Real.log x / (Real.log x + 2)) ≤
      ∫ t in Y..x, t * vW t := by
  set L := Real.log x with hLdef
  have hL0 : 0 < L := by linarith
  have hlY0 : 0 < Real.log Y := by linarith
  have hsub : Set.uIcc Y x ⊆ Set.Ioi 1 := by
    rw [Set.uIcc_of_le hYx]; intro t ht; exact lt_of_lt_of_le hY1 ht.1
  have hmem : ∀ t ∈ Set.uIcc Y x, 1 < t := fun t ht => hsub ht
  set h1 : ℝ → ℝ := fun t => 1 / (t ^ 2 * Real.log t) with hh1
  set h2 : ℝ → ℝ := fun t => 1 / (t ^ 2 * Real.log t ^ 2) with hh2
  have hc1 : ContinuousOn h1 (Set.uIcc Y x) := by
    intro t ht
    have ht1 := hmem t ht
    have ht0 : t ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.div ((continuousAt_id.pow 2).mul (continuousAt_log ht0))
      (mul_ne_zero (pow_ne_zero 2 ht0) (Real.log_pos ht1).ne')
  have hc2 : ContinuousOn h2 (Set.uIcc Y x) := by
    intro t ht
    have ht1 := hmem t ht
    have ht0 : t ≠ 0 := by positivity
    apply ContinuousAt.continuousWithinAt
    exact continuousAt_const.div ((continuousAt_id.pow 2).mul ((continuousAt_log ht0).pow 2))
      (mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 (Real.log_pos ht1).ne'))
  have hi1 : IntervalIntegrable h1 MeasureTheory.volume Y x := hc1.intervalIntegrable
  have hi2 : IntervalIntegrable h2 MeasureTheory.volume Y x := hc2.intervalIntegrable
  -- A + B = G₀
  have hAB : ∫ t in Y..x, (h1 t + h2 t) = 1 / (Y * Real.log Y) - 1 / (x * Real.log x) := by
    have hderiv : ∀ t ∈ Set.uIcc Y x,
        HasDerivAt (fun s => -(s * Real.log s)⁻¹) (h1 t + h2 t) t := by
      intro t ht
      have ht1 := hmem t ht
      have ht0 : t ≠ 0 := by positivity
      have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
      have hd : HasDerivAt (fun s => s * Real.log s) (1 * Real.log t + t * t⁻¹) t :=
        (hasDerivAt_id t).mul (Real.hasDerivAt_log ht0)
      have := (hd.inv (mul_ne_zero ht0 hl)).neg
      convert this using 1
      simp only [hh1, hh2]
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hi1.add hi2)]
    simp only [one_div]
    ring
  -- B ≤ A / log Y
  have hB : ∫ t in Y..x, h2 t ≤ (∫ t in Y..x, h1 t) / Real.log Y := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_mono_on hYx hi2 (hi1.div_const _)
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hY1 ht.1
    have hlt : Real.log Y ≤ Real.log t := Real.log_le_log (by linarith) ht.1
    have hl : 0 < Real.log t := Real.log_pos ht1
    simp only [hh1, hh2]
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have : t ^ 2 * Real.log t * Real.log Y ≤ t ^ 2 * Real.log t ^ 2 := by
      have : 0 ≤ t ^ 2 * Real.log t := by positivity
      nlinarith
    linarith
  have hA0 : 0 ≤ ∫ t in Y..x, h1 t := by
    apply intervalIntegral.integral_nonneg hYx
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le hY1 ht.1
    have := Real.log_pos ht1
    simp only [hh1]; positivity
  -- ∫ t v = 2A + B
  have htv : ∫ t in Y..x, t * vW t = 2 * (∫ t in Y..x, h1 t) + ∫ t in Y..x, h2 t := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add
      (hi1.const_mul 2) hi2]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht1 := hmem t ht
    have ht0 : t ≠ 0 := by positivity
    have hl : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    simp only [hh1, hh2, vW]
    field_simp
  rw [intervalIntegral.integral_add hi1 hi2] at hAB
  rw [htv, ← hAB]
  set A := ∫ t in Y..x, h1 t
  set B := ∫ t in Y..x, h2 t
  -- (A + B) * (1 + L/(L+2)) ≤ 2A + B, using B ≤ A/log Y ≤ 2A/L
  have hB' : B ≤ 2 * A / L := by
    refine hB.trans ?_
    rw [div_le_div_iff₀ hlY0 hL0]
    nlinarith
  have hLL : L / (L + 2) = 1 - 2 / (L + 2) := by field_simp; ring
  rw [hLL]
  have hpos : 0 < L + 2 := by linarith
  have key : (A + B) * (2 / (L + 2)) ≥ B := by
    rw [ge_iff_le, ← sub_nonneg]
    have : (A + B) * (2 / (L + 2)) - B = (2 * A - B * L) / (L + 2) := by
      field_simp; ring
    rw [this]
    apply div_nonneg _ hpos.le
    have := (le_div_iff₀ hL0).mp hB'
    nlinarith
  linarith
