import Robin.RH.Psi1
import Robin.Mertens.Identity

/-!
# The tail `∫_x^∞ (t − θ(t)) w(t) dt` for `x ≥ e^{30}`

`t − θ = (t − ψ) + (ψ − θ)`. The first part is integrated by parts against `E = Ψ₁ − t²/2`
(`|E(t)| ≤ t^{3/2}/20 + 4t`, right derivative `ψ(t) − t`), giving `≤ 0.32/(√x log x)`. The second
uses `ψ − θ ≤ ψ(√t) + ψ(t^{1/3}) + ψ(t^{1/5})` and `ψ(s) ≤ s + s^{3/4}`; its main part is
`∫_x^∞ √t w(t) dt ≤ (31/30)·2/(√x log x)`.
-/

namespace Robin

open Filter Topology Real Chebyshev MeasureTheory Set

/-- `w(t) ≤ (31/30)/(L t²)` when `log t ≥ L ≥ 30`. -/
lemma wM_le_of_log {t L : ℝ} (hL : 30 ≤ L) (ht0 : 0 < t) (ht : L ≤ Real.log t) :
    wM t ≤ (31 / 30) / (L * t ^ 2) := by
  have hl : 0 < Real.log t := by linarith
  have hL0 : 0 < L := by linarith
  unfold wM
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : L * (1 + Real.log t) ≤ (31 / 30) * Real.log t ^ 2 := by nlinarith
  have ht2 : 0 < t ^ 2 := by positivity
  calc (1 + Real.log t) * (L * t ^ 2) = t ^ 2 * (L * (1 + Real.log t)) := by ring
    _ ≤ t ^ 2 * ((31 / 30) * Real.log t ^ 2) := mul_le_mul_of_nonneg_left h1 ht2.le
    _ = 31 / 30 * (t ^ 2 * Real.log t ^ 2) := by ring

/-- The derivative of `w`. -/
noncomputable def wM' (t : ℝ) : ℝ :=
  -(2 * Real.log t ^ 2 + 3 * Real.log t + 2) / (t ^ 3 * Real.log t ^ 3)

lemma hasDerivAt_wM {t : ℝ} (ht : 1 < t) : HasDerivAt wM (wM' t) t := by
  have ht0 : 0 < t := by linarith
  have hl : 0 < Real.log t := Real.log_pos ht
  have hN : HasDerivAt (fun u => 1 + Real.log u) (1 / t) t := by
    simpa using (Real.hasDerivAt_log ht0.ne').const_add 1
  have hD : HasDerivAt (fun u => u ^ 2 * Real.log u ^ 2)
      (2 * t * Real.log t ^ 2 + t ^ 2 * (2 * Real.log t * (1 / t))) t := by
    have h1 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 : HasDerivAt (fun u => Real.log u ^ 2) (2 * Real.log t * (1 / t)) t := by
      have h := (Real.hasDerivAt_log ht0.ne').mul (Real.hasDerivAt_log ht0.ne')
      have e : (fun u => Real.log u ^ 2) = fun u => Real.log u * Real.log u := by
        funext u; ring
      rw [e]; convert h using 1; field_simp; ring
    exact h1.mul h2
  have hDn : t ^ 2 * Real.log t ^ 2 ≠ 0 := by positivity
  have := hN.div hD hDn
  unfold wM
  convert this using 1
  unfold wM'
  field_simp
  ring

lemma abs_wM'_le {t L : ℝ} (hL : 30 ≤ L) (ht0 : 0 < t) (ht : L ≤ Real.log t) :
    |wM' t| ≤ 2.103 / (L * t ^ 3) := by
  have hl : 0 < Real.log t := by linarith
  have hL0 : 0 < L := by linarith
  unfold wM'
  rw [abs_div, abs_neg, abs_of_pos (by positivity), abs_of_pos (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  set l := Real.log t
  have h1 : L * (2 * l ^ 2 + 3 * l + 2) ≤ 2.103 * l ^ 3 := by
    have : L * (2 * l ^ 2 + 3 * l + 2) ≤ l * (2 * l ^ 2 + 3 * l + 2) :=
      mul_le_mul_of_nonneg_right ht (by positivity)
    nlinarith
  have ht3 : 0 < t ^ 3 := by positivity
  calc (2 * l ^ 2 + 3 * l + 2) * (L * t ^ 3) = t ^ 3 * (L * (2 * l ^ 2 + 3 * l + 2)) := by ring
    _ ≤ t ^ 3 * (2.103 * l ^ 3) := mul_le_mul_of_nonneg_left h1 ht3.le
    _ = 2.103 * (t ^ 3 * l ^ 3) := by ring

/-- `E(t) = Ψ₁(t) − t²/2`. -/
noncomputable def E1 (t : ℝ) : ℝ := psi1 t - t ^ 2 / 2

lemma E1_hasDerivWithinAt (t : ℝ) : HasDerivWithinAt E1 (ψ t - t) (Ioi t) t := by
  have h2 : HasDerivWithinAt (fun u : ℝ => u ^ 2 / 2) t (Ioi t) t := by
    have := ((hasDerivAt_pow 2 t).div_const 2).hasDerivWithinAt (s := Ioi t)
    convert this using 1; push_cast; ring
  exact (psi1_hasDerivWithinAt t).sub h2

lemma E1_continuous : Continuous E1 := by
  unfold E1; exact psi1_continuous.sub (by fun_prop)

lemma psi_intervalIntegrable (a b : ℝ) : IntervalIntegrable ψ volume a b :=
  psi_mono.intervalIntegrable

/-- Integration by parts: `∫_x^y (t − ψ) w = E(x)w(x) − E(y)w(y) + ∫_x^y E w'`. -/
lemma integral_sub_psi_wM {x y : ℝ} (hx : 1 < x) (hxy : x ≤ y) :
    ∫ t in x..y, (t - ψ t) * wM t = E1 x * wM x - E1 y * wM y + ∫ t in x..y, E1 t * wM' t := by
  have hcw : ContinuousOn wM (Icc x y) := continuousOn_wM hx
  have hcw' : ContinuousOn wM' (Icc x y) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hl : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    unfold wM'
    exact ((((continuousAt_log ht0).pow 2).const_mul 2).add
      ((continuousAt_log ht0).const_mul 3) |>.add continuousAt_const).neg.div
      ((continuousAt_id.pow 3).mul ((continuousAt_log ht0).pow 3))
      (mul_ne_zero (pow_ne_zero 3 ht0) (pow_ne_zero 3 hl)) |>.continuousWithinAt
  have hu' : IntervalIntegrable (fun t => ψ t - t) volume x y :=
    (psi_intervalIntegrable x y).sub (continuous_id.intervalIntegrable _ _)
  have hv' : IntervalIntegrable wM' volume x y :=
    (hcw'.intervalIntegrable_of_Icc hxy)
  have hibp := intervalIntegral.integral_deriv_mul_eq_sub_of_hasDeriv_right
    (u := E1) (v := wM) (u' := fun t => ψ t - t) (v' := wM') (a := x) (b := y)
    E1_continuous.continuousOn (by rw [uIcc_of_le hxy]; exact hcw)
    (fun t _ => E1_hasDerivWithinAt t)
    (fun t ht => by
      rw [min_eq_left hxy] at ht
      exact (hasDerivAt_wM (by linarith [ht.1])).hasDerivWithinAt) hu' hv'
  have hi1 : IntervalIntegrable (fun t => (ψ t - t) * wM t) volume x y :=
    hu'.mul_continuousOn (by rw [uIcc_of_le hxy]; exact hcw)
  have hi2 : IntervalIntegrable (fun t => E1 t * wM' t) volume x y :=
    (E1_continuous.continuousOn.mul hcw').intervalIntegrable_of_Icc hxy
  rw [intervalIntegral.integral_add hi1 hi2] at hibp
  have hneg : ∫ t in x..y, (t - ψ t) * wM t = -∫ t in x..y, (ψ t - t) * wM t := by
    rw [← intervalIntegral.integral_neg]; congr 1; ext t; ring
  rw [hneg]
  linarith

end Robin
