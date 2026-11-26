import Erdos233.RH
import Erdos233.Explicit.Formula

/-!
# Step 2. The second difference of `psi1` through the explicit formula

For real `y ≥ 1` (erdos-985's `explicit_formula_zeta` is stated for natural `x` only; the real
version is `ExplicitAux.explicit_formula_real` in `Erdos233/Explicit/Formula.lean`):

`psi1 y = y²/2 + y log y − 7y/2 + 3 − (y − 1) ζ'/ζ(2) + y·G(y) + Σ_ρ m_ρ y·zeroTerm(y, ρ)`

with `|Re G(y) + log y − 1| ≤ 3/(2y)`, `Im G(y) = 0`. Taking the second difference at
`y, y(1+δ), y(1+2δ)` kills the affine terms, leaves `δ²y²` from `y²/2`, at most `6` from
`y log y + y G(y)`, and `−y^{ρ+1} coef δ ρ` from each zero. Under RH `|y^{ρ+1}| = y^{3/2}`.
-/

namespace Erdos233

open Complex ArithmeticFunction Erdos985.Analytic ExplicitAux

lemma psi1_eq_mul (t : ℝ) (ht : 0 < t) :
    psi1 t = t * ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (Λ n : ℝ) * (1 - (n : ℝ) / t) := by
  unfold psi1
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  field_simp

/-- `psi1` at real `t ≥ 1` through the explicit formula. -/
lemma psi1_formula (t : ℝ) (ht : 1 ≤ t) :
    Summable (fun ρ : Zeros => (mult ρ : ℂ) * ((t : ℂ) * zeroTermR t ρ)) ∧
    ((psi1 t : ℝ) : ℂ) = (∑' ρ : Zeros, (mult ρ : ℂ) * ((t : ℂ) * zeroTermR t ρ))
      + ((t * ((gammaPartR t).re + Real.log t) : ℝ) : ℂ)
      + ((t : ℂ) ^ 2 / 2 - 7 / 2 * t + 3)
      - ((t : ℂ) - 1) * (deriv riemannZeta 2 / riemannZeta 2) := by
  obtain ⟨hs, he⟩ := explicit_formula_real t ht
  have ht0 : (0 : ℝ) < t := by linarith
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht0.ne'
  obtain ⟨him, -, -⟩ := gammaPartR_bound t ht
  set g := (gammaPartR t).re with hgdef
  have hg : gammaPartR t = (g : ℂ) := by apply Complex.ext <;> simp [him, g]
  have hfun : (fun ρ : Zeros => (mult ρ : ℂ) * ((t : ℂ) * zeroTermR t ρ))
      = fun ρ : Zeros => (t : ℂ) * ((analyticOrderNatAt xiZeta ρ : ℂ) * zeroTermR t ρ) := by
    funext ρ
    simp only [mult]
    ring
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hs.mul_left _
  · rw [hfun, tsum_mul_left, psi1_eq_mul t ht0, ofReal_mul, he, hg]
    push_cast
    field_simp
    ring

lemma t_zeroTermR (t : ℝ) (ht : 0 < t) (ρ : ℂ) :
    (t : ℂ) * zeroTermR t ρ
      = ((t : ℂ) - 1) / (2 - ρ) - (t : ℂ) ^ (ρ + 1) / (ρ * (ρ + 1)) + t / ρ - 1 / (1 + ρ) := by
  have htc : (t : ℂ) ≠ 0 := ofReal_ne_zero.2 ht.ne'
  have h1 : (t : ℂ) * (t : ℂ)⁻¹ = 1 := mul_inv_cancel₀ htc
  unfold zeroTermR
  rw [cpow_add _ _ htc, cpow_one, cpow_neg_one]
  linear_combination (-(1 / (2 - ρ) + 1 / (1 + ρ))) * h1

lemma second_diff_zero (y δ : ℝ) (hy : 0 < y) (hδ : 0 < δ) (ρ : ℂ) :
    ((y * (1 + 2 * δ) : ℝ) : ℂ) * zeroTermR (y * (1 + 2 * δ)) ρ
      - 2 * (((y * (1 + δ) : ℝ) : ℂ) * zeroTermR (y * (1 + δ)) ρ)
      + (y : ℂ) * zeroTermR y ρ
      = -((y : ℂ) ^ (ρ + 1) * coef δ ρ) := by
  rw [t_zeroTermR _ (by positivity), t_zeroTermR _ (by positivity), t_zeroTermR _ hy]
  have e1 : (((y * (1 + 2 * δ)) : ℝ) : ℂ) ^ (ρ + 1)
      = (y : ℂ) ^ (ρ + 1) * ((1 + 2 * δ : ℝ) : ℂ) ^ (ρ + 1) := by
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hy.le (by positivity)]
  have e2 : (((y * (1 + δ)) : ℝ) : ℂ) ^ (ρ + 1)
      = (y : ℂ) ^ (ρ + 1) * ((1 + δ : ℝ) : ℂ) ^ (ρ + 1) := by
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hy.le (by positivity)]
  unfold coef
  rw [e1, e2]
  push_cast
  ring

lemma th_bounds (t : ℝ) (ht : 1 ≤ t) :
    t - 3 / 2 ≤ t * ((gammaPartR t).re + Real.log t) ∧
      t * ((gammaPartR t).re + Real.log t) ≤ t := by
  obtain ⟨-, l, u⟩ := gammaPartR_bound t ht
  have ht0 : (0 : ℝ) < t := by linarith
  constructor
  · have h := mul_le_mul_of_nonneg_left l ht0.le
    have e : t * (1 - 3 / (2 * t)) = t - 3 / 2 := by field_simp
    linarith
  · have h := mul_le_mul_of_nonneg_left u ht0.le
    rwa [mul_one] at h

lemma cpow_succ_of_RH (hRH : RiemannHypothesis) {y : ℝ} (hy : 0 < y) (ρ : Zeros) :
    (y : ℂ) ^ ((ρ : ℂ) + 1)
      = ((y ^ (3 / 2 : ℝ) : ℝ) : ℂ) * exp ((((ρ : ℂ).im * Real.log y : ℝ) : ℂ) * I) := by
  have hre := zero_re_of_RH hRH ρ
  have hyc : (y : ℂ) ≠ 0 := ofReal_ne_zero.2 hy.ne'
  have hs : (ρ : ℂ) + 1 = ((3 / 2 : ℝ) : ℂ) + (((ρ : ℂ).im : ℝ) : ℂ) * I := by
    apply Complex.ext <;> norm_num [hre]
  rw [hs, cpow_add _ _ hyc, ← ofReal_cpow hy.le]
  congr 1
  rw [cpow_def_of_ne_zero hyc, ← ofReal_log hy.le]
  congr 1
  push_cast
  ring

theorem D2_bound (hRH : RiemannHypothesis) {δ y : ℝ} (hδ : 0 < δ) (hy : 1 ≤ y) :
    |D2 δ y - δ ^ 2 * y ^ 2| ≤ 6 + y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖ := by
  have hy0 : (0 : ℝ) < y := by linarith
  have h2 : 1 ≤ y * (1 + δ) := by nlinarith
  have h3 : 1 ≤ y * (1 + 2 * δ) := by nlinarith
  obtain ⟨s1, e1⟩ := psi1_formula y hy
  obtain ⟨s2, e2⟩ := psi1_formula _ h2
  obtain ⟨s3, e3⟩ := psi1_formula _ h3
  obtain ⟨l1, u1⟩ := th_bounds y hy
  obtain ⟨l2, u2⟩ := th_bounds _ h2
  obtain ⟨l3, u3⟩ := th_bounds _ h3
  set A1 := y * ((gammaPartR y).re + Real.log y) with hA1
  set A2 := y * (1 + δ) * ((gammaPartR (y * (1 + δ))).re + Real.log (y * (1 + δ))) with hA2
  set A3 := y * (1 + 2 * δ) * ((gammaPartR (y * (1 + 2 * δ))).re
    + Real.log (y * (1 + 2 * δ))) with hA3
  set R := A3 - 2 * A2 + A1 with hRdef
  have hlin : y * (1 + 2 * δ) - 2 * (y * (1 + δ)) + y = 0 := by ring
  have hR : |R| ≤ 6 := by
    rw [abs_le]; constructor <;> linarith
  set W := ∑' ρ : Zeros, (mult ρ : ℂ) * ((y : ℂ) ^ ((ρ : ℂ) + 1) * coef δ ρ) with hWdef
  have hZ : (∑' ρ : Zeros, (mult ρ : ℂ) * (((y * (1 + 2 * δ) : ℝ) : ℂ)
        * zeroTermR (y * (1 + 2 * δ)) ρ))
      - 2 * (∑' ρ : Zeros, (mult ρ : ℂ) * (((y * (1 + δ) : ℝ) : ℂ)
        * zeroTermR (y * (1 + δ)) ρ))
      + (∑' ρ : Zeros, (mult ρ : ℂ) * ((y : ℂ) * zeroTermR y ρ)) = -W := by
    rw [← ((s3.hasSum.sub (s2.hasSum.mul_left 2)).add s1.hasSum).tsum_eq, hWdef, ← tsum_neg]
    exact tsum_congr fun ρ => by
      linear_combination (mult ρ : ℂ) * second_diff_zero y δ hy0 hδ ρ
  have hmain : ((D2 δ y - δ ^ 2 * y ^ 2 : ℝ) : ℂ) = (R : ℂ) - W := by
    unfold D2
    rw [hRdef]
    push_cast at e1 e2 e3 hZ ⊢
    linear_combination e3 - 2 * e2 + e1 + hZ
  have hW : W = ((y ^ (3 / 2 : ℝ) : ℝ) : ℂ) * F δ (Real.log y) := by
    rw [hWdef, F, zeroWave, ← tsum_mul_left]
    refine tsum_congr fun ρ => ?_
    rw [cpow_succ_of_RH hRH hy0 ρ]
    ring
  have hWn : ‖W‖ = y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖ := by
    rw [hW, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  calc |D2 δ y - δ ^ 2 * y ^ 2| = ‖((D2 δ y - δ ^ 2 * y ^ 2 : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖(R : ℂ) - W‖ := by rw [hmain]
    _ ≤ ‖(R : ℂ)‖ + ‖W‖ := norm_sub_le _ _
    _ ≤ 6 + y ^ (3 / 2 : ℝ) * ‖F δ (Real.log y)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs, hWn]
        linarith

end Erdos233
