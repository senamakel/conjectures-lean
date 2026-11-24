import Erdos233.Explicit
import Cramer.MeanSquare.Coeff

/-!
# Mean square, step 2: the first difference of `psi1` through the explicit formula

erdos-233's real-`x` explicit formula (`psi1_formula`) gives, for `h = δy`,

`psi1(y + h) − psi1(y) − h y = h K − δ Σ_ρ m_ρ y^{ρ+1} acoef δ ρ + R + h²/2 − 7h/2 − h ζ'/ζ(2)`

with `K = Σ_ρ m_ρ (1/(2−ρ) + 1/ρ)` (absolutely convergent), `|R| ≤ h + 3/2` from the gamma
factor. Under RH `|y^{ρ+1}| = y^{3/2}`, so for `1 ≤ h ≤ 4`

`|psi1(y + h) − psi1(y) − h y| ≤ h (B + √y ‖Σ_ρ m_ρ acoef δ ρ y^{iγ}‖)`,

with `B` an absolute constant.
-/

namespace Cramer.MeanSq

open Complex ArithmeticFunction Erdos985.Analytic Erdos233 ExplicitAux

lemma first_diff_zero (y δ : ℝ) (hy : 0 < y) (hδ : 0 < δ) (ρ : ℂ) :
    ((y * (1 + δ) : ℝ) : ℂ) * zeroTermR (y * (1 + δ)) ρ - (y : ℂ) * zeroTermR y ρ
      = ((δ * y : ℝ) : ℂ) * (1 / (2 - ρ) + 1 / ρ)
        - (y : ℂ) ^ (ρ + 1) * ((δ : ℂ) * acoef δ ρ) := by
  have hδc : (δ : ℂ) ≠ 0 := ofReal_ne_zero.2 hδ.ne'
  rw [t_zeroTermR _ (by positivity), t_zeroTermR _ hy]
  have e2 : (((y * (1 + δ)) : ℝ) : ℂ) ^ (ρ + 1)
      = (y : ℂ) ^ (ρ + 1) * ((1 + δ : ℝ) : ℂ) ^ (ρ + 1) := by
    rw [ofReal_mul, mul_cpow_ofReal_nonneg hy.le (by positivity)]
  have ha : (δ : ℂ) * acoef δ ρ
      = (((1 + δ : ℝ) : ℂ) ^ (ρ + 1) - 1) / (ρ * (ρ + 1)) := by
    unfold acoef
    rw [mul_div_assoc', mul_div_cancel_left₀ _ hδc]
  rw [e2, ha]
  push_cast
  ring

lemma rpow_three_halves {y : ℝ} (hy : 0 < y) : y ^ (3 / 2 : ℝ) = y * Real.sqrt y := by
  rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy,
    Real.rpow_one]

/-- The zero wave of the first-difference coefficients. -/
noncomputable def G (δ : ℝ) (u : ℝ) : ℂ := zeroWave (fun ρ => acoef δ ρ) u

theorem first_diff_bound (hRH : RiemannHypothesis) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ δ y : ℝ, 0 < δ → δ ≤ 1 / 2 → 1 ≤ y → 1 ≤ δ * y → δ * y ≤ 4 →
    |psi1 (y * (1 + δ)) - psi1 y - δ * y * y|
      ≤ δ * y * (B + Real.sqrt y * ‖G δ (Real.log y)‖) := by
  obtain ⟨Ca, -, hCa⟩ := acoef_sums hRH
  set Kf : Zeros → ℂ := fun ρ => (mult ρ : ℂ) * (1 / (2 - (ρ : ℂ)) + 1 / (ρ : ℂ)) with hKf
  set K : ℂ := ∑' ρ, Kf ρ with hK
  set c : ℂ := deriv riemannZeta 2 / riemannZeta 2 with hc
  refine ⟨‖K‖ + ‖c‖ + 8, by positivity, fun δ y hδ hδ' hy hh1 hh4 => ?_⟩
  obtain ⟨hS1, -, -⟩ := hCa δ hδ hδ'
  have hy0 : (0 : ℝ) < y := by linarith
  have h2 : 1 ≤ y * (1 + δ) := by nlinarith
  set h : ℝ := δ * y with hhdef
  have hh0 : 0 ≤ h := by positivity
  obtain ⟨s1, e1⟩ := psi1_formula y hy
  obtain ⟨s2, e2⟩ := psi1_formula _ h2
  obtain ⟨l1, u1⟩ := th_bounds y hy
  obtain ⟨l2, u2⟩ := th_bounds _ h2
  set A1 := y * ((gammaPartR y).re + Real.log y) with hA1
  set A2 := y * (1 + δ) * ((gammaPartR (y * (1 + δ))).re + Real.log (y * (1 + δ))) with hA2
  set R := A2 - A1 with hRdef
  have hR : |R| ≤ h + 3 / 2 := by
    rw [abs_le]; constructor <;> nlinarith
  -- the zero family
  set Wf : Zeros → ℂ := fun ρ => (mult ρ : ℂ) * ((y : ℂ) ^ ((ρ : ℂ) + 1) * ((δ : ℂ) * acoef δ ρ))
    with hWf
  have hWn : ∀ ρ : Zeros, ‖Wf ρ‖ = y ^ (3 / 2 : ℝ) * δ * ((mult ρ : ℝ) * ‖acoef δ ρ‖) := by
    intro ρ
    simp only [hWf]
    rw [cpow_succ_of_RH hRH hy0 ρ, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real,
      norm_exp_ofReal_mul_I, Complex.norm_natCast, Complex.norm_real,
      Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg hδ.le]
    ring
  have hWs : Summable Wf :=
    Summable.of_norm (by simpa only [hWn] using hS1.mul_left (y ^ (3 / 2 : ℝ) * δ))
  set W := ∑' ρ, Wf ρ with hWdef
  have hdiff : ∀ ρ : Zeros,
      (mult ρ : ℂ) * (((y * (1 + δ) : ℝ) : ℂ) * zeroTermR (y * (1 + δ)) ρ)
        - (mult ρ : ℂ) * ((y : ℂ) * zeroTermR y ρ)
      = (h : ℂ) * Kf ρ - Wf ρ := by
    intro ρ
    rw [hKf, hWf, hhdef]
    beta_reduce
    linear_combination (mult ρ : ℂ) * first_diff_zero y δ hy0 hδ ρ
  have hhK : Summable fun ρ => (h : ℂ) * Kf ρ := by
    refine ((s2.sub s1).add hWs).congr fun ρ => ?_
    rw [hdiff ρ]; ring
  have hhc : (h : ℂ) ≠ 0 := ofReal_ne_zero.2 (by positivity)
  have hKs : Summable Kf := (summable_mul_left_iff hhc).mp hhK
  have hZ : (∑' ρ : Zeros, (mult ρ : ℂ) * (((y * (1 + δ) : ℝ) : ℂ)
        * zeroTermR (y * (1 + δ)) ρ))
      - (∑' ρ : Zeros, (mult ρ : ℂ) * ((y : ℂ) * zeroTermR y ρ)) = (h : ℂ) * K - W := by
    have H1 := s2.hasSum.sub s1.hasSum
    have H2 : HasSum (fun ρ => (h : ℂ) * Kf ρ - Wf ρ) ((h : ℂ) * K - W) :=
      (hKs.hasSum.mul_left (h : ℂ)).sub hWs.hasSum
    refine H1.unique ?_
    convert H2 using 1
    funext ρ
    exact hdiff ρ
  have hmain : ((psi1 (y * (1 + δ)) - psi1 y - δ * y * y : ℝ) : ℂ)
      = (h : ℂ) * K - W + (R : ℂ) + (h : ℂ) ^ 2 / 2 - 7 / 2 * (h : ℂ) - (h : ℂ) * c := by
    have hhC : (h : ℂ) = (δ : ℂ) * (y : ℂ) := by rw [hhdef]; push_cast; ring
    rw [hRdef, hc, hhC]
    rw [hhC] at hZ
    push_cast at e1 e2 hZ ⊢
    linear_combination e2 - e1 + hZ
  have hW : W = ((h * Real.sqrt y : ℝ) : ℂ) * G δ (Real.log y) := by
    rw [hWdef, G, zeroWave, ← tsum_mul_left]
    refine tsum_congr fun ρ => ?_
    simp only [hWf]
    rw [cpow_succ_of_RH hRH hy0 ρ, rpow_three_halves hy0, hhdef]
    push_cast
    ring
  have hWnorm : ‖W‖ = h * (Real.sqrt y * ‖G δ (Real.log y)‖) := by
    rw [hW, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    ring
  have n1 : ‖(h : ℂ) * K‖ = h * ‖K‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hh0]
  have n2 : ‖(R : ℂ)‖ = |R| := by rw [Complex.norm_real, Real.norm_eq_abs]
  have n3 : ‖(h : ℂ) ^ 2 / 2‖ = h ^ 2 / 2 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hh0]; norm_num
  have n4 : ‖7 / 2 * (h : ℂ)‖ = 7 / 2 * h := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hh0]; norm_num
  have n5 : ‖(h : ℂ) * c‖ = h * ‖c‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hh0]
  have hh2 : h ^ 2 / 2 ≤ 2 * h := by nlinarith
  calc |psi1 (y * (1 + δ)) - psi1 y - δ * y * y|
      = ‖((psi1 (y * (1 + δ)) - psi1 y - δ * y * y : ℝ) : ℂ)‖ := by
        rw [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖(h : ℂ) * K - W + (R : ℂ) + (h : ℂ) ^ 2 / 2 - 7 / 2 * (h : ℂ) - (h : ℂ) * c‖ := by
        rw [hmain]
    _ ≤ ‖(h : ℂ) * K‖ + ‖W‖ + ‖(R : ℂ)‖ + ‖(h : ℂ) ^ 2 / 2‖ + ‖7 / 2 * (h : ℂ)‖
          + ‖(h : ℂ) * c‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_sub_le _ _
    _ = h * ‖K‖ + h * (Real.sqrt y * ‖G δ (Real.log y)‖) + |R| + h ^ 2 / 2 + 7 / 2 * h
          + h * ‖c‖ := by rw [n1, hWnorm, n2, n3, n4, n5]
    _ ≤ h * (‖K‖ + ‖c‖ + 8 + Real.sqrt y * ‖G δ (Real.log y)‖) := by nlinarith
    _ = δ * y * (‖K‖ + ‖c‖ + 8 + Real.sqrt y * ‖G δ (Real.log y)‖) := by rw [hhdef]

end Cramer.MeanSq
