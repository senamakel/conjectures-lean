import Cramer.MeanSquare.Block

/-!
# Asymptotic, step 1: `ψ(y) − y ≈ −√y G(log y)` on a block

`first_diff_bound` bounds the first difference of `psi1` by `√y ‖G‖`; here the same identity is
kept with its sign: `psi1(y + h) − psi1(y) − hy + h√y G δ (log y) = h·O(1)`. With
`h ψ(y) ≤ psi1(y + h) − psi1(y) ≤ h ψ(y + h)` and `ψ(y + 4) − ψ(y) ≤ 4 log(y + 4)`, on the block
`y ∈ [Y, 4Y]`, `δ = 1/Y`:

`‖(ψ(y) − y) + √y G (1/Y) (log y)‖ ≤ B + 4 log(y + 4)`.
-/

namespace Cramer.MeanSq

open Complex ArithmeticFunction Erdos985.Analytic Erdos233 ExplicitAux Chebyshev

theorem first_diff_approx (hRH : RiemannHypothesis) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ δ y : ℝ, 0 < δ → δ ≤ 1 / 2 → 1 ≤ y → 1 ≤ δ * y → δ * y ≤ 4 →
    ‖((psi1 (y * (1 + δ)) - psi1 y - δ * y * y : ℝ) : ℂ)
        + ((δ * y * Real.sqrt y : ℝ) : ℂ) * G δ (Real.log y)‖ ≤ δ * y * B := by
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
  have hsum : ((psi1 (y * (1 + δ)) - psi1 y - δ * y * y : ℝ) : ℂ)
        + ((δ * y * Real.sqrt y : ℝ) : ℂ) * G δ (Real.log y)
      = (h : ℂ) * K + (R : ℂ) + (h : ℂ) ^ 2 / 2 - 7 / 2 * (h : ℂ) - (h : ℂ) * c := by
    rw [hmain, hW, hhdef]; ring
  rw [hsum]
  calc ‖(h : ℂ) * K + (R : ℂ) + (h : ℂ) ^ 2 / 2 - 7 / 2 * (h : ℂ) - (h : ℂ) * c‖
      ≤ ‖(h : ℂ) * K‖ + ‖(R : ℂ)‖ + ‖(h : ℂ) ^ 2 / 2‖ + ‖7 / 2 * (h : ℂ)‖
          + ‖(h : ℂ) * c‖ := by
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_sub_le _ _).trans (add_le_add ?_ le_rfl)
        refine (norm_add_le _ _).trans (add_le_add ?_ le_rfl)
        exact norm_add_le _ _
    _ = h * ‖K‖ + |R| + h ^ 2 / 2 + 7 / 2 * h + h * ‖c‖ := by rw [n1, n2, n3, n4, n5]
    _ ≤ h * (‖K‖ + ‖c‖ + 8) := by nlinarith
    _ = δ * y * (‖K‖ + ‖c‖ + 8) := by rw [hhdef]

/-- **Pointwise approximation on a block.** Under RH, for `Y ≥ 2` and `y ∈ [Y, 4Y]`,
`‖(ψ(y) − y) + √y G (1/Y) (log y)‖ ≤ B + 4 log(y + 4)`. -/
theorem psi_approx (hRH : RiemannHypothesis) : ∃ B : ℝ, 0 ≤ B ∧
    ∀ Y y : ℝ, 2 ≤ Y → Y ≤ y → y ≤ 4 * Y →
    ‖((ψ y - y : ℝ) : ℂ) + (Real.sqrt y : ℂ) * G (1 / Y) (Real.log y)‖
      ≤ B + 4 * Real.log (y + 4) := by
  obtain ⟨B, hB0, hB⟩ := first_diff_approx hRH
  refine ⟨B, hB0, fun Y y hY hy1 hy2 => ?_⟩
  have hY0 : 0 < Y := by linarith
  have hy0 : 0 < y := by linarith
  set δ : ℝ := 1 / Y with hδdef
  have hδ : 0 < δ := by positivity
  have hδ' : δ ≤ 1 / 2 := by
    rw [hδdef, div_le_div_iff₀ hY0 (by norm_num)]; linarith
  set h : ℝ := δ * y with hhdef
  have hh : h = y / Y := by rw [hhdef, hδdef]; ring
  have hh1 : 1 ≤ h := by rw [hh, le_div_iff₀ hY0]; linarith
  have hh4 : h ≤ 4 := by rw [hh, div_le_iff₀ hY0]; linarith
  have hh0 : 0 < h := by linarith
  have hfd := hB δ y hδ hδ' (by linarith) hh1 hh4
  have hyh : y * (1 + δ) = y + h := by rw [hhdef]; ring
  rw [hyh] at hfd
  obtain ⟨lo, hi⟩ := psi1_diff_bounds hy0.le hh0.le
  have hmono : ψ (y + h) ≤ ψ (y + 4) := psi_mono (by linarith)
  have h4 := psi_add_four_sub_le hy0.le
  set D := psi1 (y + h) - psi1 y with hD
  -- `ψ y − y = (D/h − y) − e` with `0 ≤ e ≤ 4 log(y+4)`
  set e : ℝ := D / h - ψ y with he
  have he0 : 0 ≤ e := by
    rw [he, sub_nonneg, le_div_iff₀ hh0]; linarith
  have he1 : e ≤ 4 * Real.log (y + 4) := by
    have : D / h ≤ ψ (y + h) := by rw [div_le_iff₀ hh0]; linarith
    linarith
  have hsplit : ((ψ y - y : ℝ) : ℂ) + (Real.sqrt y : ℂ) * G δ (Real.log y)
      = (h : ℂ)⁻¹ * (((D - h * y : ℝ) : ℂ) + ((h * Real.sqrt y : ℝ) : ℂ) * G δ (Real.log y))
        - (e : ℂ) := by
    have hhc : (h : ℂ) ≠ 0 := ofReal_ne_zero.2 hh0.ne'
    rw [he]
    push_cast
    field_simp
    ring
  have hfd' : ‖((D - h * y : ℝ) : ℂ) + ((h * Real.sqrt y : ℝ) : ℂ) * G δ (Real.log y)‖
      ≤ h * B := by
    have e1 : (((D - h * y : ℝ) : ℂ)) + ((h * Real.sqrt y : ℝ) : ℂ) * G δ (Real.log y)
        = ((D - δ * y * y : ℝ) : ℂ) + ((δ * y * Real.sqrt y : ℝ) : ℂ) * G δ (Real.log y) := by
      rw [hhdef]
    rw [e1, hhdef]; exact hfd
  rw [hsplit]
  calc ‖(h : ℂ)⁻¹ * (((D - h * y : ℝ) : ℂ) + ((h * Real.sqrt y : ℝ) : ℂ) * G δ (Real.log y))
        - (e : ℂ)‖
      ≤ ‖(h : ℂ)⁻¹ * (((D - h * y : ℝ) : ℂ) + ((h * Real.sqrt y : ℝ) : ℂ) * G δ (Real.log y))‖
        + ‖(e : ℂ)‖ := norm_sub_le _ _
    _ ≤ B + 4 * Real.log (y + 4) := by
        rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hh0.le, Complex.norm_real,
          Real.norm_of_nonneg he0]
        have : h⁻¹ * ‖((D - h * y : ℝ) : ℂ) + ((h * Real.sqrt y : ℝ) : ℂ) * G δ (Real.log y)‖
            ≤ B := by
          rw [inv_mul_le_iff₀ hh0]; exact hfd'
        linarith

end Cramer.MeanSq
