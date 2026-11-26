import Mathlib
import Erdos985.Analytic.Digamma
import Erdos985.Analytic.Constants.VonMangoldt

/-!
# Explicit numerical constants: digamma values and `-ζ'/ζ(3/2)`

True values: `ψ(3/4) ≈ -1.0858609`, `ψ(5/4) ≈ -0.2274535`, `Σ Λ(n) n^{-3/2} ≈ 1.5052`.

The digamma bounds come from the closed forms in `Erdos985.Analytic.Digamma`; the von Mangoldt
bound is proved in `Erdos985.Analytic.Constants.VonMangoldt`.
-/

open Complex ArithmeticFunction

namespace Erdos985.Analytic

private lemma deriv_div_Gamma_eq (s : ℂ) : deriv Gamma s / Gamma s = digamma s := by
  rw [digamma_def, logDeriv_apply]

theorem digamma_three_quarters_le :
    (deriv Gamma (3 / 4) / Gamma (3 / 4)).re ≤ -1.08 := by
  rw [deriv_div_Gamma_eq]
  linarith [digamma_three_quarters_re_le]

theorem digamma_five_quarters_le :
    (deriv Gamma (5 / 4) / Gamma (5 / 4)).re ≤ -0.22 := by
  rw [deriv_div_Gamma_eq]
  linarith [digamma_five_quarters_re_le]

theorem summable_vonMangoldt_rpow : Summable fun n : ℕ => (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) :=
  ConstantsAux.summable_Λ

theorem tsum_vonMangoldt_rpow_le : ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) ≤ 1.52 := by
  have hmul := ConstantsAux.mul_eq
  obtain ⟨hZ, hD⟩ := ConstantsAux.finite_bounds
  have hS : 0 ≤ ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) :=
    tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (by positivity)
  set S := ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)
  set Z := ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)
  by_contra h
  have h' := (not_le.mp h).le
  nlinarith [mul_le_mul h' hZ (by norm_num) hS]

/-- Sharper form, needed for Bach's zero-sum constant `5/3`: `3.9490 / 2.6069 < 1.515`. -/
theorem tsum_vonMangoldt_rpow_le_sharp :
    ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) ≤ 1.515 := by
  have hmul := ConstantsAux.mul_eq
  obtain ⟨hZ, hD⟩ := ConstantsAux.finite_bounds
  have hS : 0 ≤ ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) :=
    tsum_nonneg fun n => div_nonneg vonMangoldt_nonneg (by positivity)
  set S := ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)
  set Z := ∑' n : ℕ, (1 : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ)
  by_contra h
  have h' := (not_le.mp h).le
  nlinarith [mul_le_mul h' hZ (by norm_num) hS]

end Erdos985.Analytic
