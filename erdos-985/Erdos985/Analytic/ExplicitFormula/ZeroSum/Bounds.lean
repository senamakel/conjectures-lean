import Erdos985.Analytic.ExplicitFormula.StepA

/-!
# Numerical inputs for the zero sum at `s = 3/2`
-/

namespace Erdos985.Analytic.ZeroSumAux

open Complex ArithmeticFunction
open scoped Classical

theorem log_pi_gt : (1.1364 : ℝ) < Real.log Real.pi := by
  rw [Real.lt_log_iff_exp_lt Real.pi_pos]
  have h1 : Real.exp 1.1364 = Real.exp 1 * Real.exp 0.1364 := by
    rw [← Real.exp_add]; norm_num
  have h2 := Real.exp_bound' (x := 0.1364) (by norm_num) (by norm_num) (n := 3) (by norm_num)
  simp [Finset.sum_range_succ, Nat.factorial] at h2
  rw [h1]
  have h3 := Real.exp_one_lt_d9
  have h4 := Real.pi_gt_d4
  have h5 : 0 < Real.exp 0.1364 := Real.exp_pos _
  nlinarith

variable {N : ℕ} [NeZero N]

theorem norm_logDeriv_LFunction_three_halves_le (χ : DirichletCharacter ℂ N) :
    ‖deriv (DirichletCharacter.LFunction χ) (3 / 2) / DirichletCharacter.LFunction χ (3 / 2)‖
      ≤ ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) := by
  have hs : 1 < (3 / 2 : ℂ).re := by norm_num
  rw [DirichletCharacter.deriv_LFunction_eq_deriv_LSeries χ hs,
    DirichletCharacter.LFunction_eq_LSeries χ hs]
  have h := DirichletCharacter.LSeries_twist_vonMangoldt_eq χ hs
  have h' : deriv (LSeries fun n => χ n) (3 / 2) / LSeries (fun n => χ n) (3 / 2)
      = -LSeries (fun n => χ n * (Λ n : ℂ)) (3 / 2) := by
    simp only [Pi.mul_def] at h; rw [h, neg_div, neg_neg]
  rw [h', norm_neg, LSeries]
  refine tsum_of_norm_bounded summable_vonMangoldt_rpow.hasSum fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.norm_term_eq]; simp only [hn, ↓reduceIte, norm_mul]
    have : ‖χ n‖ ≤ 1 := DirichletCharacter.norm_le_one χ n
    have hΛ : ‖(Λ n : ℂ)‖ = Λ n := by
      rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    rw [hΛ]
    norm_num
    gcongr
    calc ‖χ n‖ * Λ n ≤ 1 * Λ n := by gcongr
      _ = Λ n := one_mul _

omit [NeZero N] in
theorem re_gammaLogDeriv_three_halves_le (χ : DirichletCharacter ℂ N) :
    (gammaLogDeriv χ (3 / 2)).re ≤ -(1 / 2) * Real.log Real.pi - 0.1135 := by
  unfold gammaLogDeriv parity
  split_ifs
  · have h : ((3 / 2 : ℂ) + ((0 : ℕ) : ℂ)) / 2 = 3 / 4 := by norm_num
    rw [h]
    have := digamma_three_quarters_re_le
    simp only [add_re, mul_re, neg_re, ofReal_re, neg_im, ofReal_im]
    norm_num
    linarith
  · have h : ((3 / 2 : ℂ) + ((1 : ℕ) : ℂ)) / 2 = 5 / 4 := by norm_num
    rw [h]
    have := digamma_five_quarters_re_le
    simp only [add_re, mul_re, neg_re, ofReal_re, neg_im, ofReal_im]
    norm_num
    linarith

/-- `Re Λ'/Λ(3/2) ≤ 1.515 − ½ log π − 0.1135`. -/
theorem re_logDeriv_completed_three_halves_le {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    (deriv (DirichletCharacter.completedLFunction χ) (3 / 2)
        / DirichletCharacter.completedLFunction χ (3 / 2)).re
      ≤ 1.515 - (1 / 2) * Real.log Real.pi - 0.1135 := by
  have h := logDeriv_LFunction_eq hχ (s := 3 / 2) (by norm_num)
  rw [eq_sub_iff_add_eq] at h
  rw [← h, add_re]
  have h1 := (re_le_norm _).trans ((norm_logDeriv_LFunction_three_halves_le χ).trans
    tsum_vonMangoldt_rpow_le_sharp)
  have h2 := re_gammaLogDeriv_three_halves_le χ
  linarith

end Erdos985.Analytic.ZeroSumAux
