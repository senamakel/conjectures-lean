import Mathlib
import Erdos985.Analytic.Digamma.EulerMascheroni

/-!
# Digamma values used in Bach's zero-sum bound

Bach's bound evaluates `Re ψ((3/2 + a)/2)` for the parity `a ∈ {0, 1}` of the character,
that is, `ψ(3/4)` and `ψ(5/4)`. Exact values: `ψ(3/4) = π/2 − 3 log 2 − γ ≈ −1.08586` and
`ψ(5/4) = ψ(1/4) + 4 = 4 − π/2 − 3 log 2 − γ ≈ −0.22745`.
-/

namespace Erdos985.Analytic

open Complex

private lemma cot_pi_div_four : Complex.cot (↑Real.pi * (1 / 4)) = 1 := by
  rw [show (↑Real.pi * (1 / 4) : ℂ) = ((Real.pi / 4 : ℝ) : ℂ) by push_cast; ring,
    Complex.cot_eq_cos_div_sin, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  have : (Real.sqrt 2 / 2 : ℝ) ≠ 0 := by positivity
  rw [div_self (by exact_mod_cast this)]

/-- `ψ(3/4) = π/2 − 3 log 2 − γ`. -/
private lemma digamma_three_quarters_eq :
    digamma (3 / 4 : ℂ) =
      ((Real.pi / 2 - 3 * Real.log 2 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
  have hs : ∀ n : ℤ, (1 / 4 : ℂ) ≠ n := by
    intro n h
    have : ((4 * n : ℤ) : ℂ) = 1 := by push_cast; rw [← h]; norm_num
    have : 4 * n = 1 := by exact_mod_cast this
    omega
  have hs2 : ∀ m : ℕ, 2 * (1 / 4 : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have h1 := digamma_one_sub hs
  rw [show (1 : ℂ) - 1 / 4 = 3 / 4 by norm_num, cot_pi_div_four] at h1
  have h2 := digamma_two_mul hs2
  rw [show (2 : ℂ) * (1 / 4) = 1 / 2 by norm_num, show (1 / 4 : ℂ) + 1 / 2 = 3 / 4 by norm_num,
    digamma_one_half] at h2
  have hlog : Complex.log 2 = ((Real.log 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (by norm_num)]; norm_num
  rw [hlog] at h2
  push_cast
  linear_combination h1 / 2 - h2

theorem digamma_three_quarters_re_le : (digamma (3 / 4 : ℂ)).re ≤ -1.085 := by
  rw [digamma_three_quarters_eq, Complex.ofReal_re]
  linarith [Real.pi_lt_d6, Real.log_two_gt_d9, DigammaAux.eulerMascheroniConstant_gt]

theorem digamma_five_quarters_re_le : (digamma (5 / 4 : ℂ)).re ≤ -0.227 := by
  have hs : ∀ m : ℕ, (1 / 4 : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have := congrArg Complex.re h
    simp at this
    linarith [(m.cast_nonneg : (0 : ℝ) ≤ m)]
  have hs' : ∀ n : ℤ, (1 / 4 : ℂ) ≠ n := by
    intro n h
    have : ((4 * n : ℤ) : ℂ) = 1 := by push_cast; rw [← h]; norm_num
    have : 4 * n = 1 := by exact_mod_cast this
    omega
  have h1 := digamma_one_sub hs'
  rw [show (1 : ℂ) - 1 / 4 = 3 / 4 by norm_num, cot_pi_div_four,
    digamma_three_quarters_eq] at h1
  have h3 := digamma_apply_add_one (1 / 4) hs
  rw [show (1 / 4 : ℂ) + 1 = 5 / 4 by norm_num] at h3
  have h5 : digamma (5 / 4 : ℂ) =
      ((4 - Real.pi / 2 - 3 * Real.log 2 - Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    rw [h3]
    push_cast at h1 ⊢
    linear_combination -h1
  rw [h5, Complex.ofReal_re]
  linarith [Real.pi_gt_d6, Real.log_two_gt_d9, DigammaAux.eulerMascheroniConstant_gt]

end Erdos985.Analytic
