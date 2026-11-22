import Mathlib

/-!
# Explicit numerical constants: digamma values and `-ζ'/ζ(3/2)`

True values: `ψ(3/4) ≈ -1.0858609`, `ψ(5/4) ≈ -0.2274535`, `Σ Λ(n) n^{-3/2} ≈ 1.5052`.
-/

open Complex ArithmeticFunction

namespace Erdos985.Analytic

theorem digamma_three_quarters_le :
    (deriv Gamma (3 / 4) / Gamma (3 / 4)).re ≤ -1.08 := by
  sorry

theorem digamma_five_quarters_le :
    (deriv Gamma (5 / 4) / Gamma (5 / 4)).re ≤ -0.22 := by
  sorry

theorem summable_vonMangoldt_rpow : Summable fun n : ℕ => (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) := by
  sorry

theorem tsum_vonMangoldt_rpow_le : ∑' n : ℕ, (Λ n : ℝ) / (n : ℝ) ^ (3 / 2 : ℝ) ≤ 1.52 := by
  sorry

end Erdos985.Analytic
