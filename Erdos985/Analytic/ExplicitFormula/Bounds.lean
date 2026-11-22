import Erdos985.Analytic.ExplicitFormula.Basic

namespace Erdos985.Analytic

open Complex ArithmeticFunction MeasureTheory
open scoped Classical

variable {N : ℕ} [NeZero N]

/-! ### Step C: the bounds -/

theorem norm_zeroTerm_le (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ‖zeroTerm x ρ‖ ≤ (√(x : ℝ) + 2 + 3 / x) / ‖ρ * (ρ + 1)‖ := by
  sorry

theorem norm_gammaPart_le (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 1 ≤ x) :
    ‖gammaPart χ x‖ ≤ Real.log x + 1 := by
  sorry

theorem norm_logDeriv_LFunction_two_le (χ : DirichletCharacter ℂ N) :
    ‖deriv (DirichletCharacter.LFunction χ) 2 / DirichletCharacter.LFunction χ 2‖ ≤ 0.6 := by
  sorry

end Erdos985.Analytic
