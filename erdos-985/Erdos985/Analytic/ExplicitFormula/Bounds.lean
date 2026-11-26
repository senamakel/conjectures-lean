import Erdos985.Analytic.ExplicitFormula.Basic
import Erdos985.Analytic.ExplicitFormula.Bounds.ZeroTerm
import Erdos985.Analytic.ExplicitFormula.Bounds.LogDeriv
import Erdos985.Analytic.ExplicitFormula.Bounds.GammaPart

namespace Erdos985.Analytic

open Complex ArithmeticFunction MeasureTheory
open scoped Classical

variable {N : ℕ} [NeZero N]

/-! ### Step C: the bounds -/

theorem norm_zeroTerm_le (x : ℕ) (hx : 1 ≤ x) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    ‖zeroTerm x ρ‖ ≤ (√(x : ℝ) + 2 + 3 / x) / ‖ρ * (ρ + 1)‖ :=
  norm_zeroTerm_le' x hx hρ

theorem norm_gammaPart_le (χ : DirichletCharacter ℂ N) (x : ℕ) (hx : 1 ≤ x) :
    ‖gammaPart χ x‖ ≤ Real.log x + 1 :=
  norm_gammaPart_le' χ x hx

theorem norm_logDeriv_LFunction_two_le (χ : DirichletCharacter ℂ N) :
    ‖deriv (DirichletCharacter.LFunction χ) 2 / DirichletCharacter.LFunction χ 2‖ ≤ 0.6 :=
  norm_logDeriv_LFunction_two_le' χ

end Erdos985.Analytic
