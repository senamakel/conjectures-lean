import Erdos985.Analytic.ExplicitFormula.Basic

namespace Erdos985.Analytic

open Complex ArithmeticFunction MeasureTheory
open scoped Classical

variable {N : ℕ} [NeZero N]

/-! ### Step A: zeros, log-derivatives -/

/-- Unconditionally, zeros of the completed L-function lie in the open strip `0 < Re s < 1`. -/
theorem completedLFunction_zero_re_mem {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive)
    (hχ : χ ≠ 1) {ρ : ℂ} (hρ : DirichletCharacter.completedLFunction χ ρ = 0) :
    0 < ρ.re ∧ ρ.re < 1 := by
  sorry

/-- Under GRH every zero of the completed L-function lies on `Re s = 1/2`. -/
theorem completedLFunction_zero_re (hGRH : DirichletLNonvanishingRightOfHalf)
    {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) {ρ : ℂ}
    (hρ : DirichletCharacter.completedLFunction χ ρ = 0) : ρ.re = 1 / 2 := by
  sorry

/-- `L'/L = Λ'/Λ − G` to the right of `Re s = 1`. -/
theorem logDeriv_LFunction_eq {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s
      = deriv (DirichletCharacter.completedLFunction χ) s
          / DirichletCharacter.completedLFunction χ s - gammaLogDeriv χ s := by
  sorry

end Erdos985.Analytic
