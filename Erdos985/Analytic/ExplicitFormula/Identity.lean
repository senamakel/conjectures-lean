import Erdos985.Analytic.ExplicitFormula.StepA

namespace Erdos985.Analytic

open Complex ArithmeticFunction MeasureTheory
open scoped Classical

variable {N : ℕ} [NeZero N]

/-! ### Step B: the explicit formula (an exact identity) -/

/-- The weighted explicit formula, with the Hadamard constant eliminated. -/
theorem explicit_formula {χ : DirichletCharacter ℂ N} (hprim : χ.IsPrimitive) (hχ : χ ≠ 1)
    (x : ℕ) (hx : 1 ≤ x) :
    bachSum χ x
      = (∑' ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0},
            (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℂ) * zeroTerm x ρ)
        + gammaPart χ x
        - (1 - 1 / (x : ℂ)) * (deriv (DirichletCharacter.LFunction χ) 2
            / DirichletCharacter.LFunction χ 2) := by
  sorry

end Erdos985.Analytic
