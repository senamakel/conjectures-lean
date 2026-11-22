import Erdos985.Analytic.ExplicitFormula.StepA

namespace Erdos985.Analytic

open Complex ArithmeticFunction MeasureTheory
open scoped Classical

variable {N : ℕ} [NeZero N]

/-- Hadamard at `s = 3/2` plus the functional equation, under GRH. -/
theorem zeroSum_le (hGRH : DirichletLNonvanishingRightOfHalf) {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    Summable (fun ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0} =>
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
          / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) ∧
    ∑' ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0},
        (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ)
          / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖
      ≤ (2 / 3) * (Real.log N + 5 / 3) := by
  sorry

end Erdos985.Analytic
