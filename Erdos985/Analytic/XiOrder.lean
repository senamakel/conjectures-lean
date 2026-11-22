import Erdos985.Analytic.Hadamard

/-!
# The completed Dirichlet L-function has order at most one

For a primitive non-trivial character `χ`, Mathlib's `completedLFunction χ` is entire
(`DirichletCharacter.differentiable_completedLFunction`). These are the hypotheses
`hadamard_logDeriv` needs.
-/

namespace Erdos985.Analytic

open Complex

theorem completedLFunction_orderAtMostOne {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    OrderAtMostOne (DirichletCharacter.completedLFunction χ) := by
  sorry

theorem completedLFunction_zero_ne_zero {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprim : χ.IsPrimitive) (hχ : χ ≠ 1) :
    DirichletCharacter.completedLFunction χ 0 ≠ 0 := by
  sorry

end Erdos985.Analytic
