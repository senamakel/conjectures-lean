import Mathlib

/-!
# The completed L-functions are entire of order ≤ 1

`xiZeta s = s (s - 1) Λ(s)` (Riemann's ξ up to a factor ½), written via Mathlib's entire
`completedRiemannZeta₀`, and `completedLFunction χ` for non-trivial primitive `χ`.
-/

open Complex

namespace Erdos985.Analytic

/-- Riemann's `ξ`, up to the factor `1/2`: `s (s - 1) Λ(s)`, extended to an entire function. -/
noncomputable def xiZeta (s : ℂ) : ℂ := s * (s - 1) * completedRiemannZeta₀ s + 1

theorem differentiable_xiZeta : Differentiable ℂ xiZeta := by
  sorry

theorem xiZeta_eq {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    xiZeta s = s * (s - 1) * completedRiemannZeta s := by
  sorry

theorem xiZeta_zero : xiZeta 0 = 1 := by
  sorry

theorem xiZeta_growth :
    ∃ C : ℝ, ∀ s : ℂ, ‖xiZeta s‖ ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  sorry

theorem completedLFunction_growth {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    ∃ C : ℝ, ∀ s : ℂ, ‖DirichletCharacter.completedLFunction χ s‖
      ≤ C * Real.exp (C * ‖s‖ * Real.log (‖s‖ + 2)) := by
  sorry

theorem completedLFunction_zero_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) :
    DirichletCharacter.completedLFunction χ 0 ≠ 0 := by
  sorry

end Erdos985.Analytic
