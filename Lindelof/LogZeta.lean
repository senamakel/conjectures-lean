import Lindelof.RH

/-!
# Step 5: a logarithm of `ζ₁(s) / (s + 1)` on `Re s > 1/2`

`ζ₁(s) / (s + 1) = ζ(s) (s - 1)/(s + 1)` is holomorphic and, under RH, nonvanishing on the
half-plane; the half-plane is simply connected, so it has a holomorphic logarithm. Normalized
against the Euler product, that logarithm is bounded on `2 ≤ σ ≤ 5`. (Dividing by `s + 1`
removes the `log (s - 1)` growth, which would otherwise spoil the three-lines step.)
-/

namespace Lindelof

open Complex

/-- The half-plane `Re s > 1/2`. -/
def halfPlane : Set ℂ := {s | 1 / 2 < s.re}

/-- The function whose logarithm we take: `ζ₁(s) / (s + 1)`. -/
noncomputable def zetaQ (s : ℂ) : ℂ := riemannZeta₁ s / (s + 1)

theorem exists_log_zetaQ (hRH : RiemannHypothesis) :
    ∃ M : ℂ → ℂ, DifferentiableOn ℂ M halfPlane ∧
      (∀ s ∈ halfPlane, exp (M s) = zetaQ s) ∧
      ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ 5 → ‖M s‖ ≤ C := by
  sorry

end Lindelof
