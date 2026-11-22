import Lindelof.Monotone
import Lindelof.GammaRatio

/-!
# Step 4: consequences for `ζ` of Steps 2 and 3

`ζ = ξ / (s (s - 1) Γℝ(s))`, so monotonicity of `|ξ|` moves bounds for `ζ` to the left at the
cost of a Gamma ratio.
-/

namespace Lindelof

open Complex

/-- Under RH, `‖ζ(1/2 + it)‖ ≤ C t^{δ/2} ‖ζ(1/2 + δ + it)‖`, uniformly in `δ ∈ (0, 1/2]`. -/
theorem norm_zeta_half_le (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 2 → ∀ t : ℝ, 1 ≤ t →
      ‖riemannZeta (1 / 2 + t * I)‖ ≤ C * t ^ (δ / 2) * ‖riemannZeta ((1 / 2 + δ : ℝ) + t * I)‖ := by
  sorry

/-- Under RH, `ζ` grows at most linearly on `σ ≥ 1/2`, `|t| ≥ 1`. -/
theorem norm_zeta_le_poly (hRH : RiemannHypothesis) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 2 ≤ s.re → 1 ≤ |s.im| → ‖riemannZeta s‖ ≤ C * |s.im| := by
  sorry

end Lindelof
