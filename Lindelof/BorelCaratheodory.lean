import Lindelof.Transfer
import Lindelof.LogZeta

/-!
# Step 6: Borel–Carathéodory gives `‖M s‖ ≪_δ log (|t| + 2)` on `σ ≥ 1/2 + δ`

`Re M = log |zetaQ| ≤ C log (|t| + 2)` by `norm_zeta_le_poly`; apply
`Complex.borelCaratheodory` on discs centred at `5/2 + it` of radius `2 - δ/2`.
-/

namespace Lindelof

open Complex

theorem norm_log_zetaQ_le (hRH : RiemannHypothesis) {M : ℂ → ℂ}
    (hM : DifferentiableOn ℂ M halfPlane) (hexp : ∀ s ∈ halfPlane, exp (M s) = zetaQ s)
    (hbd : ∃ C : ℝ, ∀ s : ℂ, 2 ≤ s.re → s.re ≤ 5 → ‖M s‖ ≤ C) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ s : ℂ, 1 / 2 + δ ≤ s.re → s.re ≤ 2 →
      ‖M s‖ ≤ C * Real.log (|s.im| + 2) := by
  sorry

end Lindelof
