import Mathlib

/-!
# Step 7: Hadamard three-lines with logarithmic growth

If `F` is holomorphic on the closed strip `a ≤ σ ≤ b`, `‖F‖ ≤ A log (|t| + 2)` on the strip and
`‖F‖ ≤ B` on the right edge, then `‖F(σ + it)‖ ≤ C log (|t| + 2)^{(b-σ)/(b-a)}`.

Proof: `Complex.HadamardThreeLines.norm_le_interpStrip_of_mem_verticalClosedStrip` applied to
`F(s) exp((s - i t₀)²)`, which is bounded on the strip and concentrated at height `t₀`.
-/

namespace Lindelof

open Complex

theorem norm_le_log_rpow_of_strip {F : ℂ → ℂ} {a b A B : ℝ} (hab : a < b)
    (hF : DifferentiableOn ℂ F {s : ℂ | a ≤ s.re ∧ s.re ≤ b})
    (hA : ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖F s‖ ≤ A * Real.log (|s.im| + 2))
    (hB : ∀ s : ℂ, s.re = b → ‖F s‖ ≤ B) :
    ∃ C : ℝ, ∀ σ t : ℝ, a ≤ σ → σ ≤ b →
      ‖F (σ + t * I)‖ ≤ C * Real.log (|t| + 2) ^ ((b - σ) / (b - a)) := by
  sorry

end Lindelof
