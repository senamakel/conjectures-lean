import Lindelof.RH

/-!
# Step 2: under RH, `|ξ(σ + it)|` increases in `σ ≥ 1/2`

See `docs/BLUEPRINT.md`, Step 2: the Hadamard product (`hadamard_logDeriv`) together with
`ξ(1 - s) = ξ(s)` and `ξ(s̄) = conj ξ(s)` gives `2 ∂σ log|ξ| = Σ_ρ m_ρ (2σ - 1)/|s - ρ|² ≥ 0`.
-/

namespace Lindelof

open Complex Erdos985.Analytic

/-- Under RH, `σ ↦ ‖ξ(σ + it)‖` is monotone on `[1/2, ∞)`. -/
theorem norm_xiZeta_le_of_half_le (hRH : RiemannHypothesis) (t : ℝ) {σ σ' : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσσ' : σ ≤ σ') :
    ‖xiZeta (σ + t * I)‖ ≤ ‖xiZeta (σ' + t * I)‖ := by
  sorry

end Lindelof
