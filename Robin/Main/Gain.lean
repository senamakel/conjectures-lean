import Robin.RH.Psi1

/-!
# Lower bound for the gain `Σ_{p≤x} min(1/p², ε log p)` for `x ≥ e^{30}`

Let `Y` solve `Y² log Y = 1/ε` (so `√x ≤ Y ≤ √(2(x+1))`). Then the gain is
`ε θ(Y) + Σ_{Y<p≤x} 1/p² = θ(x)/(x² log x) + ∫_Y^x θ(t) v(t) dt` (Abel summation, `v = −(d/dt) 1/(t² log t)`),
and `∫_Y^x t v(t) dt ≥ (1/(Y log Y) − 1/(x log x))(1 + 1/(1 + 1/log Y))`, which is about
`2√2/(√x log x)`; the errors from `θ − t` are `O(x^{-3/4}/log x)`.
-/

namespace Robin

open Filter Topology Real Chebyshev MeasureTheory

theorem gain_bound (hB : Psi1NatBound) {x : ℝ} (hx : Real.exp 30 ≤ x) :
    (2.67 - 60 * x ^ (-(1 : ℝ) / 4)) / (√x * Real.log x) ≤ gainSum x := by
  sorry

end Robin
