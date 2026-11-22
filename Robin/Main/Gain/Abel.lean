import Robin.Main.Gain.Basic

/-! # Splitting the gain at `Y` and Abel summation -/

namespace Robin.Gain

open Real Chebyshev

theorem gain_ge_integral {x Y : ℝ} (hY1 : 1 < Y) (hYx : Y ≤ x)
    (hYeq : Y ^ 2 * Real.log Y = 1 / epsR x) (heps : 0 < epsR x) :
    ∫ t in Y..x, θ t * vW t ≤ gainSum x := by
  sorry

end Robin.Gain
