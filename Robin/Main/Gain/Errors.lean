import Robin.Main.Gain.Basic

/-! # Error integrals `∫ (ψ − t) v` and `∫ (ψ − θ) v` -/

namespace Robin.Gain

open Real Chebyshev

theorem integral_rpow_le {x Y : ℝ} (hY : 0 < Y) (hYx : Y ≤ x) :
    ∫ t in Y..x, t ^ (-(5 : ℝ) / 2) ≤ 2 / 3 * Y ^ (-(3 : ℝ) / 2) := by
  sorry

theorem psi_theta_integral {x Y : ℝ} (hY1 : 1 < Y) (hYx : Y ≤ x) (hL : 30 ≤ Real.log x)
    (hlY : Real.log x / 2 ≤ Real.log Y) :
    ∫ t in Y..x, (ψ t - θ t) * vW t ≤ 45 / Real.log x * Y ^ (-(3 : ℝ) / 2) := by
  sorry

theorem psi_t_integral (P : ℝ → ℝ) (hPc : Continuous P)
    (hPd : ∀ t, HasDerivWithinAt P (ψ t) (Set.Ioi t) t)
    (hPb : ∀ t : ℝ, 16 ≤ t → |P t - t ^ 2 / 2| ≤ t ^ ((3 : ℝ) / 2) / 20 + 4 * t)
    {x Y : ℝ} (hY : 10 ^ 6 ≤ Y) (hYx : Y ≤ x) (hL : 30 ≤ Real.log x)
    (hlY : Real.log x / 2 ≤ Real.log Y) :
    |∫ t in Y..x, (ψ t - t) * vW t| ≤ 1 / Real.log x * Y ^ (-(3 : ℝ) / 2) := by
  sorry

end Robin.Gain
