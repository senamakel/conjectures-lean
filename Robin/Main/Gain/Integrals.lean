import Robin.Main.Gain.Basic

/-! # The main integral `∫ t·v` -/

namespace Robin.Gain

open Real Chebyshev

theorem main_integral {x Y : ℝ} (hY1 : 1 < Y) (hYx : Y ≤ x) (hL : 30 ≤ Real.log x)
    (hlY : Real.log x / 2 ≤ Real.log Y) :
    (1 / (Y * Real.log Y) - 1 / (x * Real.log x)) * (1 + Real.log x / (Real.log x + 2)) ≤
      ∫ t in Y..x, t * vW t := by
  sorry

end Robin.Gain
