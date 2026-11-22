import Robin.Main.Gain.Basic

/-! # The splitting point `Y` with `Y² log Y = 1/ε` -/

namespace Robin.Gain

open Real

theorem exists_Y {x : ℝ} (hx : Real.exp 30 ≤ x) :
    ∃ Y, √x ≤ Y ∧ Y ≤ x ∧ Y ^ 2 * Real.log Y = 1 / epsR x ∧
      Real.log x / 2 ≤ Real.log Y ∧ Real.log Y ≤ (Real.log x + 0.6933) / 2 ∧
      0.7071 ≤ √x / Y := by
  sorry

end Robin.Gain
