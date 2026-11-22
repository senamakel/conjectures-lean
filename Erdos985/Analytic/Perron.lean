import Mathlib

/-!
# Contour integrals of the weighted Perron kernel `x^s / (s (s + 1))`

All integrals are over the vertical line `Re s = c`, written `s = c + t i`, normalized by
`1/(2π)` (so they equal `(1/2πi) ∫_{(c)}`).
-/

open Complex MeasureTheory

namespace Erdos985.Analytic

/-- Perron's formula for the Cesàro kernel: `(1/2πi)∫_{(c)} y^s/(s(s+1)) ds = max 0 (1 - 1/y)`. -/
theorem perron_cesaro (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (max 0 (1 - 1 / y) : ℝ) := by
  sorry

/-- Residue formula for one extra simple pole `w` left of the line, `x ≥ 1`. -/
theorem perron_residue (x c : ℝ) (hx : 1 ≤ x) (hc : 0 < c) (w : ℂ) (hw : w.re < c)
    (hw0 : w ≠ 0) (hw1 : w ≠ -1) :
    (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
      (x : ℂ) ^ ((c : ℂ) + t * I) /
        (((c : ℂ) + t * I - w) * ((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = (x : ℂ) ^ w / (w * (w + 1)) - 1 / w + (x : ℂ) ^ (-1 : ℂ) / (1 + w) := by
  sorry

end Erdos985.Analytic
