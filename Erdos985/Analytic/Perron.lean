import Mathlib

/-!
# Perron's formula with the weight `(1 − n/N)`

The kernel `N^s / (s (s + 1))` gives an absolutely convergent integral:
`(1/2πi) ∫_{(c)} y^s / (s(s+1)) ds = max(0, 1 − 1/y)` for `y > 0`, `c > 0`.
Writing `s = c + it`, `ds = i dt`, so the prefactor becomes `1/(2π)`.
-/

namespace Erdos985.Analytic

open Complex MeasureTheory

theorem perron_kernel (y c : ℝ) (hy : 0 < y) (hc : 0 < c) :
    ∫ t : ℝ, (y : ℂ) ^ ((c : ℂ) + t * I) / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1))
      = 2 * Real.pi * (if 1 ≤ y then 1 - 1 / y else 0) := by
  sorry

theorem perron_weighted (a : ℕ → ℂ) (c : ℝ) (hc : 0 < c)
    (ha : Summable fun n : ℕ => ‖a n‖ / (n : ℝ) ^ c) (N : ℕ) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioo 0 N, a n * (1 - (n : ℂ) / N)
      = (1 / (2 * Real.pi)) * ∫ t : ℝ, LSeries a ((c : ℂ) + t * I) * (N : ℂ) ^ ((c : ℂ) + t * I)
          / (((c : ℂ) + t * I) * ((c : ℂ) + t * I + 1)) := by
  sorry

end Erdos985.Analytic
