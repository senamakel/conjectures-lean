import Mathlib

/-!
# The polynomial inequality behind the analytic range

With `α(u) = Σ_{k<8} k! u^{8−k} + 110000 + 14 u³` and
`β(u) = u⁹ Σ_{k<8} k! (u−1)^{7−k} − (u−1)⁸ (12000 + 23 u³)`, we have
`α(u)² (u−1)⁸ < u⁸ β(u)` for every `u ≥ 40`. Writing `u = 40 + v`, the difference is a polynomial
of degree 20 in `v` whose coefficients are all positive.
-/

namespace Ramanujan

/-- `α(u)`: the upper bound for `(li x + ε(x)) · log⁹ x / x`. -/
def alpha (u : ℝ) : ℝ :=
  u ^ 8 + u ^ 7 + 2 * u ^ 6 + 6 * u ^ 5 + 24 * u ^ 4 + 120 * u ^ 3 + 720 * u ^ 2 + 5040 * u +
    110000 + 14 * u ^ 3

/-- `Σ_{k<8} k! (u−1)^{7−k}`. -/
def bnum (u : ℝ) : ℝ :=
  (u - 1) ^ 7 + (u - 1) ^ 6 + 2 * (u - 1) ^ 5 + 6 * (u - 1) ^ 4 + 24 * (u - 1) ^ 3 +
    120 * (u - 1) ^ 2 + 720 * (u - 1) + 5040

/-- `β(u)`: the lower bound for `(li(x/e) − ε(x/e)) · log⁹ x · log⁸(x/e) / (x/e)`. -/
def beta (u : ℝ) : ℝ := u ^ 9 * bnum u - (u - 1) ^ 8 * (12000 + 23 * u ^ 3)

theorem poly_ineq {u : ℝ} (hu : 40 ≤ u) : alpha u ^ 2 * (u - 1) ^ 8 < u ^ 8 * beta u := by
  obtain ⟨v, hv, rfl⟩ : ∃ v : ℝ, 0 ≤ v ∧ u = 40 + v := ⟨u - 40, by linarith, by ring⟩
  rw [← sub_pos]
  unfold alpha beta bnum
  ring_nf
  positivity

end Ramanujan
