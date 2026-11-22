import Mathlib

/-!
# Digamma values used in Bach's zero-sum bound

Bach's bound evaluates `Re ψ((3/2 + a)/2)` for the parity `a ∈ {0, 1}` of the character,
that is, `ψ(3/4)` and `ψ(5/4)`. Exact values: `ψ(3/4) = π/2 − 3 log 2 − γ ≈ −1.08586` and
`ψ(5/4) = ψ(1/4) + 4 = 4 − π/2 − 3 log 2 − γ ≈ −0.22745`.
-/

namespace Erdos985.Analytic

open Complex

theorem digamma_three_quarters_re_le : (digamma (3 / 4 : ℂ)).re ≤ -1.085 := by
  sorry

theorem digamma_five_quarters_re_le : (digamma (5 / 4 : ℂ)).re ≤ -0.227 := by
  sorry

end Erdos985.Analytic
