import Erdos985.Analytic.Principal
import Robin.RH.Psi1

/-!
# Bach's weighted explicit-formula bound under RH

The RH-only version of `Erdos985.Analytic.bach_principal_of_GRH`: for every natural `x ≥ 1`,
`|Σ_{n<x} Λ(n)(1 − n/x) − x/2| ≤ √x/20 + 3`.
The erdos-985 proof uses GRH only to place the zeros of `ξ` on the critical line; Mathlib's
`RiemannHypothesis` suffices for that.
-/

namespace Robin

open ArithmeticFunction

/-- The bound produced by the explicit formula; the hypothesis of the analytic part. -/
def BachBound : Prop :=
  ∀ x : ℕ, 1 ≤ x →
    |∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) - x / 2| ≤ √(x : ℝ) / 20 + 3

theorem bachBound_of_RH (hRH : RiemannHypothesis) : BachBound := by
  sorry

/-- `BachBound` multiplied by `m`: the bound for `Ψ₁` at integers. -/
theorem psi1NatBound_of_bachBound (hB : BachBound) : Psi1NatBound := by
  sorry

theorem psi1NatBound_of_RH (hRH : RiemannHypothesis) : Psi1NatBound :=
  psi1NatBound_of_bachBound (bachBound_of_RH hRH)

end Robin
