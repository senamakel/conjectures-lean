import Mathlib

/-!
# Hadamard factorization, logarithmic-derivative form, for entire functions of order ≤ 1

If `f` is entire, `f 0 ≠ 0`, and `‖f z‖ ≤ C exp(C ‖z‖ log(‖z‖ + 2))`, then the zeros `ρ`
(with multiplicity `m ρ`) satisfy `Σ m ρ / ‖ρ‖^(1+ε) < ∞` for every `ε > 0`, and
`f'/f (z) = b + Σ_ρ m ρ (1/(z - ρ) + 1/ρ)` away from the zeros.
-/

namespace Erdos985.Analytic

theorem hadamard_logDeriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hgrowth : ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (C * ‖z‖ * Real.log (‖z‖ + 2))) :
    (∀ ε : ℝ, 0 < ε → Summable fun ρ : {ρ : ℂ // f ρ = 0} =>
        (analyticOrderNatAt f ρ : ℝ) / ‖(ρ : ℂ)‖ ^ (1 + ε)) ∧
    ∃ b : ℂ, ∀ z : ℂ, f z ≠ 0 →
      Summable (fun ρ : {ρ : ℂ // f ρ = 0} =>
        (analyticOrderNatAt f ρ : ℂ) * (1 / (z - ρ) + 1 / ρ)) ∧
      deriv f z / f z = b + ∑' ρ : {ρ : ℂ // f ρ = 0},
        (analyticOrderNatAt f ρ : ℂ) * (1 / (z - ρ) + 1 / ρ) := by
  sorry

end Erdos985.Analytic
