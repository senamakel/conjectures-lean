import Mathlib

/-!
# Hadamard factorization for entire functions of order at most one (logarithmic-derivative form)

Classical (Hadamard 1893; e.g. Titchmarsh, *Theory of Functions*, §8.24; Davenport,
*Multiplicative Number Theory*, Ch. 11). Stated through the logarithmic derivative, which is
what the explicit formula uses, and avoiding infinite products.
-/

namespace Erdos985.Analytic

open Complex

/-- `f` grows at most like `exp(|z|^(1+ε))` for every `ε > 0` (order at most one). -/
def OrderAtMostOne (f : ℂ → ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ z : ℂ, ‖f z‖ ≤ C * Real.exp (‖z‖ ^ (1 + ε))

/-- Hadamard: the zeros of an entire function of order at most one, counted with
multiplicity, satisfy `Σ 1/|ρ|² < ∞`, and `f'/f(z) = b + Σ_ρ (1/(z − ρ) + 1/ρ)`. -/
theorem hadamard_logDeriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) (hf0 : f 0 ≠ 0)
    (hord : OrderAtMostOne f) :
    (Summable fun ρ : ℂ => (MeromorphicOn.divisor f Set.univ ρ : ℝ) / ‖ρ‖ ^ 2) ∧
    ∃ b : ℂ, ∀ z : ℂ, f z ≠ 0 →
      logDeriv f z = b + ∑' ρ : ℂ, (MeromorphicOn.divisor f Set.univ ρ : ℂ) * (1 / (z - ρ) + 1 / ρ) := by
  sorry

end Erdos985.Analytic
