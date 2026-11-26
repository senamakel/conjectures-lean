import Erdos985.Analytic.ExplicitFormula
import Erdos985.Analytic.Principal

/-!
# Shared definitions for the LLS explicit-formula lemmas

`χ` is a Dirichlet character mod `N`; in the lemmas it is primitive and non-trivial. Mathlib's
`completedLFunction χ` carries no conductor factor, so `D χ (1 − s) = −log N − D χ⁻¹ s`
(`Erdos985.Analytic.ZeroSumAux.logDeriv_functional_equation`).

* `D χ s = Λ'/Λ(s, χ)`, the logarithmic derivative of the completed `L`-function.
* `Z2 χ = Σ_ρ m_ρ / |ρ|²` over the zeros of `Λ(s, χ)` with multiplicity. Under GRH this is
  `2 |Re B(χ)|` in the notation of Lamzouri–Li–Soundararajan (`LLS.Z2_eq`).
* `logSum χ x = Σ_{n ≤ x} Λ(n) χ(n) log(x/n)` (LLS's `S(x, χ)`).
* `cesShift χ x = Σ_{n < x} Λ(n) χ(n)/n · (1 − n/x)` (the sum in LLS Lemma 2.3).
-/

namespace LLS

open Complex ArithmeticFunction

variable {N : ℕ} [NeZero N]

/-- `Λ'/Λ(s, χ)` for Mathlib's completed `L`-function. -/
noncomputable def D (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  deriv (DirichletCharacter.completedLFunction χ) s / DirichletCharacter.completedLFunction χ s

/-- `Σ_ρ m_ρ / |ρ|²` over the zeros of the completed `L`-function. -/
noncomputable def Z2 (χ : DirichletCharacter ℂ N) : ℝ :=
  ∑' ρ : {ρ : ℂ // DirichletCharacter.completedLFunction χ ρ = 0},
    (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2

/-- `S(x, χ) = Σ_{n ≤ x} Λ(n) χ(n) log(x/n)`. -/
noncomputable def logSum {M : ℕ} (χ : DirichletCharacter ℂ M) (x : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (x + 1), (Λ n : ℂ) * χ n * (Real.log ((x : ℝ) / n) : ℂ)

/-- `Σ_{n < x} Λ(n) χ(n)/n · (1 − n/x)`. -/
noncomputable def cesShift {M : ℕ} (χ : DirichletCharacter ℂ M) (x : ℕ) : ℂ :=
  ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n / n * (1 - (n : ℂ) / x)

/-- Upper bound for the gamma-factor term of the log-weighted explicit formula
(LLS's `Ẽ_𝔞(x)`, both parities): `π²/6 − (γ/2) log x`. -/
noncomputable def Etil (x : ℝ) : ℝ := Real.pi ^ 2 / 6 - Real.eulerMascheroniConstant / 2 * Real.log x

/-- Upper bound for the gamma-factor term of the shifted Cesàro formula (LLS's
`−½(1 − 1/x) log π + E_𝔞(x)`, both parities, with slack in the `1/x` term). -/
noncomputable def Eshift (x : ℝ) : ℝ :=
  -(1 / 2) * (1 - 1 / x) * Real.log Real.pi - Real.eulerMascheroniConstant / 2 * (1 - 1 / x)
    + (Real.log x + 2) / x

end LLS
