import Erdos985.Bach
import Erdos985.Analytic.Hadamard
import Erdos985.Analytic.Perron.Weighted
import Erdos985.Analytic.Perron.Residue
import Erdos985.Analytic.Digamma

/-!
# Bach's non-principal bound from Hadamard and Perron  (assembly)

Notation: `χ` is primitive and non-trivial mod `N`, and `Λ(s) = completedLFunction χ s`, using
Mathlib's normalisation (`= gammaFactor χ s · L(s,χ)`, with no conductor factor). Write
`D = Λ'/Λ`, `a ∈ {0, 1}` for the parity of `χ`, `G(s) = -½ log π + ½ ψ((s+a)/2)` for the
logarithmic derivative of the gamma factor, and `K(s) = x^s / (s(s+1))`.

1. Perron (`PerronKernel.perron_weighted`, `c = 2`): `bachSum χ x = (1/2π) ∫ (−L'/L)(2+it) K dt`.
2. `−L'/L = −(D − D(2)) + (G − G(2)) − L'/L(2)`, and `(1/2π) ∫ K = 1 − 1/x`.
3. Hadamard: `D(s) − D(2) = Σ_ρ m_ρ (1/(s−ρ) − 1/(2−ρ))`. The constant `b` cancels.
4. Integrating term by term with `perron_residue_aux` (`w = ρ`) gives `explicit_formula`.
5. Under GRH (`ρ = ½ + iγ`, so `|ρ(2−ρ)| = |ρ(ρ+1)|` and `|(2−ρ)(1+ρ)| ≥ |ρ(ρ+1)|`):
   - `‖zeroTerm x ρ‖ ≤ (√x + 2 + 3/x) / ‖ρ(ρ+1)‖`;
   - `‖gammaPart‖ ≤ log x + 1`;
   - `‖L'/L(2)‖ ≤ Σ Λ(n)/n² ≤ 0.6`;
   - `Σ_ρ m_ρ/‖ρ(ρ+1)‖ ≤ (2/3)(log N + 5/3)`. This last one comes from
     `Re Σ_ρ 1/(s−ρ) = ½ log N + Re D(s)` at `s = 3/2`, which uses Hadamard at `s = 1` and the
     functional equation. Then `1/|ρ(ρ+1)| ≤ (4/3)/(1+γ²) = (4/3) Re 1/(3/2 − ρ)`.
6. Together these give exactly MTT Lemma 1, the statement of `Erdos985.bach_nonprincipal`.
-/

namespace Erdos985.Analytic

open Complex ArithmeticFunction MeasureTheory
open scoped Classical

variable {N : ℕ} [NeZero N]

/-- Parity of a Dirichlet character: `0` if even, `1` if odd. -/
noncomputable def parity (χ : DirichletCharacter ℂ N) : ℕ := if χ.Even then 0 else 1

/-- Logarithmic derivative of Mathlib's `gammaFactor χ`: `-½ log π + ½ ψ((s+a)/2)`. -/
noncomputable def gammaLogDeriv (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  -(1 / 2) * (Real.log Real.pi : ℂ) + (1 / 2) * digamma ((s + parity χ) / 2)

/-- The gamma-factor contribution to the weighted explicit formula. -/
noncomputable def gammaPart (χ : DirichletCharacter ℂ N) (x : ℕ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ,
    (gammaLogDeriv χ (2 + t * I) - gammaLogDeriv χ 2) * (x : ℂ) ^ ((2 : ℂ) + t * I)
      / (((2 : ℂ) + t * I) * ((2 : ℂ) + t * I + 1))

/-- The contribution of one zero `ρ`, before multiplicity. -/
noncomputable def zeroTerm (x : ℕ) (ρ : ℂ) : ℂ :=
  (1 - 1 / (x : ℂ)) / (2 - ρ)
    - ((x : ℂ) ^ ρ / (ρ * (ρ + 1)) - 1 / ρ + (x : ℂ) ^ (-1 : ℂ) / (1 + ρ))

end Erdos985.Analytic
