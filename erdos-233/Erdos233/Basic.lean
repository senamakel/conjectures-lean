import Erdos985
import Erdos233.Statement

/-!
# Shared definitions

* `Zeros` are the zeros of `ξ = xiZeta` (erdos-985), i.e. the nontrivial zeros of `ζ`, and
  `mult ρ` is the multiplicity.
* `psi1 y = Σ_{n ≤ y} Λ(n) (y − n) = ∫_0^y ψ`.
* `D2 δ y = psi1(y(1+2δ)) − 2 psi1(y(1+δ)) + psi1(y)`, a second difference with step `δy`. Its
  Λ-side is `Σ_n Λ(n) w(n)` with a tent weight `0 ≤ w ≤ δy` supported on `(y, y(1+2δ))`.
* `coef δ ρ = ((1+2δ)^{ρ+1} − 2(1+δ)^{ρ+1} + 1) / (ρ(ρ+1))`, so that the zero `ρ` contributes
  `−y^{ρ+1} coef δ ρ` to `D2 δ y`.
* `zeroWave c u = Σ_ρ m_ρ c_ρ e^{iγu}` (`γ = Im ρ`).
-/

namespace Erdos233

open Complex ArithmeticFunction Erdos985.Analytic

/-- The zeros of `ξ` (the nontrivial zeros of `ζ`). -/
abbrev Zeros : Type := {ρ : ℂ // xiZeta ρ = 0}

/-- Multiplicity of a zero of `ξ`. -/
noncomputable def mult (ρ : Zeros) : ℕ := analyticOrderNatAt xiZeta ρ

/-- `psi1 y = Σ_{n ≤ y} Λ(n) (y − n)`. -/
noncomputable def psi1 (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊y⌋₊ + 1), (Λ n : ℝ) * (y - n)

/-- The second difference of `psi1` with step `δ y`. -/
noncomputable def D2 (δ y : ℝ) : ℝ :=
  psi1 (y * (1 + 2 * δ)) - 2 * psi1 (y * (1 + δ)) + psi1 y

/-- The coefficient of `−y^{ρ+1}` in `D2 δ y`. -/
noncomputable def coef (δ : ℝ) (ρ : ℂ) : ℂ :=
  ((((1 + 2 * δ : ℝ) : ℂ) ^ (ρ + 1) - 2 * ((1 + δ : ℝ) : ℂ) ^ (ρ + 1) + 1)) / (ρ * (ρ + 1))

/-- `Σ_ρ m_ρ c_ρ e^{iγu}`. -/
noncomputable def zeroWave (c : Zeros → ℂ) (u : ℝ) : ℂ :=
  ∑' ρ : Zeros, (mult ρ : ℂ) * c ρ * exp ((((ρ : ℂ).im * u : ℝ) : ℂ) * I)

/-- The wave of the coefficients `coef δ`. -/
noncomputable def F (δ : ℝ) (u : ℝ) : ℂ := zeroWave (fun ρ => coef δ ρ) u

/-- First index whose prime is `≥ m`: the number of primes `< m`. -/
abbrev idx (m : ℕ) : ℕ := Nat.primeCounting' m

/-- Indices `n` with `x ≤ p_n < 2x`. -/
abbrev block (x : ℕ) : Finset ℕ := Finset.Ico (idx x) (idx (2 * x))

end Erdos233
