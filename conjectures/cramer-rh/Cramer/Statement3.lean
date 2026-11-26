import Mathlib

/-!
# Cramér's mean-square asymptotic under RH (target statement, Round 6 — do not change)

H. Cramér, *Ein Mittelwertsatz in der Primzahltheorie*, Math. Z. **12** (1922), 147–153. Under
the Riemann hypothesis

`∫_1^X ((ψ(x) − x)/x)² dx ∼ c₁ log X`,   `c₁ = Σ_ρ m_ρ/|ρ|² ≈ 0.046`.

This is the form quoted by Brent–Platt–Trudgian, *The mean square of the error term in the prime
number theorem*, J. Number Theory **238** (2022), 740–762 (arXiv:2008.06140), §5.1 eq. (18) and
the proof of their Theorem 5, who attribute it to Montgomery–Vaughan, *Multiplicative Number
Theory I* (2007), Theorem 13.6 and Exercise 13.1.1.3. (Brent–Platt–Trudgian was read;
Montgomery–Vaughan was not available and is cited through them.)

**Multiplicity.** Brent–Platt–Trudgian (§5.1): "In sums over zeros, each zero ρ is counted
according to its multiplicity m_ρ." So in `c₁ = Σ_ρ m_ρ/|ρ|²` a zero of multiplicity `m` occurs
`m` times, each time with weight `m`. Summed over *distinct* zeros this is
`Σ_ρ m_ρ²/|ρ|²`, which is what `cramerConstant` below is. It is also what the classical proof
gives: `(ψ(e^u) − e^u)e^{−u/2} ≈ −Σ_{distinct ρ} m_ρ e^{iγu}/ρ`, an almost periodic function whose
mean square is the sum of the squared moduli `m_ρ²/|ρ|²` of its coefficients. If every zero is
simple, the two readings agree.

Definitions use Mathlib only: `riemannZeta`, `analyticOrderNatAt` (the multiplicity of a zero),
and `Chebyshev.psi` (`ψ x = Σ_{0 < n ≤ x} Λ(n)`). No formal-conjectures statement exists
(searched 2026-11-24 at `9097e2f9`).

The statement includes the summability of the series defining `c₁`, so that `∑'` is not the junk
value `0`.
-/

namespace Cramer

open Chebyshev Filter Topology

/-- The nontrivial zeros of `ζ`: the zeros in the critical strip `0 < Re s < 1`, each listed
once. -/
def NontrivialZeros : Set ℂ := {ρ | 0 < ρ.re ∧ ρ.re < 1 ∧ riemannZeta ρ = 0}

/-- The summand `m_ρ² / |ρ|²` of Cramér's constant at a distinct zero `ρ` of multiplicity
`m_ρ = analyticOrderNatAt riemannZeta ρ`. -/
noncomputable def cramerTerm (ρ : NontrivialZeros) : ℝ :=
  (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2

/-- Cramér's constant `c₁ = Σ_ρ m_ρ/|ρ|²` (zeros counted with multiplicity), written as a sum
over distinct zeros: `Σ_{ρ distinct} m_ρ²/|ρ|²`. -/
noncomputable def cramerConstant : ℝ := ∑' ρ : NontrivialZeros, cramerTerm ρ

/-- **Cramér (1922)**; Montgomery–Vaughan Theorem 13.6 / Exercise 13.1.1.3:
`∫_1^X ((ψ(x) − x)/x)² dx ∼ c₁ log X`, with the series for `c₁` convergent. -/
def CramerLogMeanSquareAsymptotic : Prop :=
  Summable cramerTerm ∧
    Tendsto (fun X : ℝ => (∫ x in (1 : ℝ)..X, ((ψ x - x) / x) ^ 2) / Real.log X) atTop
      (𝓝 cramerConstant)

end Cramer
