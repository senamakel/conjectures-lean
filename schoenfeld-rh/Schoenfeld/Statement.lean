import Schoenfeld.LogIntegral

/-!
# Target statements (fixed; see the conjectures tracker, rule 3)

Schoenfeld, *Sharper bounds for the Chebyshev functions θ(x) and ψ(x). II*, Math. Comp. 30
(1976), 337–360, Theorem 10 and Corollary 1: under RH,

* `|ψ(x) − x| < √x log² x / (8π)` for `x ≥ 73.2`,
* `|θ(x) − x| < √x log² x / (8π)` for `x ≥ 599`,
* `|π(x) − li(x)| < √x log x / (8π)` for `x ≥ 2657`.

`li` is the principal-value logarithmic integral `li(x) = pv ∫₀ˣ dt / log t`, taken verbatim
from formal-conjectures (`Real.logIntegral`, vendored in `Schoenfeld/LogIntegral.lean`):
`li(x) = li(2) + ∫₂ˣ dt / log t` with `li(2) ≈ 1.04516`. This is the normalisation Schoenfeld
uses; the offset logarithmic integral `Li(x) = ∫₂ˣ dt / log t` differs from it by `li(2)`.

No formal-conjectures statement of Schoenfeld's bounds exists (searched 2026-11-24), so the
statements below are written here. They are parametrised by the constant `C` and the threshold
`x₀`, so that a weaker proved constant can be stated against the same definition; Schoenfeld's
statements are the instances with `C = 1/(8π)`.

The ψ statement `PsiBound` is relied on by `cramer-rh`; keep its form stable.
-/

namespace Schoenfeld

open Chebyshev Real

/-- `|ψ(x) − x| < C √x log² x` for all real `x ≥ x₀`. -/
def PsiBound (C x₀ : ℝ) : Prop :=
  ∀ x : ℝ, x₀ ≤ x → |ψ x - x| < C * (√x * Real.log x ^ 2)

/-- `|θ(x) − x| < C √x log² x` for all real `x ≥ x₀`. -/
def ThetaBound (C x₀ : ℝ) : Prop :=
  ∀ x : ℝ, x₀ ≤ x → |θ x - x| < C * (√x * Real.log x ^ 2)

/-- `|π(x) − li(x)| < C √x log x` for all real `x ≥ x₀`, with `π(x) = π(⌊x⌋)` and the
principal-value `li`. -/
def PiBound (C x₀ : ℝ) : Prop :=
  ∀ x : ℝ, x₀ ≤ x →
    |(Nat.primeCounting ⌊x⌋₊ : ℝ) - Real.logIntegral x| < C * (√x * Real.log x)

/-- Schoenfeld's ψ bound: `|ψ(x) − x| < √x log² x / (8π)` for `x ≥ 73.2`. -/
def SchoenfeldPsi : Prop := PsiBound (1 / (8 * π)) 73.2

/-- Schoenfeld's θ bound: `|θ(x) − x| < √x log² x / (8π)` for `x ≥ 599`. -/
def SchoenfeldTheta : Prop := ThetaBound (1 / (8 * π)) 599

/-- Schoenfeld's Corollary 1: `|π(x) − li(x)| < √x log x / (8π)` for `x ≥ 2657`. -/
def SchoenfeldPi : Prop := PiBound (1 / (8 * π)) 2657

/-- Schoenfeld's three bounds together. -/
def SchoenfeldStatement : Prop := SchoenfeldPsi ∧ SchoenfeldTheta ∧ SchoenfeldPi

end Schoenfeld
