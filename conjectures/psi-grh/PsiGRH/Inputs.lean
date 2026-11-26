import Mathlib
import PsiGRH.Statement

/-!
# Cited analytic inputs (tier H)

Two classical, unconditional facts about a primitive Dirichlet L-function enter the main library
as explicit `Prop` hypotheses, stated here in Mathlib terms. Neither involves GRH.

* `TruncatedExplicitFormula`: the truncated explicit formula for `ψ(u, χ)` (Davenport,
  *Multiplicative Number Theory*, Ch. 17 and 19; Montgomery–Vaughan Ch. 12), with
  an error uniform in the modulus.
* `ZeroWindowCount`: a unit window of the critical strip at height `t` holds `≪ log(q(|t|+2))`
  zeros, counted with multiplicity (Davenport Ch. 16; Montgomery–Vaughan Theorem 10.17).

`Unconditional/PsiGRHUnconditional.lean` discharges both from
`GlobalTheory.ExplicitFormula.truncated_explicit_formula` and
`GlobalTheory.ZeroWindow.count_zeros_window` of leanprover-community/riemann-hypothesis. The
wording below is this repository's own (that repository has no licence, so nothing is copied);
the discharge is a short bridging proof, not a definitional match.
-/

namespace PsiGRH

open DirichletCharacter

/-- The zeros of `L(s, χ)` in the open critical strip with `|Im ρ| < T`. -/
def stripZeros {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (T : ℝ) : Set ℂ :=
  {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im| < T ∧ LFunction χ ρ = 0}

/-- The zeros of `L(s, χ)` in the open critical strip with `|Im ρ − t| ≤ 1`. -/
def windowZeros {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (t : ℝ) : Set ℂ :=
  {ρ : ℂ | 0 < ρ.re ∧ ρ.re < 1 ∧ |ρ.im - t| ≤ 1 ∧ LFunction χ ρ = 0}

/-- The truncated explicit formula, uniform in the modulus: for primitive `χ` mod `N` and
`2 ≤ T ≤ u`,
`|ψ(u, χ) − E₀(χ) u + Σ_{|Im ρ| < T} m_ρ u^ρ/ρ|
   ≤ C (u log²(NuT)/T + log(Nu) + Σ_{|Im ρ| < 1} m_ρ/|ρ|)`. -/
def TruncatedExplicitFormula : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ u T : ℝ, 2 ≤ T → T ≤ u →
      (stripZeros χ T).Finite ∧
      ‖psiChar χ u - mainTerm χ u +
          ∑ᶠ ρ ∈ stripZeros χ T, (analyticOrderNatAt (LFunction χ) ρ : ℂ) * ((u : ℂ) ^ ρ / ρ)‖ ≤
        C * (u * Real.log (N * u * T) ^ 2 / T + Real.log (N * u) +
          ∑ᶠ ρ ∈ stripZeros χ 1, (analyticOrderNatAt (LFunction χ) ρ : ℝ) / ‖ρ‖)

/-- Zeros in a unit window, uniform in the modulus: for primitive `χ` mod `N` and real `t`,
`Σ_{|Im ρ − t| ≤ 1} m_ρ ≤ C log(N(|t| + 2))`. -/
def ZeroWindowCount : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
    ∀ t : ℝ, (windowZeros χ t).Finite ∧
      ∑ᶠ ρ ∈ windowZeros χ t, (analyticOrderNatAt (LFunction χ) ρ : ℝ) ≤
        C * Real.log (N * (|t| + 2))

end PsiGRH
