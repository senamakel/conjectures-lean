import Erdos985.Analytic.ExplicitFormula
import Erdos985.Analytic.XiGrowth
import Erdos985.Analytic.Principal.Bounds.Gamma
import Erdos985.Analytic.Principal.Bounds.Xi

/-!
# Bach's principal bound (RH) from Hadamard for `ξ`  — interfaces

`ξ = xiZeta = s(s−1)Λ(s)` with `Λ(s) = Γℝ(s) ζ(s)`; `ζ'/ζ = ξ'/ξ − 1/s − 1/(s−1) − G(s)`, with
`G = gammaLogDeriv` of the (even) character mod 1. Perron at `c = 2` plus Hadamard for `ξ`,
subtracting the value at `s = 2` (so the Hadamard constant cancels), and the residues
`w = ρ` (`perron_residue`), `w = 1` (gives `x/2 − 1 + 1/(2x)`) and `w = 0`
(`perron_residue_zero`, gives `log x − 1 + 1/x`) yield `explicit_formula_zeta`.

Bounds: `Σ_ρ m/|ρ(ρ+1)| ≤ Σ m/|ρ|² = 2 Σ Re(1/ρ) = 2 + γ − log 4π < 1/20` under RH
(the Hadamard constant of `ξ` is `ξ'/ξ(0) = ½ log 4π − 1 − γ/2`, computed from the
functional equation `ξ(s) = ξ(1−s)` and the Laurent expansion `ζ(s) = 1/(s−1) + γ + …`);
`gammaPart + log x ∈ [1 − 3/(2x), 1]`; `ζ'/ζ(2) ∈ [−0.6, 0]`.
Then `|S − x/2| ≤ (√x + 2 + 3/x)/20 + 5/2 ≤ √x/20 + 3`.
-/

namespace Erdos985.Analytic

open Complex ArithmeticFunction

/-- RH, i.e. GRH for the character mod 1: every zero of `ξ` lies on `Re s = 1/2`. -/
theorem xiZeta_zero_re (hGRH : DirichletLNonvanishingRightOfHalf) {ρ : ℂ} (hρ : xiZeta ρ = 0) :
    ρ.re = 1 / 2 := by
  exact PrincipalAux.xiZeta_zero_re' hGRH hρ

/-- Under RH, `Σ_ρ m/|ρ(ρ+1)| ≤ 2 + γ − log 4π < 1/20`. -/
theorem zeroSum_zeta_le (hGRH : DirichletLNonvanishingRightOfHalf) :
    Summable (fun ρ : {ρ : ℂ // xiZeta ρ = 0} =>
        (analyticOrderNatAt xiZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖) ∧
    ∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℝ) / ‖(ρ : ℂ) * ((ρ : ℂ) + 1)‖
      ≤ 1 / 20 := by
  exact PrincipalAux.zeroSum_zeta_le' hGRH

/-- The gamma part for an even character nearly cancels `log x`. -/
theorem gammaPart_one_bound (x : ℕ) (hx : 1 ≤ x) :
    (gammaPart (1 : DirichletCharacter ℂ 1) x).im = 0 ∧
    1 - 3 / (2 * (x : ℝ)) ≤ (gammaPart (1 : DirichletCharacter ℂ 1) x).re + Real.log x ∧
    (gammaPart (1 : DirichletCharacter ℂ 1) x).re + Real.log x ≤ 1 := by
  exact PrincipalAux.gammaPart_one_bound' x hx

/-- `ζ'/ζ(2) = −Σ Λ(n)/n² ∈ [−0.6, 0]`. -/
theorem logDeriv_zeta_two_bound :
    (deriv riemannZeta 2 / riemannZeta 2).im = 0 ∧
    -0.6 ≤ (deriv riemannZeta 2 / riemannZeta 2).re ∧ (deriv riemannZeta 2 / riemannZeta 2).re ≤ 0 := by
  exact PrincipalAux.logDeriv_zeta_two_bound'

end Erdos985.Analytic
