import Erdos985.Analytic.ExplicitFormula
import Erdos985.Analytic.XiGrowth

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

theorem xiZeta_zero_re_mem {ρ : ℂ} (hρ : xiZeta ρ = 0) : 0 < ρ.re ∧ ρ.re < 1 := by
  sorry

/-- The weighted explicit formula for `ζ`. -/
theorem explicit_formula_zeta (x : ℕ) (hx : 1 ≤ x) :
    (((∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) : ℝ)) : ℂ)
      = (∑' ρ : {ρ : ℂ // xiZeta ρ = 0}, (analyticOrderNatAt xiZeta ρ : ℂ) * zeroTerm x ρ)
        + gammaPart (1 : DirichletCharacter ℂ 1) x
        + ((x : ℂ) / 2 + (Real.log x : ℂ) - 7 / 2 + 3 / (x : ℂ))
        - (1 - 1 / (x : ℂ)) * (deriv riemannZeta 2 / riemannZeta 2) := by
  sorry

end Erdos985.Analytic
