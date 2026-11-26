import Littlewood.Dirichlet
import Littlewood.GammaSide

/-!
# Step 6: the explicit formula for `ζ'/ζ` with the weight `log (x/n)`

Under RH, for `Re s > 1/2`, `|Im s| ≥ 1` and `x ≥ 1`,

    log x · (-ζ'/ζ(s)) = D(s, x) + Z(s, x) - E_R(s, x)

with `D(s, x) = Σ_{n ≤ x} Λ(n) n^{-s} log (x/n)`, `Z(s, x) = Σ_ρ m_ρ (x^{ρ-s} - 1)/(ρ - s)²`
and `E_R` the trivial-pole terms of `GammaSide`. Proof: integrate
`L(Λ, s + w) = R(s + w) - ξ'/ξ(s + w)` against `x^w / w²` on `Re w = 2` and compare
`perron_vonMangoldt`, `perron_R` and `perron_xi`.
-/

open Complex MeasureTheory ArithmeticFunction

namespace Littlewood

open Erdos985.Analytic

/-- The Dirichlet polynomial `D(s, x) = Σ_{n ≤ x} Λ(n) n^{-s} log (x/n)`. -/
noncomputable def dirPoly (s : ℂ) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.range (⌊x⌋₊ + 1), (Λ n : ℂ) * (n : ℂ) ^ (-s) * (Real.log (x / n) : ℂ)

/-- The zero sum `Z(s, x) = Σ_ρ m_ρ (x^{ρ-s} - 1)/(ρ - s)²`. -/
noncomputable def zeroSum (s : ℂ) (x : ℝ) : ℂ :=
  ∑' ρ : XiZero, mult ρ * (((x : ℂ) ^ ((ρ : ℂ) - s) - 1) / ((ρ : ℂ) - s) ^ 2)

/-- **The explicit formula** (RH). -/
theorem explicit_formula (hRH : RiemannHypothesis) {s : ℂ} (hs : 1 / 2 < s.re)
    (hs1 : s ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    (Real.log x : ℂ) * (-(deriv riemannZeta s / riemannZeta s))
      = dirPoly s x + zeroSum s x - ER s x := by
  have hs0 : 0 < s.re := by linarith
  have hre : ∀ v : ℝ, 1 < (s + lineP v).re := fun v => by simp; linarith
  obtain ⟨hID, hPD⟩ := perron_vonMangoldt hs0 hx
  obtain ⟨hIR, hPR⟩ := perron_R hs0 hs1 hx
  obtain ⟨hIX, hPX⟩ := perron_xi hRH hs hx
  have hpt : ∀ v : ℝ, LSeries (fun n => (Λ n : ℂ)) (s + lineP v) =
      archR (s + lineP v) + -(deriv xiZeta (s + lineP v) / xiZeta (s + lineP v)) := by
    intro v
    have h1 : s + lineP v ≠ 1 := fun h => by have := hre v; rw [h] at this; simp at this
    rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div (hre v), neg_div,
      logDeriv_riemannZeta_eq_archR (by linarith [hre v]) h1
        (riemannZeta_ne_zero_of_one_le_re (hre v).le)]
    ring
  have hfun : (fun v : ℝ => LSeries (fun n => (Λ n : ℂ)) (s + lineP v) *
        ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2)))
      = fun v => archR (s + lineP v) * ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2)) +
          -(deriv xiZeta (s + lineP v) / xiZeta (s + lineP v)) *
            ((x : ℂ) ^ lineP v * (1 / lineP v ^ 2)) := by
    funext v; rw [hpt v]; ring
  rw [hfun, integral_add hIR hIX, mul_add, hPR, hPX] at hPD
  have hζ : riemannZeta s ≠ 0 := Lindelof.riemannZeta_ne_zero_of_RH hRH hs hs1
  rw [logDeriv_riemannZeta_eq_archR hs0 hs1 hζ]
  have hZ : ∑' ρ : XiZero, -mult ρ * (((x : ℂ) ^ ((ρ : ℂ) - s) - 1) / ((ρ : ℂ) - s) ^ 2)
      = -zeroSum s x := by
    rw [zeroSum, ← tsum_neg]; congr 1; funext ρ; ring
  rw [hZ] at hPD
  unfold dirPoly
  rw [← hPD]
  ring

end Littlewood
