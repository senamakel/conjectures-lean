import LLS.L1.Final

/-!
# Definitions for LLS Theorem 1.5 with the paper's constants

For a primitive `χ` mod `N` of parity `𝔞 ∈ {0, 1}`:

* `Gpar 𝔞 = Re G(1)`, `G(s) = −½ log π + ½ ψ((s + 𝔞)/2)` (`Erdos985.Analytic.gammaLogDeriv`);
* `G3par 𝔞 = Re G(3)`;
* `ELpar 𝔞 x ≤ Re(Γₛ(x) + (1 − 1/x) G(3)) ≤ EUpar 𝔞 x`, the gamma part of the shifted Cesàro
  formula (LLS Lemma 2.3's `−½(1 − 1/x) log π + E_𝔞(x)`), per parity;
* `Wsum χ x = Σ_{n ≤ x} Λ(n) χ(n) (1/(n log n) − 1/(x log x))`, the sum of LLS Lemma 5.1.
-/

namespace LLS.Sharp

open Real
open ArithmeticFunction (vonMangoldt)
open scoped ArithmeticFunction.vonMangoldt

/-- `Re G(1)` for parity `𝔞`: `−½ log π − log 2 − γ/2` (even), `−½ log π − γ/2` (odd). -/
noncomputable def Gpar (a : ℕ) : ℝ :=
  if a = 0 then -(1 / 2) * log π - log 2 - eulerMascheroniConstant / 2
  else -(1 / 2) * log π - eulerMascheroniConstant / 2

/-- `Re G(3)` for parity `𝔞`: `−½ log π + 1 − log 2 − γ/2` (even), `−½ log π + ½ − γ/2` (odd). -/
noncomputable def G3par (a : ℕ) : ℝ :=
  if a = 0 then -(1 / 2) * log π + 1 - log 2 - eulerMascheroniConstant / 2
  else -(1 / 2) * log π + 1 / 2 - eulerMascheroniConstant / 2

/-- Lower bound for the gamma part of the shifted Cesàro formula, parity `𝔞`. -/
noncomputable def ELpar (a : ℕ) (x : ℝ) : ℝ :=
  if a = 0 then (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * log x) - 1 / 3 + (1 - 1 / x) * G3par 0
  else -(1 / 2) + (1 - 1 / x) * G3par 1

/-- Upper bound for the gamma part of the shifted Cesàro formula, parity `𝔞`. -/
noncomputable def EUpar (a : ℕ) (x : ℝ) : ℝ :=
  if a = 0 then
    (1 - 1 / x) / 3 - (1 - 1 / x - 1 / x * log x) - 1 / 3 + 3 / 2 * (1 / x) + (1 - 1 / x) * G3par 0
  else (3 * (1 / x) - 1) / 2 + (1 - 1 / x) * G3par 1

/-- `W(χ, x) = Σ_{n ≤ x} Λ(n) χ(n) (1/(n log n) − 1/(x log x))` (LLS Lemma 5.1). -/
noncomputable def Wsum {M : ℕ} (χ : DirichletCharacter ℂ M) (x : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (x + 1),
    (Λ n : ℂ) * χ n * ((1 / ((n : ℝ) * Real.log n) - 1 / ((x : ℝ) * Real.log x) : ℝ) : ℂ)

end LLS.Sharp
