import Schoenfeld.ThetaSharp
import Schoenfeld.SmallRange

/-!
# Schoenfeld's ψ and θ bounds with the constant `1/(8π)`

* `schoenfeldPsi_of_RH_of_inputs`: `SchoenfeldPsi` from RH, Rosser's zero count, PsiCert and
  `PsiSmallRange`: `[73.2, 1500]` by `PsiSmallRange`, `[1500, 10¹⁰]` by PsiCert
  (`0.8 < log² x/(8π)`), `x ≥ 10¹⁰` by `psi_sharp_large`.
* `schoenfeldTheta_of_RH_of_inputs`: `SchoenfeldTheta` from the same inputs with `ThetaSmallRange`:
  `[599, 3·10⁴]`, then `theta_mid` and `theta_sharp_large`.
-/

namespace Schoenfeld

open Real Chebyshev

/-- On `[1500, 10¹⁰]`, PsiCert gives Schoenfeld's ψ bound. -/
theorem psi_sharp_mid (hC : PsiCert) {x : ℝ} (h1 : 1500 ≤ x) (h2 : x ≤ 10 ^ 10) :
    |ψ x - x| < 1 / (8 * π) * (√x * Real.log x ^ 2) := by
  have hc := hC x h1 h2
  have hs : 0 < √x := Real.sqrt_pos.mpr (by linarith)
  have hl : 7 ≤ Real.log x := by
    have := log_ge_of_pow_le 10 (show (2 : ℝ) ^ 10 ≤ x by norm_num; linarith)
    have : (2 : ℝ) ^ 10 / x ≤ 1024 / 1500 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; norm_num; linarith
    norm_num at *; linarith
  have hp := Real.pi_lt_d4
  have : 4 / 5 * √x < 1 / (8 * π) * (√x * Real.log x ^ 2) := by
    rw [show 1 / (8 * π) * (√x * Real.log x ^ 2) = √x * (Real.log x ^ 2 / (8 * π)) by ring,
      mul_comm]
    apply mul_lt_mul_of_pos_left _ hs
    rw [lt_div_iff₀ (by positivity)]
    nlinarith
  linarith

/-- **Schoenfeld's ψ bound** (Theorem 10, (6.2)): `|ψ(x) − x| < √x log² x/(8π)` for `x ≥ 73.2`,
from RH, Rosser's zero count, PsiCert and the range `[73.2, 1500]`. -/
theorem schoenfeldPsi_of_RH_of_inputs (hRH : RiemannHypothesis) (hR : RosserZeroCount) (hC : PsiCert)
    (hS : PsiSmallRange) : SchoenfeldPsi := by
  intro x hx
  rcases le_or_gt x 1500 with h | h
  · exact hS x hx h
  rcases le_or_gt x (10 ^ 10) with h' | h'
  · exact psi_sharp_mid hC h.le h'
  · exact psi_sharp_large hRH hR h'.le

/-- **Schoenfeld's θ bound** (Theorem 10, (6.3)): `|θ(x) − x| < √x log² x/(8π)` for `x ≥ 599`,
from RH, Rosser's zero count, PsiCert and the range `[599, 3·10⁴]`. -/
theorem schoenfeldTheta_of_RH_of_inputs (hRH : RiemannHypothesis) (hR : RosserZeroCount) (hC : PsiCert)
    (hS : ThetaSmallRange) : SchoenfeldTheta := by
  intro x hx
  rcases le_or_gt x 30000 with h | h
  · exact hS x hx h
  rcases le_or_gt x (10 ^ 10) with h' | h'
  · exact theta_mid hC h.le h'
  · exact theta_sharp_large hRH hR hC h'.le

end Schoenfeld
