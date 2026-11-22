import Robin.Statement
import Robin.RH.Bach
import Robin.Elementary.SigmaBound
import Robin.Main.Estimate
import Robin.Small

/-!
# Robin's theorem: RH implies `σ(n) < e^γ n log log n` for `n > 5040`

* `5040 < n ≤ exp(e^{30})`: `robin_small_range` (cited computation of Morrill–Platt).
* `log n > e^{30}`: put `x = log n`, `ε = log(1+1/x)/log x`. Then
  `log(σ(n)/n) ≤ ε(x − θ(x)) + Σ_{p≤x} c_p − Σ_{p≤x} min(1/p², ε log p)` (`log_sigma_div_le`),
  and the right side is `< γ + log log x` (`main_estimate`, which uses RH through `Ψ₁`).
-/

namespace Robin

open ArithmeticFunction Real Chebyshev
open scoped ArithmeticFunction.sigma

theorem primeSum_eps_log (e x : ℝ) :
    primeSum (fun p => cp p - e * Real.log p) x = primeSum cp x - e * θ x := by
  unfold primeSum
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, theta]
  congr 2

/-- **Robin's theorem** (1984). -/
theorem robin_of_RH (hRH : RiemannHypothesis) : RobinStatement := by
  intro n hn
  by_cases hsmall : Real.log n ≤ Real.exp 30
  · exact robin_small_range n hn hsmall
  push Not at hsmall
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have he30 : (3 : ℝ) ≤ Real.exp 30 := by
    have := Real.add_one_le_exp (30 : ℝ); linarith
  have hx3 : 3 ≤ Real.log n := by linarith
  have hsig := log_sigma_div_le (n := n) (by omega) hx3
  rw [primeSum_eps_log] at hsig
  have hmain := main_estimate (psi1NatBound_of_RH hRH) hsmall.le
  have hlt : Real.log ((σ 1 n : ℝ) / n) <
      Real.eulerMascheroniConstant + Real.log (Real.log (Real.log n)) := by linarith
  have hσpos : (0 : ℝ) < σ 1 n := by
    have : 0 < σ 1 n := by
      rw [sigma_pos_iff]; omega
    exact_mod_cast this
  have h := Real.exp_lt_exp.mpr hlt
  rw [Real.exp_log (div_pos hσpos hn0), Real.exp_add, Real.exp_log (Real.log_pos (by linarith))] at h
  rw [div_lt_iff₀ hn0] at h
  linarith [h]

end Robin
