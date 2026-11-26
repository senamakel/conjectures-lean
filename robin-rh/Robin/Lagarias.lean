import Robin.Main
import Robin.Lagarias.Finite

/-!
# Lagarias's inequality from RH

Lagarias (2002), "An elementary problem equivalent to the Riemann hypothesis", §3:
under RH, `σ(n) ≤ H_n + exp(H_n) log H_n` for every `n ≥ 1`.

* `n > 5040`: Robin's inequality `σ(n) < e^γ n log log n` (`Robin.robin_of_RH_of_verified`,
  which takes the computed range `RobinVerifiedRange` as a hypothesis) together with
  `H_n ≥ log n + γ`, which gives `exp H_n ≥ e^γ n` and `log H_n ≥ log log n`.
* `1 ≤ n ≤ 5040`: the certified finite check `Robin.Lagarias.lagarias_le_5040`.
-/

namespace Robin

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- **Lagarias's inequality** under the Riemann hypothesis, with the computed range of Robin's
inequality as an explicit hypothesis. -/
theorem lagarias_of_RH_of_verified (hRH : RiemannHypothesis) (hcomp : RobinVerifiedRange) :
    LagariasStatement := by
  intro n hn
  by_cases hsmall : n ≤ 5040
  · exact Lagarias.lagarias_le_5040 hn hsmall
  push Not at hsmall
  have hrob := robin_of_RH_of_verified hRH hcomp n hsmall
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hHn := Lagarias.log_add_gamma_le_harmonic hn
  have hγ : 0 < Real.eulerMascheroniConstant :=
    lt_trans (by norm_num) Real.one_half_lt_eulerMascheroniConstant
  have hlogn : 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt hn0]
    have := Real.exp_one_lt_d9
    have : (5040 : ℝ) < n := by exact_mod_cast hsmall
    linarith
  have hloglog : Real.log (Real.log n) ≤ Real.log (harmonic n) :=
    Real.log_le_log (by linarith) (by linarith)
  have hll0 : 0 < Real.log (Real.log n) := Real.log_pos hlogn
  have hexp : Real.exp Real.eulerMascheroniConstant * n ≤ Real.exp (harmonic n) := by
    calc Real.exp Real.eulerMascheroniConstant * n
        = Real.exp (Real.log n + Real.eulerMascheroniConstant) := by
          rw [Real.exp_add, Real.exp_log hn0]; ring
      _ ≤ _ := Real.exp_le_exp.mpr hHn
  have hprod : Real.exp Real.eulerMascheroniConstant * n * Real.log (Real.log n) ≤
      Real.exp (harmonic n) * Real.log (harmonic n) :=
    mul_le_mul hexp hloglog hll0.le (Real.exp_pos _).le
  have hH0 : (0 : ℝ) ≤ harmonic n := by linarith
  linarith

end Robin
