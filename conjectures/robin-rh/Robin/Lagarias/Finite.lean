import Robin.Statement
import Robin.Lagarias.Bounds
import Erdos985.Analytic.Digamma.EulerMascheroni

/-!
# Lagarias's inequality for `1 ≤ n ≤ 5040`

* `1 ≤ n ≤ 12`: exact rational `H_n`, `exp H_n ≥ expLower H_n`, `log H_n ≥ L` certified by
  `expUpper L ≤ H_n`.
* `13 ≤ n ≤ 5040`: `H_n ≥ log n + γ` (Mathlib), `γ > 0.57688` (Erdos985), hence
  `exp H_n ≥ e^{0.57688} n`, `H_n ≥ t + 0.57688` and `log H_n ≥ L` for certified rationals
  `t ≤ log n`, `L ≤ log (t + 0.57688)`.
-/

namespace Robin.Lagarias

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- Computable `σ₁`. -/
def sig (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

lemma sigma_one_eq_sig (n : ℕ) : σ 1 n = sig n := by
  rw [sigma_one_apply, sig]

/-- Rational lower bound for Euler's constant (`Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt`). -/
def gLow : ℚ := 57688 / 100000

/-- Rational lower bound for `exp gLow`. -/
def eg : ℚ := expLower gLow

/-- Certificate for small `n`, using the exact rational `H_n`. -/
def smallCheck (n : ℕ) : Bool :=
  let H := harmonic n
  let L := logLo H
  decide (0 ≤ L ∧ expUpper L ≤ H ∧ (sig n : ℚ) ≤ H + expLower H * L)

/-- Certificate for medium `n`, using `H_n ≥ log n + γ`. -/
def midCheck (n : ℕ) : Bool :=
  let t := logLo n
  let L := logLo (t + gLow)
  decide (0 ≤ t ∧ 0 ≤ L ∧ expUpper t ≤ n ∧ expUpper L ≤ t + gLow ∧
    (sig n : ℚ) ≤ t + gLow + eg * n * L)

/-- `H_n ≥ log n + γ` for `n ≥ 1`. -/
lemma log_add_gamma_le_harmonic {n : ℕ} (hn : 1 ≤ n) :
    Real.log n + Real.eulerMascheroniConstant ≤ (harmonic n : ℝ) := by
  have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' n
  have hn0 : n ≠ 0 := by omega
  simp only [Real.eulerMascheroniSeq', hn0, ↓reduceIte] at h
  linarith

lemma ineq_of_smallCheck {n : ℕ} (h : smallCheck n = true) :
    (σ 1 n : ℝ) ≤ (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n) := by
  simp only [smallCheck, decide_eq_true_eq] at h
  obtain ⟨hL0, hLup, hsig⟩ := h
  set H := harmonic n
  set L := logLo H
  have hlog : (L : ℝ) ≤ Real.log (H : ℝ) := le_log_of_expUpper_le hL0 (by exact_mod_cast hLup)
  have hH0 : (0 : ℚ) ≤ H := by
    simp only [H, harmonic]; positivity
  have hexp : ((expLower H : ℚ) : ℝ) ≤ Real.exp H := expLower_le_exp hH0
  have hsigR : ((sig n : ℚ) : ℝ) ≤ ((H + expLower H * L : ℚ) : ℝ) := by exact_mod_cast hsig
  push_cast at hsigR
  rw [sigma_one_eq_sig]
  have : ((expLower H : ℚ) : ℝ) * L ≤ Real.exp H * Real.log H :=
    mul_le_mul hexp hlog (by exact_mod_cast hL0) (Real.exp_pos _).le
  linarith

lemma ineq_of_midCheck {n : ℕ} (hn : 1 ≤ n) (h : midCheck n = true) :
    (σ 1 n : ℝ) ≤ (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n) := by
  simp only [midCheck, decide_eq_true_eq] at h
  obtain ⟨ht0, hL0, htup, hLup, hsig⟩ := h
  set t := logLo n
  set L := logLo (t + gLow)
  have hγ : ((gLow : ℚ) : ℝ) < Real.eulerMascheroniConstant := by
    have := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
    simp only [gLow]; push_cast; linarith
  have hlogn : (t : ℝ) ≤ Real.log n := by
    have := le_log_of_expUpper_le (y := (n : ℝ)) ht0 (by exact_mod_cast htup)
    exact this
  have hHn := log_add_gamma_le_harmonic hn
  have hH : ((t + gLow : ℚ) : ℝ) ≤ harmonic n := by push_cast; linarith
  have hlogH : (L : ℝ) ≤ Real.log (harmonic n) :=
    le_log_of_expUpper_le hL0 (le_trans (by exact_mod_cast hLup) hH)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hexpH : (eg : ℝ) * n ≤ Real.exp (harmonic n) := by
    have h1 : (eg : ℝ) ≤ Real.exp Real.eulerMascheroniConstant :=
      (expLower_le_exp (by simp [gLow]; norm_num)).trans (Real.exp_le_exp.mpr hγ.le)
    have h2 : Real.exp Real.eulerMascheroniConstant * n ≤ Real.exp (harmonic n) := by
      calc Real.exp Real.eulerMascheroniConstant * n
          = Real.exp (Real.log n + Real.eulerMascheroniConstant) := by
            rw [Real.exp_add, Real.exp_log hn0]; ring
        _ ≤ _ := Real.exp_le_exp.mpr hHn
    nlinarith
  have hprod : (eg : ℝ) * n * L ≤ Real.exp (harmonic n) * Real.log (harmonic n) :=
    mul_le_mul hexpH hlogH (by exact_mod_cast hL0) (Real.exp_pos _).le
  have hsigR : ((sig n : ℚ) : ℝ) ≤ ((t + gLow + eg * n * L : ℚ) : ℝ) := by exact_mod_cast hsig
  push_cast at hsigR hH hprod
  rw [sigma_one_eq_sig]
  linarith

/-- Finite check: `smallCheck n = true` for every `n ∈ [1, 12]`, i.e. with `H = H_n` (exact
rational) and `L = logLo H`: `0 ≤ L`, `expUpper L ≤ H` and `σ(n) ≤ H + expLower H · L`.
Checked by the kernel (`decide +kernel`). -/
theorem smallCheck_range : (List.range' 1 12).all smallCheck = true := by
  decide +kernel

/-- Finite check: `midCheck n = true` for every `n ∈ [13, 5040]`, i.e. with `t = logLo n`,
`L = logLo (t + 0.57688)`: `0 ≤ t`, `0 ≤ L`, `expUpper t ≤ n`, `expUpper L ≤ t + 0.57688` and
`σ(n) ≤ t + 0.57688 + expLower 0.57688 · n · L` (all in `ℚ`). This is the computational part of
Lagarias's inequality below Robin's range `n > 5040`. Uses `native_decide`: the check runs
`σ` by trial division and a bisection for `log` at each of the 5028 values, which is far too slow
for kernel reduction (`decide +kernel` takes minutes for 40 values). -/
theorem midCheck_range : (List.range' 13 5028).all midCheck = true := by
  native_decide

/-- Lagarias's inequality for `1 ≤ n ≤ 5040`. -/
theorem lagarias_le_5040 {n : ℕ} (hn : 1 ≤ n) (hn' : n ≤ 5040) :
    (σ 1 n : ℝ) ≤ (harmonic n : ℝ) + Real.exp (harmonic n) * Real.log (harmonic n) := by
  by_cases h12 : n ≤ 12
  · apply ineq_of_smallCheck
    have := List.all_eq_true.mp smallCheck_range n (List.mem_range'_1.mpr (by omega))
    exact this
  · apply ineq_of_midCheck hn
    have := List.all_eq_true.mp midCheck_range n (List.mem_range'_1.mpr (by omega))
    exact this

end Robin.Lagarias
