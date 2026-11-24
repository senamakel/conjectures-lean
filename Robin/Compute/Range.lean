import Robin.Compute.Chain
import Robin.Compute.Chunks.Small
import Robin.Small

/-!
# `RobinVerifiedRange`, proved

* `5040 < n ≤ 10000`: `directOK` (`small_ok`).
* `10000 < n`, `log n ≤ e^{30}`: `log n ≥ log 10001 ≥ x0/XS`, and `valid_final` covers
  `x0/XS ≤ log n < cov/XS` with `cov/XS > e^{30}`.
-/

namespace Robin.Compute

open RobinCompute Real

lemma exp30_lt_cov : Real.exp 30 < ((s623.cov : ℕ) : ℝ) / XS := by
  rw [final_cov]
  have h1 : Real.exp 30 = Real.exp 1 ^ 30 := by rw [← Real.exp_nat_mul]; norm_num
  have h2 : Real.exp 1 ^ 30 < (2.7182818286 : ℝ) ^ 30 :=
    pow_lt_pow_left₀ Real.exp_one_lt_d9 (Real.exp_pos 1).le (by norm_num)
  rw [h1]
  refine h2.trans_le ?_
  unfold XS
  norm_num

theorem robinVerifiedRange_proved : Robin.RobinVerifiedRange := by
  intro n hn hlog
  have hs := small_ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hs
  obtain ⟨hdir, hx0⟩ := hs
  by_cases hsmall : n ≤ 10000
  · exact robinAt_of_directOK (hdir n (List.mem_range'_1.mpr ⟨by omega, by omega⟩))
  push Not at hsmall
  obtain ⟨-, -, -, -, -, -, hcov⟩ := valid_final
  apply hcov n (by omega) _ (lt_of_le_of_lt hlog exp30_lt_cov)
  have hD := D_pos
  have hX := XS_pos
  have hl := logLoNat_le (m := 10001) (by norm_num)
  have hx0' : (x0 : ℝ) * D ≤ XS * logLoNat 10001 := by exact_mod_cast hx0
  have hmono : Real.log (10001 : ℕ) ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hsmall)
  rw [div_le_iff₀ hX]
  have : (x0 : ℝ) * D ≤ XS * (D * Real.log (10001 : ℕ)) := by nlinarith
  have : (x0 : ℝ) ≤ XS * Real.log (10001 : ℕ) := by nlinarith
  push_cast at hmono this ⊢
  nlinarith

end Robin.Compute
