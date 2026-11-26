import Nicolas.Mertens
import Nicolas.Tail

/-!
# The analytic range `x ≥ 10^5`

Under `Psi1NatBound` (a consequence of RH, robin-rh's `psi1NatBound_of_RH`), for real
`x ≥ 10^5`: `γ + log log θ(x) < Σ_{p≤x} c_p`.

By `mertens_eq`, `Σ c_p = γ + log log x + (θ − x)/(x log x) + J(x) − T(x)` with
`J(x) = −∫_x^∞ (θ − t) w ≥ 0.86/(√x log x)` (`tail_lower`) and `0 ≤ T(x) ≤ 4/x`
(`tailK_le_div`), while `log log θ(x) ≤ log log x + (θ − x)/(x log x)` (`loglog_theta_le`).
The difference is `J − T ≥ 0.86/(√x log x) − 4/x > 0` because `4 log x < 0.86 √x`.
-/

namespace Nicolas

open Real Chebyshev Robin

lemma log_ge_11 {x : ℝ} (hx : 100000 ≤ x) : 11 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have h : Real.exp 11 = Real.exp 1 ^ 11 := by rw [← Real.exp_nat_mul]; norm_num
  have he := Real.exp_one_lt_d9
  have : Real.exp 1 ^ 11 ≤ (2.7182818286 : ℝ) ^ 11 :=
    pow_le_pow_left₀ (Real.exp_pos 1).le he.le 11
  rw [h]
  linarith [show (2.7182818286 : ℝ) ^ 11 ≤ 100000 by norm_num]

/-- `4 log x < 0.86 √x` for `x ≥ 10^5`. -/
lemma four_log_lt {x : ℝ} (hx : 100000 ≤ x) : 4 * Real.log x < 0.86 * √x := by
  have hx0 : 0 < x := by linarith
  have hlog := Real.log_le_rpow_div hx0.le (show (0 : ℝ) < 1 / 5 by norm_num)
  have hsplit : √x = x ^ ((1 : ℝ) / 5) * x ^ ((3 : ℝ) / 10) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]; norm_num
  have h31 : 31 ≤ x ^ ((3 : ℝ) / 10) := by
    by_contra h
    push Not at h
    have h0 : 0 ≤ x ^ ((3 : ℝ) / 10) := Real.rpow_nonneg hx0.le _
    have h10 : (x ^ ((3 : ℝ) / 10)) ^ (10 : ℕ) = x ^ 3 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    have hlt : (x ^ ((3 : ℝ) / 10)) ^ (10 : ℕ) < 31 ^ 10 := pow_lt_pow_left₀ h h0 (by norm_num)
    rw [h10] at hlt
    have : (100000 : ℝ) ^ 3 ≤ x ^ 3 := pow_le_pow_left₀ (by norm_num) hx 3
    norm_num at hlt this
    linarith
  have h5 : 0 < x ^ ((1 : ℝ) / 5) := Real.rpow_pos_of_pos hx0 _
  rw [hsplit]
  have : Real.log x ≤ 5 * x ^ ((1 : ℝ) / 5) := by
    rw [div_div_eq_mul_div, div_one] at hlog
    linarith [show x ^ ((1 : ℝ) / 5) / (1 / 5) = 5 * x ^ ((1 : ℝ) / 5) by ring]
  nlinarith

/-- **Analytic range.** Under `Psi1NatBound`, `γ + log log θ(x) < Σ_{p≤x} c_p` for `x ≥ 10^5`. -/
theorem sum_cp_gt_large (hB : Psi1NatBound) {x : ℝ} (hx : 100000 ≤ x) :
    Real.eulerMascheroniConstant + Real.log (Real.log (θ x)) < primeSum cp x := by
  have hx0 : 0 < x := by linarith
  have hL := log_ge_11 hx
  have hL0 : 0 < Real.log x := by linarith
  obtain ⟨-, hM⟩ := mertens_eq (theta_sub_bound hB) (show (2 : ℝ) ≤ x by linarith)
  obtain ⟨-, hJ⟩ := tail_lower hB hx hL
  have hT := tailK_le_div hx0
  have hθ := loglog_theta_le (show (3 : ℝ) ≤ x by linarith)
  have hcmp : 4 / x < 0.86 / (√x * Real.log x) := by
    have hs : 0 < √x := Real.sqrt_pos.mpr hx0
    rw [div_lt_div_iff₀ hx0 (by positivity)]
    have := four_log_lt hx
    calc 4 * (√x * Real.log x) = √x * (4 * Real.log x) := by ring
      _ < √x * (0.86 * √x) := mul_lt_mul_of_pos_left this hs
      _ = 0.86 * x := by
        rw [show √x * (0.86 * √x) = 0.86 * (√x * √x) by ring, Real.mul_self_sqrt hx0.le]
  linarith

end Nicolas
