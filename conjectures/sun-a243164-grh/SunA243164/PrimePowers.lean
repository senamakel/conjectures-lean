import SunA243164.TwistedSieve

/-!
# The prime-power term

`Epp x = Σ_{n < x, n not prime} Λ(n)(1 - n/x)` is at most `ψ(x) - θ(x)`, and Mathlib's
`Chebyshev.psi_eq_theta_add_sum_theta` and `Chebyshev.theta_le_log4_mul_x` bound that by
`log 4 · (√x + K · x^{1/3})` with `K = ⌊log x / log 2⌋`.
-/

namespace SunA243164.Sieve

open ArithmeticFunction Finset Chebyshev Real

lemma Epp_le_psi_sub_theta (x : ℕ) : Epp x ≤ ψ x - θ x := by
  have hψθ : ψ x - θ x = ∑ n ∈ Ioc 0 x, (Λ n : ℝ) * (if n.Prime then 0 else 1) := by
    rw [psi, theta, Nat.floor_natCast, Finset.sum_filter, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    split_ifs with h
    · rw [vonMangoldt_apply_prime h]; ring
    · ring
  rw [hψθ, Epp]
  have hsub : ∑ n ∈ range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) * (if n.Prime then 0 else 1)
      ≤ ∑ n ∈ range x, (Λ n : ℝ) * (if n.Prime then 0 else 1) := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hnx := mem_range.mp hn
    have hx0 : (0 : ℝ) < x := by exact_mod_cast (by omega : 0 < x)
    have h1 : 0 ≤ (n : ℝ) / x := by positivity
    have h0 : (0 : ℝ) ≤ (if n.Prime then 0 else 1) := by split_ifs <;> norm_num
    have hΛ : 0 ≤ (Λ n : ℝ) := vonMangoldt_nonneg
    nlinarith [mul_nonneg hΛ h0, mul_nonneg (mul_nonneg hΛ h0) h1]
  refine hsub.trans ?_
  -- `range x ⊆ {0} ∪ Ioc 0 x` and the `n = 0` term vanishes
  have hsplit : ∑ n ∈ range x, (Λ n : ℝ) * (if n.Prime then 0 else 1)
      ≤ ∑ n ∈ Ioc 0 x, (Λ n : ℝ) * (if n.Prime then 0 else 1) := by
    rcases Nat.eq_zero_or_pos x with rfl | hx
    · simp
    rw [Finset.range_eq_Ico, ← Finset.sum_Ioc_add_eq_sum_Ico_succ_bot] <;> try omega
    · simp only [vonMangoldt_apply_zero, Nat.cast_zero, zero_mul, zero_add]
      refine Finset.sum_le_sum_of_subset_of_nonneg (fun n hn => ?_) fun n _ _ => ?_
      · simp only [Finset.mem_Ioc, Finset.mem_Ico] at hn ⊢; omega
      · have : (0 : ℝ) ≤ (if n.Prime then 0 else 1) := by split_ifs <;> norm_num
        exact mul_nonneg vonMangoldt_nonneg this
  exact hsplit

/-- `Epp x ≤ log 4 · (√x + ⌊log x / log 2⌋ · x^{1/3})` for `x ≥ 2`. -/
theorem Epp_le (x : ℕ) (hx : 2 ≤ x) :
    Epp x ≤ Real.log 4 * (√(x : ℝ) + (⌊Real.log x / Real.log 2⌋₊ : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3)) := by
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set K := ⌊Real.log x / Real.log 2⌋₊
  have hψ := psi_eq_theta_add_sum_theta hxR
  have h1 := Epp_le_psi_sub_theta x
  rw [hψ, add_sub_cancel_left] at h1
  refine h1.trans ?_
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hK2 : 2 ≤ K ∨ K < 2 := le_or_lt 2 K
  -- each term is at most `log 4 · x^{1/n}`
  have hterm : ∀ n ∈ Icc 2 K, θ ((x : ℝ) ^ ((1 : ℝ) / n)) ≤ Real.log 4 * (x : ℝ) ^ ((1 : ℝ) / n) :=
    fun n _ => theta_le_log4_mul_x (by positivity)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hlog4
  rcases hK2 with hK | hK
  · rw [← Finset.add_sum_Ioc_eq_sum_Icc hK]
    have hsq : (x : ℝ) ^ ((1 : ℝ) / (2 : ℕ)) = √(x : ℝ) := by
      rw [Real.sqrt_eq_rpow]; norm_num
    rw [hsq]
    gcongr
    calc ∑ n ∈ Ioc 2 K, (x : ℝ) ^ ((1 : ℝ) / n) ≤ ∑ _n ∈ Ioc 2 K, (x : ℝ) ^ ((1 : ℝ) / 3) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hn3 : (3 : ℝ) ≤ n := by
            have := (Finset.mem_Ioc.mp hn).1; exact_mod_cast this
          apply Real.rpow_le_rpow_of_exponent_le (by linarith)
          exact one_div_le_one_div_of_le (by norm_num) hn3
      _ = ((K - 2 : ℕ) : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul]
      _ ≤ (K : ℝ) * (x : ℝ) ^ ((1 : ℝ) / 3) := by
          gcongr
          exact_mod_cast Nat.sub_le K 2
  · have : Icc 2 K = ∅ := Finset.Icc_eq_empty (by omega)
    rw [this, Finset.sum_empty]
    positivity

end SunA243164.Sieve
