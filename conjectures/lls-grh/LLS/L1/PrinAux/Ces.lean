import LLS.Analytic.Mertens

/-!
# An unconditional upper bound `Σ_{n<N} Λ(n)/n (1 − n/N) ≤ log N − 1 + 1/N`

`N Σ_{n<N} Λ(n)/n (1 − n/N) = Σ_{d≤N−1} Λ(d)(N − d)/d ≤ Σ_{d≤N−1} Λ(d) ⌊(N−1)/d⌋ = log (N−1)!`
(Chebyshev's identity) and `log (N−1)! ≤ N log N − N + 1` (comparison with `∫_1^N log t`).
-/

namespace LLS

open ArithmeticFunction Finset

lemma log_factorial_eq_sum_floor (k : ℕ) :
    Real.log (k.factorial) = ∑ d ∈ Ioc 0 k, (Λ d : ℝ) * ((k / d : ℕ) : ℝ) := by
  have hfac : Real.log (k.factorial) = ∑ n ∈ Ioc 0 k, Real.log n := by
    rw [log_factorial_eq, sum_Ioc_zero_eq]; push_cast; rfl
  rw [hfac]
  have h1 : ∑ n ∈ Ioc 0 k, Real.log n = ∑ n ∈ Ioc 0 k, ∑ d ∈ n.divisors, (Λ d : ℝ) :=
    sum_congr rfl fun n _ => vonMangoldt_sum.symm
  have h2 : ∑ n ∈ Ioc 0 k, ∑ d ∈ n.divisors, (Λ d : ℝ)
      = ∑ d ∈ Ioc 0 k, ∑ n ∈ (Ioc 0 k).filter (d ∣ ·), (Λ d : ℝ) := by
    refine Finset.sum_comm' fun n d => ?_
    rw [mem_Ioc, Nat.mem_divisors, mem_filter, mem_Ioc, mem_Ioc]
    constructor
    · intro h
      exact ⟨⟨h.1, h.2.1⟩,
        Nat.pos_of_dvd_of_pos h.2.1 h.1.1, (Nat.le_of_dvd h.1.1 h.2.1).trans h.1.2⟩
    · intro h
      exact ⟨h.1.1, h.1.2, by omega⟩
  rw [h1, h2]
  refine sum_congr rfl fun d _ => ?_
  rw [sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]

/-- `log (N − 1)! ≤ N log N − N + 1` for `N ≥ 1`. -/
lemma log_factorial_pred_le (N : ℕ) (hN : 1 ≤ N) :
    Real.log ((N - 1).factorial) ≤ N * Real.log N - N + 1 := by
  induction N, hN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [show N + 1 - 1 = (N - 1) + 1 by omega, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity), show (N - 1 + 1 : ℕ) = N by omega]
    push_cast
    -- `(N+1) log(N+1) − N log N − 1 − log N = (N+1)(log(N+1) − log N) − 1 ≥ 0`
    have hl : 1 / ((N : ℝ) + 1) ≤ Real.log ((N : ℝ) + 1) - Real.log N := by
      rw [← Real.log_div (by positivity) hN0.ne']
      have h := Real.add_one_le_exp (-(1 / ((N : ℝ) + 1)))
      have hpos : (0 : ℝ) < ((N : ℝ) + 1) / N := by positivity
      rw [Real.le_log_iff_exp_le hpos]
      have e1 : Real.exp (1 / ((N : ℝ) + 1)) * Real.exp (-(1 / ((N : ℝ) + 1))) = 1 := by
        rw [← Real.exp_add]; simp
      have h2 : 0 < 1 - 1 / ((N : ℝ) + 1) := by
        have : 1 / ((N : ℝ) + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
        linarith
      have e2 : 1 - 1 / ((N : ℝ) + 1) = N / ((N : ℝ) + 1) := by field_simp; ring
      have h3 : Real.exp (1 / ((N : ℝ) + 1)) * (N / ((N : ℝ) + 1)) ≤ 1 := by
        calc _ ≤ Real.exp (1 / ((N : ℝ) + 1)) * Real.exp (-(1 / ((N : ℝ) + 1))) := by
              rw [← e2]; gcongr; linarith
          _ = 1 := e1
      rw [mul_div_assoc'] at h3
      rw [div_le_one (by positivity)] at h3
      rw [le_div_iff₀ hN0]
      linarith
    have : ((N : ℝ) + 1) * (1 / ((N : ℝ) + 1)) = 1 := by field_simp
    nlinarith

theorem vonMangoldt_ces_le_aux (N : ℕ) (hN : 2 ≤ N) :
    ∑ n ∈ range N, (Λ n : ℝ) / n * (1 - (n : ℝ) / N) ≤ Real.log N - 1 + 1 / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  -- the sum is `(1/N) Σ_{d ∈ (0, N−1]} Λ(d)(N − d)/d`
  have hsum : ∑ n ∈ range N, (Λ n : ℝ) / n * (1 - (n : ℝ) / N)
      = (1 / N) * ∑ d ∈ Ioc 0 (N - 1), (Λ d : ℝ) * (((N : ℝ) - d) / d) := by
    rw [mul_sum]
    have : range N = insert 0 (Ioc 0 (N - 1)) := by
      ext n; simp only [mem_range, mem_insert, mem_Ioc]; omega
    rw [this, sum_insert (by simp)]
    simp only [Nat.cast_zero, div_zero, zero_mul, zero_add, ArithmeticFunction.map_zero]
    refine sum_congr rfl fun d _ => ?_
    field_simp
  rw [hsum]
  have hfl : ∑ d ∈ Ioc 0 (N - 1), (Λ d : ℝ) * (((N : ℝ) - d) / d)
      ≤ Real.log ((N - 1).factorial) := by
    rw [log_factorial_eq_sum_floor]
    refine sum_le_sum fun d hd => ?_
    obtain ⟨hd0, hdN⟩ := mem_Ioc.1 hd
    have hΛ : (0 : ℝ) ≤ Λ d := vonMangoldt_nonneg
    refine mul_le_mul_of_nonneg_left ?_ hΛ
    have hdR : (0 : ℝ) < d := by exact_mod_cast hd0
    rw [div_le_iff₀ hdR]
    -- `((N−1)/d) d ≥ N − d`
    have h1 : N - 1 < ((N - 1) / d + 1) * d := by
      rw [add_mul, one_mul]; exact Nat.lt_div_mul_add hd0
    have h2 : N - d ≤ (N - 1) / d * d := by
      have := Nat.lt_div_mul_add (a := N - 1) hd0
      omega
    have h3 : ((N - d : ℕ) : ℝ) ≤ (((N - 1) / d * d : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast [Nat.cast_sub (show d ≤ N by omega)] at h3
    linarith
  have hst := log_factorial_pred_le N (by omega)
  have : (1 / (N : ℝ)) * (N * Real.log N - N + 1) = Real.log N - 1 + 1 / N := by field_simp
  calc (1 / (N : ℝ)) * ∑ d ∈ Ioc 0 (N - 1), (Λ d : ℝ) * (((N : ℝ) - d) / d)
      ≤ (1 / (N : ℝ)) * (N * Real.log N - N + 1) :=
        mul_le_mul_of_nonneg_left (hfl.trans hst) (by positivity)
    _ = _ := this

end LLS
