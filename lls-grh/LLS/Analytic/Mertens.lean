import LLS.Defs

/-! # An unconditional Mertens-type lower bound

`Σ_{n<x} Λ(n)/n · (1 − n/x) = (1/x) Σ_{k<x} A(k)` with `A(k) = Σ_{n≤k} Λ(n)/n`, and
`k A(k) ≥ log k!` (Chebyshev's identity `log k! = Σ_{d≤k} Λ(d) ⌊k/d⌋`), together with Stirling's
lower bound `log k! ≥ k log k − k + ½ log k + ½ log 2π` (Mathlib).
-/

namespace LLS

open ArithmeticFunction Finset

/-- `Σ_{k<x} Σ_{n≤k} a n = Σ_{n<x} a n (x − n)`. -/
lemma sum_range_sum_range_succ (a : ℕ → ℝ) (x : ℕ) :
    ∑ k ∈ range x, ∑ n ∈ range (k + 1), a n = ∑ n ∈ range x, a n * ((x : ℝ) - n) := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [sum_range_succ, ih, sum_range_succ, sum_range_succ (fun n => a n * (((x + 1 : ℕ) : ℝ) - n))]
    have : ∑ n ∈ range x, a n * (((x + 1 : ℕ) : ℝ) - n)
        = ∑ n ∈ range x, a n * ((x : ℝ) - n) + ∑ n ∈ range x, a n := by
      rw [← sum_add_distrib]; refine sum_congr rfl fun n _ => ?_; push_cast; ring
    rw [this]; push_cast; ring

lemma sum_Ioc_zero_eq (g : ℕ → ℝ) (k : ℕ) :
    ∑ n ∈ Ioc 0 k, g n = ∑ i ∈ range k, g (i + 1) := by
  induction k with
  | zero => simp
  | succ k ih => rw [Finset.sum_Ioc_succ_top (by omega), ih, sum_range_succ]

lemma log_factorial_eq (k : ℕ) :
    Real.log (k.factorial) = ∑ i ∈ range k, Real.log ((i : ℝ) + 1) := by
  rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod,
    Real.log_prod fun i _ => by positivity]
  push_cast; rfl

/-- Chebyshev: `log k! ≤ k Σ_{n≤k} Λ(n)/n`. -/
lemma log_factorial_le (k : ℕ) :
    Real.log (k.factorial) ≤ k * ∑ n ∈ range (k + 1), (Λ n : ℝ) / n := by
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
  have h3 : ∑ d ∈ Ioc 0 k, ∑ n ∈ (Ioc 0 k).filter (d ∣ ·), (Λ d : ℝ)
      = ∑ d ∈ Ioc 0 k, (Λ d : ℝ) * ((k / d : ℕ) : ℝ) := by
    refine sum_congr rfl fun d _ => ?_
    rw [sum_const, Nat.Ioc_filter_dvd_card_eq_div, nsmul_eq_mul, mul_comm]
  rw [h3]
  have h4 : ∑ n ∈ range (k + 1), (Λ n : ℝ) / n = ∑ n ∈ Ioc 0 k, (Λ n : ℝ) / n := by
    rw [sum_range_succ', sum_Ioc_zero_eq]; simp
  rw [h4, mul_sum]
  refine sum_le_sum fun d hd => ?_
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (mem_Ioc.1 hd).1
  have hΛ : (0 : ℝ) ≤ Λ d := vonMangoldt_nonneg
  have : ((k / d : ℕ) : ℝ) ≤ (k : ℝ) / d := Nat.cast_div_le
  calc (Λ d : ℝ) * ((k / d : ℕ) : ℝ) ≤ Λ d * ((k : ℝ) / d) := mul_le_mul_of_nonneg_left this hΛ
    _ = k * ((Λ d : ℝ) / d) := by ring

lemma log_succ_sub_log_le {k : ℕ} (hk : 1 ≤ k) :
    Real.log (k + 1) - Real.log k ≤ 1 / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  rw [← Real.log_div (by positivity) hk0.ne']
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (k + 1) / k by positivity)
  have e : ((k : ℝ) + 1) / k - 1 = 1 / k := by field_simp; ring
  linarith

/-- Per-`k` lower bound: `A(k) ≥ log k − 1 + ½ (log (k+1) − log k)`. -/
lemma A_ge {k : ℕ} (hk : 1 ≤ k) :
    Real.log k - 1 + (Real.log (k + 1) - Real.log k) / 2
      ≤ ∑ n ∈ range (k + 1), (Λ n : ℝ) / n := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hS := Stirling.le_log_factorial_stirling (n := k) (by omega)
  have hC := log_factorial_le k
  have hlk : 0 ≤ Real.log k := Real.log_nonneg (by exact_mod_cast hk)
  have h2pi : 1 ≤ Real.log (2 * Real.pi) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; have := Real.pi_gt_three; linarith
  have hd := log_succ_sub_log_le hk
  -- k * A ≥ k log k − k + (log k)/2 + (log 2π)/2 ≥ k(log k − 1) + 1/2
  have hA : k * (Real.log k - 1) + 1 / 2 ≤ k * ∑ n ∈ range (k + 1), (Λ n : ℝ) / n := by
    nlinarith
  have hA' : Real.log k - 1 + 1 / (2 * k) ≤ ∑ n ∈ range (k + 1), (Λ n : ℝ) / n := by
    have e : Real.log k - 1 + 1 / (2 * k) = (k * (Real.log k - 1) + 1 / 2) / k := by
      field_simp
    rw [e, div_le_iff₀ hk0]; linarith
  have : (Real.log (k + 1) - Real.log k) / 2 ≤ 1 / (2 * k) := by
    rw [show (1 : ℝ) / (2 * k) = (1 / k) / 2 by ring]; linarith
  linarith

/-- `Σ_{n < x} Λ(n)/n · (1 − n/x) ≥ log x − 2` for `x ≥ 2` (unconditional). -/
theorem vonMangoldt_ces_ge (x : ℕ) (hx : 2 ≤ x) :
    Real.log x - 2 ≤ ∑ n ∈ Finset.range x, (Λ n : ℝ) / n * (1 - (n : ℝ) / x) := by
  have hx0 : (0 : ℝ) < x := by positivity
  set a : ℕ → ℝ := fun n => (Λ n : ℝ) / n
  have hid : ∑ n ∈ range x, (Λ n : ℝ) / n * (1 - (n : ℝ) / x)
      = (1 / x) * ∑ k ∈ range x, ∑ n ∈ range (k + 1), a n := by
    rw [sum_range_sum_range_succ, mul_sum]
    refine sum_congr rfl fun n _ => ?_
    simp only [a]; field_simp
  rw [hid]
  -- split off k = 0
  obtain ⟨m, rfl⟩ : ∃ m, x = m + 1 := ⟨x - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  rw [sum_range_succ']
  simp only [zero_add, range_one, sum_singleton, a, ArithmeticFunction.map_zero, Nat.cast_zero,
    div_zero, add_zero]
  -- Σ_{k<m} A(k+1) ≥ Σ_{k<m} (log(k+1) − 1) + ½ log(m+1)
  have hsum : ∑ k ∈ range m, (Real.log (k + 1 : ℕ) - 1
        + (Real.log ((k + 1 : ℕ) + 1) - Real.log (k + 1 : ℕ)) / 2)
      ≤ ∑ k ∈ range m, ∑ n ∈ range (k + 1 + 1), (Λ n : ℝ) / n :=
    sum_le_sum fun k _ => A_ge (by omega)
  have htel : ∑ k ∈ range m, (Real.log ((k + 1 : ℕ) + 1) - Real.log (k + 1 : ℕ))
      = Real.log (m + 1 : ℕ) := by
    have := Finset.sum_range_sub (fun k : ℕ => Real.log ((k + 1 : ℕ) : ℝ)) m
    simp only [Nat.cast_add, Nat.cast_one, zero_add, Real.log_one,
      sub_zero] at this ⊢
    rw [← this]
  have hfac : ∑ k ∈ range m, Real.log (k + 1 : ℕ) = Real.log (m.factorial) := by
    rw [log_factorial_eq]; push_cast; rfl
  have hsplit : ∑ k ∈ range m, (Real.log (k + 1 : ℕ) - 1
        + (Real.log ((k + 1 : ℕ) + 1) - Real.log (k + 1 : ℕ)) / 2)
      = Real.log (m.factorial) - m + Real.log (m + 1 : ℕ) / 2 := by
    rw [sum_add_distrib, sum_sub_distrib, ← sum_div, htel, hfac, sum_const, card_range, nsmul_eq_mul, mul_one]
  rw [hsplit] at hsum
  have hS := Stirling.le_log_factorial_stirling (n := m) (by omega)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h2pi : 1 ≤ Real.log (2 * Real.pi) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    have := Real.exp_one_lt_d9; have := Real.pi_gt_three; linarith
  have hlogd : Real.log ((m : ℝ) + 1) - Real.log m ≤ 1 / m := log_succ_sub_log_le hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hl2 : Real.log ((m : ℝ) + 1) - Real.log m ≤ Real.log 2 := by
    rw [← Real.log_div (by positivity) hm0.ne']
    exact Real.log_le_log (by positivity) (by rw [div_le_iff₀ hm0]; linarith)
  have hl2' := Real.log_two_lt_d9
  have e : m * Real.log ((m : ℝ) + 1) - m * Real.log m ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hlogd hm0.le
    rw [mul_one_div_cancel hm0.ne', mul_sub] at this; exact this
  push_cast at hsum ⊢
  have key : ((m : ℝ) + 1) * (Real.log ((m : ℝ) + 1) - 2)
      ≤ ∑ k ∈ range m, ∑ n ∈ range (k + 1 + 1), (Λ n : ℝ) / n := by
    nlinarith
  rw [show Real.log ((m : ℝ) + 1) - 2
      = 1 / ((m : ℝ) + 1) * (((m : ℝ) + 1) * (Real.log ((m : ℝ) + 1) - 2)) by field_simp]
  exact mul_le_mul_of_nonneg_left key (by positivity)

end LLS
