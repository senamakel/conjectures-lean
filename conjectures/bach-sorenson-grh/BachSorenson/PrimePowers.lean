import Mathlib

/-!
# Step 4: prime powers that are not primes

`Σ_{n<x, n not prime} Λ(n) ≤ ψ(x) − θ(x) = Σ_{2 ≤ k ≤ log₂ x} θ(x^{1/k})`, and with Chebyshev's
`θ(y) ≤ y log 4` (Mathlib's `Chebyshev.theta_le_log4_mul_x`) this is at most
`log 4 · (√x + x^{1/3} + x^{1/4} log x / log 2)`.
-/

namespace BachSorenson

open ArithmeticFunction Finset Real Chebyshev

/-- `Σ_{n<x, n not prime} Λ(n)`. -/
noncomputable def ppSum (x : ℕ) : ℝ := ∑ n ∈ (range x).filter (fun n => ¬ n.Prime), (Λ n : ℝ)

/-- The explicit bound on `ppSum`. -/
noncomputable def ppBound (x : ℕ) : ℝ :=
  Real.log 4 * (√(x : ℝ) + (x : ℝ) ^ ((1 : ℝ) / 3)
    + (x : ℝ) ^ ((1 : ℝ) / 4) * (Real.log x / Real.log 2))

lemma ppSum_nonneg (x : ℕ) : 0 ≤ ppSum x := sum_nonneg fun _ _ => vonMangoldt_nonneg

lemma ppSum_le_psi_sub_theta (x : ℕ) : ppSum x ≤ ψ (x : ℝ) - θ (x : ℝ) := by
  rw [psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, ppSum]
  have e : ∑ n ∈ (range x).filter (fun n => ¬ n.Prime), (Λ n : ℝ)
      = ∑ n ∈ ((range x).filter (fun n => ¬ n.Prime)).erase 0, (Λ n : ℝ) := by
    rw [sum_erase]; simp
  rw [e]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => vonMangoldt_nonneg
  intro n hn
  simp only [mem_erase, mem_filter, mem_range] at hn
  simp only [mem_filter, mem_Ioc]
  exact ⟨⟨Nat.pos_of_ne_zero hn.1, hn.2.1.le⟩, hn.2.2⟩

theorem ppSum_le (x : ℕ) (hx : 2 ≤ x) : ppSum x ≤ ppBound x := by
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hx1 : (1 : ℝ) ≤ x := by linarith
  refine (ppSum_le_psi_sub_theta x).trans ?_
  rw [psi_eq_theta_add_sum_theta hxR, add_sub_cancel_left]
  set N := ⌊Real.log x / Real.log 2⌋₊
  set f : ℕ → ℝ := fun n => θ ((x : ℝ) ^ ((1 : ℝ) / n))
  have hf0 : ∀ n, 0 ≤ f n := fun n => theta_nonneg _
  have hfle : ∀ n, f n ≤ Real.log 4 * (x : ℝ) ^ ((1 : ℝ) / n) := fun n =>
    theta_le_log4_mul_x (rpow_nonneg hx0 _)
  have hsub : Icc 2 N ⊆ insert 2 (insert 3 (Icc 4 N)) := by
    intro n hn
    simp only [mem_Icc] at hn
    simp only [mem_insert, mem_Icc]
    omega
  have h2 : (2 : ℕ) ∉ insert 3 (Icc 4 N) := by simp
  have h3 : (3 : ℕ) ∉ Icc 4 N := by simp
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have htail : ∑ n ∈ Icc 4 N, f n ≤ Real.log 4 * ((x : ℝ) ^ ((1 : ℝ) / 4) * N) := by
    calc ∑ n ∈ Icc 4 N, f n ≤ ∑ _n ∈ Icc 4 N, Real.log 4 * (x : ℝ) ^ ((1 : ℝ) / 4) := by
          refine sum_le_sum fun n hn => (hfle n).trans ?_
          have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast (mem_Icc.1 hn).1
          gcongr
      _ = (Icc 4 N).card * (Real.log 4 * (x : ℝ) ^ ((1 : ℝ) / 4)) := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ N * (Real.log 4 * (x : ℝ) ^ ((1 : ℝ) / 4)) := by
          gcongr
          rw [Nat.card_Icc]; omega
      _ = _ := by ring
  have hN : (N : ℝ) ≤ Real.log x / Real.log 2 :=
    Nat.floor_le (div_nonneg (Real.log_nonneg hx1) (Real.log_nonneg (by norm_num)))
  have hsq : (x : ℝ) ^ ((1 : ℝ) / (2 : ℕ)) = √(x : ℝ) := by
    rw [Real.sqrt_eq_rpow]; norm_num
  calc ∑ n ∈ Icc 2 N, f n ≤ ∑ n ∈ insert 2 (insert 3 (Icc 4 N)), f n :=
        sum_le_sum_of_subset_of_nonneg hsub fun n _ _ => hf0 n
    _ = f 2 + (f 3 + ∑ n ∈ Icc 4 N, f n) := by rw [sum_insert h2, sum_insert h3]
    _ ≤ Real.log 4 * √(x : ℝ) + (Real.log 4 * (x : ℝ) ^ ((1 : ℝ) / 3)
          + Real.log 4 * ((x : ℝ) ^ ((1 : ℝ) / 4) * (Real.log x / Real.log 2))) := by
        have e2 := hfle 2
        rw [hsq] at e2
        have e3 := hfle 3
        push_cast at e3
        have : Real.log 4 * ((x : ℝ) ^ ((1 : ℝ) / 4) * N)
            ≤ Real.log 4 * ((x : ℝ) ^ ((1 : ℝ) / 4) * (Real.log x / Real.log 2)) := by
          gcongr
        linarith
    _ = ppBound x := by unfold ppBound; ring

end BachSorenson
