import LLS.Analytic.Principal

/-!
# Upper bound for the principal log-weighted sum under GRH

`Σ_{n ≤ x} Λ(n) log(x/n) ≤ x + (3/20)√x + 4 log x + 2`, by the summation by parts of
`LLS.psiLog_ge` run the other way: `T(N) ≤ G⁺(N) = N²/2 + N√N/20 + 3N` and `(N + ½) a_N ≤ 1 + a_N/2`.
-/

namespace LLS.Thm14

open ArithmeticFunction Erdos985 Finset LLS

/-- `G⁺(N) = N²/2 + N√N/20 + 3N`. -/
noncomputable def GP (N : ℕ) : ℝ := (N : ℝ) ^ 2 / 2 + N * √(N : ℝ) / 20 + 3 * N

lemma TN_le_GP (hGRH : DirichletLNonvanishingRightOfHalf) (N : ℕ) : TN N ≤ GP N := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [TN, GP]
  have h := (abs_le.1 (Analytic.bach_principal_of_GRH hGRH N hN)).2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : TN N = N * ∑ n ∈ range N, (Λ n : ℝ) * (1 - (n : ℝ) / N) := by
    unfold TN; rw [mul_sum]; refine sum_congr rfl fun n _ => ?_; field_simp
  rw [e]
  unfold GP
  have := mul_le_mul_of_nonneg_left (show ∑ n ∈ range N, (Λ n : ℝ) * (1 - (n : ℝ) / N)
    ≤ (N : ℝ) / 2 + √(N : ℝ) / 20 + 3 by linarith) hN0.le
  nlinarith

/-- `Σ_{n ≤ x} Λ(n) log(x/n) ≤ x + (3/20)√x + 4 log x + 2` under GRH. -/
theorem psiLog_le (hGRH : DirichletLNonvanishingRightOfHalf) (x : ℕ) (hx : 1 ≤ x) :
    ∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * Real.log ((x : ℝ) / n)
      ≤ (x : ℝ) + 3 / 20 * √(x : ℝ) + 4 * Real.log x + 2 := by
  have hlog2 := Real.log_two_lt_d9
  rcases Nat.lt_or_ge x 2 with hx2 | hx2
  · have : x = 1 := by omega
    subst this
    simp [sum_range_succ]
    norm_num
  obtain ⟨k, rfl⟩ : ∃ k, x = k + 2 := ⟨x - 2, by omega⟩
  rw [psiLog_eq]
  set F : ℕ → ℝ := fun N => GP N - TN N
  have hsplit : ∑ N ∈ range (k + 2), (∑ n ∈ range (N + 1), (Λ n : ℝ)) * aN N
      = ∑ N ∈ range (k + 2), (GP (N + 1) - GP N) * aN N
        - ∑ N ∈ range (k + 2), (F (N + 1) - F N) * aN N := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun N _ => ?_
    rw [← TN_succ]; simp only [F]; ring
  rw [hsplit]
  have hab := abel_ge F aN aN_zero (fun N _ => by simp only [F]; linarith [TN_le_GP hGRH N])
    (fun N hN => aN_anti hN) k
  have hF1 : F 1 = 71 / 20 := by simp [F, TN, GP]; norm_num
  have ha1 : aN 1 = Real.log 2 := by simp [aN]; norm_num
  have hFx : 0 ≤ F (k + 2) * aN (k + 1) :=
    mul_nonneg (by simp only [F]; linarith [TN_le_GP hGRH (k + 2)]) (aN_nonneg _)
  rw [hF1, ha1] at hab
  have hG : ∑ N ∈ range (k + 2), (GP (N + 1) - GP N) * aN N
      ≤ ((k + 2 : ℕ) : ℝ) - 1 + 7 / 2 * Real.log ((k + 2 : ℕ) : ℝ)
        + 3 / 20 * √((k + 2 : ℕ) : ℝ) := by
    rw [sum_range_succ' _ (k + 1), aN_zero, mul_zero, add_zero]
    have hterm : ∀ j ∈ range (k + 1), (GP (j + 1 + 1) - GP (j + 1)) * aN (j + 1)
        ≤ 1 + 7 / 2 * (Real.log ((j + 1 : ℕ) + 1 : ℝ) - Real.log ((j + 1 : ℕ) : ℝ))
          + 3 / 20 * (√(((j + 1 : ℕ) : ℝ) + 1) - √((j + 1 : ℕ) : ℝ))
          + 3 / 20 * (1 / √((j + 1 : ℕ) : ℝ) - 1 / √(((j + 1 : ℕ) : ℝ) + 1)) := by
      intro j _
      set N := j + 1 with hNdef
      have hN : 1 ≤ N := by omega
      have hN0 : (1 : ℝ) ≤ N := by exact_mod_cast hN
      set u := √(N : ℝ)
      set v := √((N : ℝ) + 1)
      have hu : 1 ≤ u := by rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hN0
      have hu2 : u ^ 2 = N := Real.sq_sqrt (by linarith)
      have hv2 : v ^ 2 = N + 1 := Real.sq_sqrt (by linarith)
      have hv0 : 0 < v := Real.sqrt_pos.2 (by linarith)
      have hvu : u ≤ v := Real.sqrt_le_sqrt (by linarith)
      have hcube := cube_diff_le hu (by rw [hv2, hu2]) hv0
      have hG : GP (N + 1) - GP N = ((N : ℝ) + 1 / 2) + 3 + (v ^ 3 - u ^ 3) / 20 := by
        unfold GP
        have e1 : (((N + 1 : ℕ) : ℝ)) * √((N + 1 : ℕ) : ℝ) = v ^ 3 := by
          push_cast; rw [pow_succ, hv2]
        have e2 : (N : ℝ) * √(N : ℝ) = u ^ 3 := by rw [pow_succ, hu2]
        rw [e1, e2]; push_cast; ring
      have ha2 := aN_le hN
      have ha0 := aN_nonneg N
      have hd0 : 0 ≤ v ^ 3 - u ^ 3 := by nlinarith [pow_le_pow_left₀ (by linarith) hvu 3]
      have hNa : (N : ℝ) * aN N ≤ 1 := by
        have := mul_le_mul_of_nonneg_left ha2 (show (0 : ℝ) ≤ N by positivity)
        rwa [show (N : ℝ) * (1 / N) = 1 by field_simp] at this
      have hcub : (v ^ 3 - u ^ 3) * aN N ≤ (v ^ 3 - u ^ 3) / u ^ 2 := by
        rw [hu2, div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left ha2 hd0
      have haeq : aN N = Real.log ((N : ℝ) + 1) - Real.log N := rfl
      rw [hG]
      have : (((N : ℝ) + 1 / 2) + 3 + (v ^ 3 - u ^ 3) / 20) * aN N
          = (N : ℝ) * aN N + 7 / 2 * aN N + (v ^ 3 - u ^ 3) * aN N / 20 := by ring
      rw [this, ← haeq]
      linarith
    refine le_trans (sum_le_sum hterm) ?_
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
    have t1 := Finset.sum_range_sub (fun j : ℕ => Real.log ((j + 1 : ℕ) : ℝ)) (k + 1)
    have t2 := Finset.sum_range_sub (fun j : ℕ => √((j + 1 : ℕ) : ℝ)) (k + 1)
    have t3 := Finset.sum_range_sub (fun j : ℕ => 1 / √((j + 1 : ℕ) : ℝ)) (k + 1)
    simp only [Nat.cast_add, Nat.cast_one, zero_add, Real.log_one, Real.sqrt_one,
      div_one] at t1 t2 t3 ⊢
    have e1 : ∑ j ∈ range (k + 1), (Real.log ((j : ℝ) + 1 + 1) - Real.log ((j : ℝ) + 1))
        = Real.log ((k : ℝ) + 1 + 1) := by rw [t1]; simp
    have e2 : ∑ j ∈ range (k + 1), (√((j : ℝ) + 1 + 1) - √((j : ℝ) + 1))
        = √((k : ℝ) + 1 + 1) - 1 := by rw [t2]
    have e3 : ∑ j ∈ range (k + 1), (1 / √((j : ℝ) + 1) - 1 / √((j : ℝ) + 1 + 1))
        = 1 - 1 / √((k : ℝ) + 1 + 1) := by
      have h := congrArg Neg.neg t3
      rw [← Finset.sum_neg_distrib] at h
      convert h using 1
      · exact sum_congr rfl fun j _ => by ring
      · ring
    rw [e1, e2, e3, sum_const, card_range, nsmul_eq_mul, mul_one]
    have : 0 ≤ 1 / √((k : ℝ) + 1 + 1) := by positivity
    push_cast
    simp only [show ((k : ℝ) + 1 + 1) = (k : ℝ) + 2 by ring] at *
    linarith
  have hl0 : 0 ≤ Real.log ((k + 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  push_cast at hG hab hFx hl0 ⊢
  nlinarith

end LLS.Thm14
