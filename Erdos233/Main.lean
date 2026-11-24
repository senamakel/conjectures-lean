import Erdos233.Dyadic

/-!
# Step 10. From blocks `x ≤ p_n < 2x` to `Σ_{n<N} d_n² ≪ N log⁴ N`

The indices `n < N` are covered by `n < idx x₀` (finitely many, a constant) and the blocks
`2^j x₀ ≤ p_n < 2^{j+1} x₀`, `j < J = log₂ p_N + 1`; `block_sq` bounds block `j` by
`C 2^j x₀ log³(2^j x₀)`, so the total is `≪ p_N log³ p_N`. Chebyshev's bound
(Mathlib's `Chebyshev.pi_ge_of_four_le`) gives `p_N ≤ 18 N log N`.
-/

namespace Erdos233

open Real Filter Asymptotics

lemma sum_Ico_blocks (f : ℕ → ℝ) (x₀ J : ℕ) :
    ∑ n ∈ Finset.Ico (idx x₀) (idx (2 ^ J * x₀)), f n
      = ∑ j ∈ Finset.range J, ∑ n ∈ block (2 ^ j * x₀), f n := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih, block, show 2 * (2 ^ J * x₀) = 2 ^ (J + 1) * x₀ by ring]
    refine (Finset.sum_Ico_consecutive _ ?_ ?_).symm
    · exact Nat.monotone_primeCounting' (by
        have : 1 ≤ 2 ^ J := Nat.one_le_two_pow; nlinarith)
    · exact Nat.monotone_primeCounting' (by
        rw [pow_succ, mul_comm (2 ^ J) 2, mul_assoc]
        exact Nat.le_mul_of_pos_left _ (by norm_num))

/-- `p_N ≤ 18 N log N` for `N ≥ 3`. -/
lemma nth_prime_le (N : ℕ) (hN : 3 ≤ N) :
    (Nat.nth Nat.Prime N : ℝ) ≤ 18 * N * Real.log N := by
  set X := Nat.nth Nat.Prime N with hX
  have hX4 : 4 ≤ X := by have := Nat.add_two_le_nth_prime N; omega
  have hpi : Nat.primeCounting X = N + 1 :=
    Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime N
  have hcheb := Chebyshev.pi_ge_of_four_le hX4
  rw [hpi] at hcheb
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hl2 : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlX0 : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have h1 : (X : ℝ) * Real.log 2 ≤ (N + 1) * Real.log X := by
    rw [div_le_iff₀ hlX0] at hcheb; push_cast at hcheb; linarith
  -- `log X ≤ 2√X`
  have hsX : Real.log X ≤ 2 * Real.sqrt X := by
    have hs0 : 0 < Real.sqrt X := Real.sqrt_pos.2 hX0
    have := Real.log_le_sub_one_of_pos hs0
    rw [Real.log_sqrt hX0.le] at this
    linarith
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hsq : Real.sqrt X ≤ 3 * (N + 1) := by
    have hs0 : 0 < Real.sqrt X := Real.sqrt_pos.2 hX0
    have hXs : (X : ℝ) = Real.sqrt X * Real.sqrt X := (Real.mul_self_sqrt hX0.le).symm
    have : Real.sqrt X * Real.sqrt X * 0.69 ≤ (N + 1) * (2 * Real.sqrt X) := by
      rw [← hXs]
      calc (X : ℝ) * 0.69 ≤ X * Real.log 2 := by gcongr
        _ ≤ (N + 1) * Real.log X := h1
        _ ≤ (N + 1) * (2 * Real.sqrt X) := by gcongr
    nlinarith
  have hXN : (X : ℝ) ≤ 9 * (N + 1) ^ 2 := by
    have := Real.mul_self_sqrt hX0.le
    nlinarith [Real.sqrt_nonneg (X : ℝ)]
  have hlN : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]; have := Real.exp_one_lt_d9; linarith
  have hlogX : Real.log X ≤ 6 * Real.log N := by
    have hNN : (9 : ℝ) * (N + 1) ^ 2 ≤ (N : ℝ) ^ 6 := by
      have : (N : ℝ) + 1 ≤ N ^ 2 := by nlinarith
      have h2 : (N + 1 : ℝ) ^ 2 ≤ (N ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
      have h3 : (9 : ℝ) ≤ N ^ 2 := by nlinarith
      calc (9 : ℝ) * (N + 1) ^ 2 ≤ N ^ 2 * (N ^ 2) ^ 2 := by
            exact mul_le_mul h3 h2 (by positivity) (by positivity)
        _ = (N : ℝ) ^ 6 := by ring
    calc Real.log X ≤ Real.log ((N : ℝ) ^ 6) := Real.log_le_log hX0 (hXN.trans hNN)
      _ = 6 * Real.log N := by rw [Real.log_pow]; push_cast; ring
  have : (X : ℝ) * 0.69 ≤ (N + 1) * (6 * Real.log N) := by
    calc (X : ℝ) * 0.69 ≤ X * Real.log 2 := by gcongr
      _ ≤ (N + 1) * Real.log X := h1
      _ ≤ (N + 1) * (6 * Real.log N) := by gcongr
  nlinarith

theorem erdos_233_upper_bound_of_RH (hRH : RiemannHypothesis) : Erdos233UpperBoundStatement := by
  obtain ⟨Cb, Xb, hCb, hblock⟩ := block_sq hRH
  set x₀ : ℕ := ⌈max Xb 5⌉₊ with hx₀
  have hx₀X : max Xb 5 ≤ (x₀ : ℝ) := Nat.le_ceil _
  have hx₀5 : (5 : ℝ) ≤ x₀ := le_trans (le_max_right _ _) hx₀X
  have hx₀pos : 0 < x₀ := by exact_mod_cast (show (0 : ℝ) < x₀ by linarith)
  set K₀ := ∑ n ∈ Finset.range (idx x₀), (primeGap n : ℝ) ^ 2 with hK₀
  set a := Real.log (2 * x₀) with ha
  have ha0 : 0 ≤ a := Real.log_nonneg (by linarith)
  set C₁ := 36 * Cb * x₀ * (a + 6) ^ 3 with hC₁
  have hC₁0 : 0 ≤ C₁ := by positivity
  have hK0 : 0 ≤ K₀ := Finset.sum_nonneg fun _ _ => by positivity
  refine IsBigO.of_bound (C₁ + 1) ?_
  rw [eventually_atTop]
  refine ⟨max 3 ⌈K₀⌉₊, fun N hN => ?_⟩
  have hN3 : 3 ≤ N := le_of_max_le_left hN
  have hNK : K₀ ≤ N := (Nat.le_ceil K₀).trans (by exact_mod_cast le_of_max_le_right hN)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlN : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le hN0]
    have := Real.exp_one_lt_d9
    have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    linarith
  set X := Nat.nth Nat.Prime N with hX
  set J := Nat.log 2 X + 1 with hJ
  have hXJ : X < 2 ^ J := Nat.lt_pow_succ_log_self (by norm_num) X
  have hJX : 2 ^ J ≤ 2 * X := by
    rw [hJ, pow_succ]
    have := Nat.pow_log_le_self 2 (show X ≠ 0 from (Nat.prime_nth_prime N).ne_zero)
    omega
  have hNidx : N ≤ idx (2 ^ J * x₀) := by
    have : X < 2 ^ J * x₀ := by nlinarith
    exact ((Nat.lt_nth_iff_count_lt Nat.infinite_setOfPred_prime).2 this).le
  have hidx : idx x₀ ≤ idx (2 ^ J * x₀) :=
    Nat.monotone_primeCounting' (by have : 1 ≤ 2 ^ J := Nat.one_le_two_pow; nlinarith)
  -- the sum up to `N`
  have hsplit : ∑ n ∈ Finset.range N, (primeGap n : ℝ) ^ 2
      ≤ K₀ + ∑ j ∈ Finset.range J, ∑ n ∈ block (2 ^ j * x₀), (primeGap n : ℝ) ^ 2 := by
    rw [← sum_Ico_blocks, hK₀, Finset.sum_range_add_sum_Ico _ hidx]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hNidx)
      fun _ _ _ => by positivity
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (Nat.prime_nth_prime N).pos
  have hlog0 : 0 ≤ Real.log (2 * x₀ * X) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ X := by exact_mod_cast (Nat.prime_nth_prime N).one_lt.le
    nlinarith)
  have hblocks : ∑ j ∈ Finset.range J, ∑ n ∈ block (2 ^ j * x₀), (primeGap n : ℝ) ^ 2
      ≤ Cb * x₀ * Real.log (2 * x₀ * X) ^ 3 * 2 ^ J := by
    have hL : ∀ j ∈ Finset.range J, Real.log ((2 ^ j * x₀ : ℕ) : ℝ) ≤ Real.log (2 * x₀ * X) := by
      intro j hj
      refine Real.log_le_log (by positivity) ?_
      have : 2 ^ j * x₀ ≤ 2 * x₀ * X := by
        have : 2 ^ j ≤ 2 ^ J := Nat.pow_le_pow_right (by norm_num) (Finset.mem_range.1 hj).le
        nlinarith
      exact_mod_cast this
    calc ∑ j ∈ Finset.range J, ∑ n ∈ block (2 ^ j * x₀), (primeGap n : ℝ) ^ 2
        ≤ ∑ j ∈ Finset.range J, Cb * ((2 ^ j * x₀ : ℕ) : ℝ) * Real.log ((2 ^ j * x₀ : ℕ) : ℝ) ^ 3 :=
          Finset.sum_le_sum fun j _ => hblock _ (by
            refine le_trans (le_trans (le_max_left _ _) hx₀X) ?_
            have : 1 ≤ 2 ^ j := Nat.one_le_two_pow
            exact_mod_cast (show x₀ ≤ 2 ^ j * x₀ by nlinarith))
      _ ≤ ∑ j ∈ Finset.range J, Cb * x₀ * Real.log (2 * x₀ * X) ^ 3 * 2 ^ j := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hl0 : 0 ≤ Real.log ((2 ^ j * x₀ : ℕ) : ℝ) := Real.log_nonneg (by
            have : 1 ≤ 2 ^ j * x₀ := Nat.one_le_iff_ne_zero.2 (by positivity)
            exact_mod_cast this)
          have h3 := pow_le_pow_left₀ hl0 (hL j hj) 3
          push_cast at h3 ⊢
          have h := mul_le_mul_of_nonneg_left h3 (show 0 ≤ Cb * ((2 : ℝ) ^ j * x₀) by positivity)
          linarith
      _ = Cb * x₀ * Real.log (2 * x₀ * X) ^ 3 * ∑ j ∈ Finset.range J, (2 : ℝ) ^ j := by
          rw [Finset.mul_sum]
      _ ≤ Cb * x₀ * Real.log (2 * x₀ * X) ^ 3 * 2 ^ J := by
          have hgeom : ∑ j ∈ Finset.range J, (2 : ℝ) ^ j ≤ 2 ^ J := by
            have := geom_sum_mul_of_one_le (show (1 : ℝ) ≤ 2 by norm_num) J
            norm_num at this; linarith [this, (pow_pos (show (0 : ℝ) < 2 by norm_num) J)]
          exact mul_le_mul_of_nonneg_left hgeom (by positivity)
  -- sizes
  have hpN := nth_prime_le N hN3
  have hlog : Real.log (2 * x₀ * X) ≤ (a + 6) * Real.log N := by
    rw [Real.log_mul (by positivity) hX0.ne', ← ha]
    have hlX : Real.log X ≤ 6 * Real.log N := by
      have hXN : (X : ℝ) ≤ (N : ℝ) ^ 6 := by
        have h1 : 18 * (N : ℝ) * Real.log N ≤ 18 * N * N := by
          have := Real.log_le_sub_one_of_pos hN0
          gcongr; linarith
        have : (3 : ℝ) ≤ N := by exact_mod_cast hN3
        have h2 : 18 * (N : ℝ) * N ≤ N ^ 6 := by
          have : (27 : ℝ) ≤ N ^ 3 := by nlinarith
          nlinarith
        linarith
      calc Real.log X ≤ Real.log ((N : ℝ) ^ 6) := Real.log_le_log hX0 hXN
        _ = 6 * Real.log N := by rw [Real.log_pow]; push_cast; ring
    nlinarith
  have h2J : ((2 : ℝ) ^ J) ≤ 2 * X := by exact_mod_cast hJX
  have hmain : Cb * x₀ * Real.log (2 * x₀ * X) ^ 3 * 2 ^ J ≤ C₁ * (N * Real.log N ^ 4) := by
    have e1 := pow_le_pow_left₀ hlog0 hlog 3
    have : Cb * x₀ * Real.log (2 * x₀ * X) ^ 3 * 2 ^ J
        ≤ Cb * x₀ * ((a + 6) * Real.log N) ^ 3 * (2 * (18 * N * Real.log N)) := by
      have h3 : (2 : ℝ) ^ J ≤ 2 * (18 * N * Real.log N) := by linarith
      gcongr
    rw [hC₁]
    calc _ ≤ Cb * x₀ * ((a + 6) * Real.log N) ^ 3 * (2 * (18 * N * Real.log N)) := this
      _ = 36 * Cb * x₀ * (a + 6) ^ 3 * (N * Real.log N ^ 4) := by ring
  have hg0 : 0 ≤ (N : ℝ) * Real.log N ^ 4 := by positivity
  have hK : K₀ ≤ 1 * ((N : ℝ) * Real.log N ^ 4) := by
    have : (1 : ℝ) ≤ Real.log N ^ 4 := one_le_pow₀ hlN
    nlinarith
  have hS0 : 0 ≤ ∑ n ∈ Finset.range N, (primeGap n : ℝ) ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hg0]
  rw [abs_of_nonneg hS0]
  nlinarith

end Erdos233
