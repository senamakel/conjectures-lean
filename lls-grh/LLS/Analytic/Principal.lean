import LLS.Defs

/-! # The principal log-weighted sum under RH, by summation by parts from erdos-985

Write `T(N) = Σ_{n<N} Λ(n)(N − n)`, so `T(N+1) − T(N) = ψ(N)` and, by erdos-985's principal
bound, `T(N) ≥ G(N) = N²/2 − N√N/20 − 3N` for `N ≥ 1`. With `a_N = log(N+1) − log N`,
`Σ_{n≤x} Λ(n) log(x/n) = Σ_{N<x} ψ(N) a_N`. Summation by parts against the decreasing `a_N`
and `F = T − G ≥ 0` (`F(1) = 2.55`) reduces the claim to the elementary
`(G(N+1) − G(N)) a_N ≥ 1 − 3a_N − (3/20)(√(N+1) − √N) − (3/20)(1/√N − 1/√(N+1))`.
-/

namespace LLS

open ArithmeticFunction Erdos985 Finset

/-- `a_N = log(N+1) − log N`. -/
noncomputable def aN (N : ℕ) : ℝ := Real.log ((N : ℝ) + 1) - Real.log N

lemma aN_zero : aN 0 = 0 := by simp [aN]

lemma aN_nonneg (N : ℕ) : 0 ≤ aN N := by
  unfold aN
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have : Real.log N ≤ Real.log ((N : ℝ) + 1) :=
      Real.log_le_log (by exact_mod_cast hN) (by linarith)
    linarith

lemma aN_anti {N : ℕ} (hN : 1 ≤ N) : aN (N + 1) ≤ aN N := by
  unfold aN
  have h0 : (0 : ℝ) < N := by exact_mod_cast hN
  push_cast
  rw [← Real.log_div (by positivity) (by positivity), ← Real.log_div (by positivity) h0.ne']
  refine Real.log_le_log (by positivity) ?_
  rw [div_le_div_iff₀ (by positivity) h0]
  nlinarith

lemma aN_le {N : ℕ} (hN : 1 ≤ N) : aN N ≤ 1 / N := by
  unfold aN
  have h0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.log_div (by positivity) h0.ne']
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (N + 1) / N by positivity)
  have e : ((N : ℝ) + 1) / N - 1 = 1 / N := by field_simp; ring
  linarith

lemma aN_ge {N : ℕ} (hN : 1 ≤ N) : 2 / (2 * N + 1) ≤ aN N := by
  unfold aN
  have h0 : (0 : ℝ) < N := by exact_mod_cast hN
  set y : ℝ := 1 / (2 * N + 1)
  have hy0 : 0 ≤ y := by positivity
  have hy1 : y < 1 := by
    rw [div_lt_one (by positivity)]; linarith
  have h := Real.sum_range_le_log_div hy0 hy1 1
  simp only [range_one, sum_singleton, mul_zero, zero_add, pow_one, Nat.cast_zero, div_one] at h
  have e : (1 + y) / (1 - y) = ((N : ℝ) + 1) / N := by
    simp only [y]; field_simp; ring
  rw [e, Real.log_div (by positivity) h0.ne'] at h
  simp only [y] at h
  have : 2 / (2 * (N : ℝ) + 1) = 2 * (1 / (2 * N + 1)) := by ring
  linarith

/-- Termwise bound for the `√`-part: with `u = √N`, `v = √(N+1)`,
`(v³ − u³)/u² ≤ 3(v − u) + 3(1/u − 1/v)`. -/
lemma cube_diff_le {u v : ℝ} (hu : 1 ≤ u) (hv : v ^ 2 = u ^ 2 + 1) (hv0 : 0 < v) :
    (v ^ 3 - u ^ 3) / u ^ 2 ≤ 3 * (v - u) + 3 * (1 / u - 1 / v) := by
  have hu0 : 0 < u := by linarith
  have hvu : u < v := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  have key : 0 ≤ (3 * (v - u) * u ^ 2 * v + 3 * (v - u) * u) - (v ^ 3 - u ^ 3) * v := by
    -- (v³−u³)v − 3(v−u)u²v = (v−u)²(v+2u)v and (v−u)(v+u) = 1
    have h1 : (v - u) * (v + u) = 1 := by nlinarith
    have : (v ^ 3 - u ^ 3) * v - 3 * (v - u) * u ^ 2 * v = (v - u) ^ 2 * (v + 2 * u) * v := by ring
    have h2 : (v - u) ^ 2 * (v + 2 * u) * v ≤ 3 * (v - u) * u := by
      have hvu0 : 0 < v - u := by linarith
      -- (v−u)(v+2u)v ≤ 3u ⟸ (v+2u)v ≤ 3u(v+u)
      have h3 : (v + 2 * u) * v ≤ 3 * u * (v + u) := by nlinarith
      have : (v - u) ^ 2 * (v + 2 * u) * v = (v - u) * ((v - u) * ((v + 2 * u) * v)) := by ring
      rw [this]
      have h4 : (v - u) * ((v + 2 * u) * v) ≤ 3 * u := by
        calc (v - u) * ((v + 2 * u) * v) ≤ (v - u) * (3 * u * (v + u)) :=
              mul_le_mul_of_nonneg_left h3 hvu0.le
          _ = 3 * u * ((v - u) * (v + u)) := by ring
          _ = 3 * u := by rw [h1, mul_one]
      have := mul_le_mul_of_nonneg_left h4 hvu0.le
      linarith
    linarith
  have e : (3 * (v - u) + 3 * (1 / u - 1 / v)) * u ^ 2 - (v ^ 3 - u ^ 3)
      = ((3 * (v - u) * u ^ 2 * v + 3 * (v - u) * u) - (v ^ 3 - u ^ 3) * v) / v := by
    field_simp
  have := div_nonneg key hv0.le
  linarith

/-- `Σ_{n ≤ x} Λ(n) log(x/n) = Σ_{N<x} ψ(N) a_N`. -/
lemma psiLog_eq (x : ℕ) :
    ∑ n ∈ range (x + 1), (Λ n : ℝ) * Real.log ((x : ℝ) / n)
      = ∑ N ∈ range x, (∑ n ∈ range (N + 1), (Λ n : ℝ)) * aN N := by
  have h1 : ∀ y : ℕ, ∑ n ∈ range (y + 1), (Λ n : ℝ) * Real.log ((y : ℝ) / n)
      = ∑ n ∈ range (y + 1), (Λ n : ℝ) * (Real.log y - Real.log n) := by
    intro y
    refine sum_congr rfl fun n hn => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn0
    · simp
    · have hy : y ≠ 0 := by have := mem_range.1 hn; omega
      rw [Real.log_div (by exact_mod_cast hy) (by exact_mod_cast hn0.ne')]
  rw [h1]
  induction x with
  | zero => simp
  | succ x ih =>
    rw [sum_range_succ (fun N => (∑ n ∈ range (N + 1), (Λ n : ℝ)) * aN N), ← ih,
      sum_range_succ (fun n => (Λ n : ℝ) * (Real.log ((x + 1 : ℕ) : ℝ) - Real.log n)),
      sub_self, mul_zero, add_zero, sum_mul, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    simp only [aN]; push_cast; ring

/-- `T(N) = Σ_{n<N} Λ(n)(N − n)`. -/
noncomputable def TN (N : ℕ) : ℝ := ∑ n ∈ range N, (Λ n : ℝ) * ((N : ℝ) - n)

lemma TN_succ (N : ℕ) : TN (N + 1) - TN N = ∑ n ∈ range (N + 1), (Λ n : ℝ) := by
  unfold TN
  rw [sum_range_succ, sum_range_succ (fun n => (Λ n : ℝ))]
  have : ∑ n ∈ range N, (Λ n : ℝ) * (((N + 1 : ℕ) : ℝ) - n)
      = ∑ n ∈ range N, (Λ n : ℝ) * ((N : ℝ) - n) + ∑ n ∈ range N, (Λ n : ℝ) := by
    rw [← sum_add_distrib]; refine sum_congr rfl fun n _ => ?_; push_cast; ring
  rw [this]; push_cast; ring

/-- `G(N) = N²/2 − N√N/20 − 3N`. -/
noncomputable def GN (N : ℕ) : ℝ := (N : ℝ) ^ 2 / 2 - N * √(N : ℝ) / 20 - 3 * N

lemma GN_le_TN (hGRH : DirichletLNonvanishingRightOfHalf) {N : ℕ} (hN : 1 ≤ N) :
    GN N ≤ TN N := by
  have h := (abs_le.1 (Analytic.bach_principal_of_GRH hGRH N hN)).1
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have e : TN N = N * ∑ n ∈ range N, (Λ n : ℝ) * (1 - (n : ℝ) / N) := by
    unfold TN; rw [mul_sum]; refine sum_congr rfl fun n _ => ?_; field_simp
  rw [e]
  unfold GN
  have := mul_le_mul_of_nonneg_left (show (N : ℝ) / 2 - √(N : ℝ) / 20 - 3
    ≤ ∑ n ∈ range N, (Λ n : ℝ) * (1 - (n : ℝ) / N) by linarith) hN0.le
  nlinarith

/-- Summation by parts, lower bound. -/
lemma abel_ge (F a : ℕ → ℝ) (ha0 : a 0 = 0) (hF : ∀ N, 1 ≤ N → 0 ≤ F N)
    (ha : ∀ N, 1 ≤ N → a (N + 1) ≤ a N) (k : ℕ) :
    F (k + 2) * a (k + 1) - F 1 * a 1 ≤ ∑ N ∈ range (k + 2), (F (N + 1) - F N) * a N := by
  induction k with
  | zero =>
    simp [sum_range_succ, ha0]
    linarith [show (F 2 - F 1) * a 1 + F 1 * a 1 = F 2 * a 1 by ring]
  | succ k ih =>
    rw [sum_range_succ]
    have h1 := hF (k + 2) (by omega)
    have h2 := ha (k + 1) (by omega)
    have h3 : 0 ≤ F (k + 2) * (a (k + 1) - a (k + 2)) := mul_nonneg h1 (by linarith)
    have e : k + 1 + 1 = k + 2 := rfl
    simp only [e] at *
    nlinarith

/-- `Σ_{n ≤ x} Λ(n) log(x/n) ≥ x − (3/20)√x − 3 log x − 3` under GRH, from
`Erdos985.Analytic.bach_principal_of_GRH` by Abel summation. -/
theorem psiLog_ge (hGRH : DirichletLNonvanishingRightOfHalf) (x : ℕ) (hx : 1 ≤ x) :
    (x : ℝ) - 3 / 20 * √(x : ℝ) - 3 * Real.log x - 3
      ≤ ∑ n ∈ Finset.range (x + 1), (Λ n : ℝ) * Real.log ((x : ℝ) / n) := by
  have hlog2 := Real.log_two_lt_d9
  rcases Nat.lt_or_ge x 2 with hx2 | hx2
  · have : x = 1 := by omega
    subst this
    simp [sum_range_succ]
    norm_num
  obtain ⟨k, rfl⟩ : ∃ k, x = k + 2 := ⟨x - 2, by omega⟩
  rw [psiLog_eq]
  set F : ℕ → ℝ := fun N => TN N - GN N
  have hsplit : ∑ N ∈ range (k + 2), (∑ n ∈ range (N + 1), (Λ n : ℝ)) * aN N
      = ∑ N ∈ range (k + 2), (GN (N + 1) - GN N) * aN N
        + ∑ N ∈ range (k + 2), (F (N + 1) - F N) * aN N := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun N _ => ?_
    rw [← TN_succ]; simp only [F]; ring
  rw [hsplit]
  -- the Abel part
  have hab := abel_ge F aN aN_zero (fun N hN => by simp only [F]; linarith [GN_le_TN hGRH hN])
    (fun N hN => aN_anti hN) k
  have hF1 : F 1 = 51 / 20 := by simp [F, TN, GN]; norm_num
  have ha1 : aN 1 = Real.log 2 := by simp [aN]; norm_num
  have hFx : 0 ≤ F (k + 2) * aN (k + 1) :=
    mul_nonneg (by simp only [F]; linarith [GN_le_TN hGRH (N := k + 2) (by omega)]) (aN_nonneg _)
  rw [hF1, ha1] at hab
  -- the G part
  have hG : ((k + 2 : ℕ) : ℝ) - 1 - 3 * Real.log ((k + 2 : ℕ) : ℝ) - 3 / 20 * √((k + 2 : ℕ) : ℝ)
      ≤ ∑ N ∈ range (k + 2), (GN (N + 1) - GN N) * aN N := by
    rw [sum_range_succ' _ (k + 1), aN_zero, mul_zero, add_zero]
    have hterm : ∀ j ∈ range (k + 1),
        1 - 3 * (Real.log ((j + 1 : ℕ) + 1 : ℝ) - Real.log ((j + 1 : ℕ) : ℝ))
          - 3 / 20 * (√(((j + 1 : ℕ) : ℝ) + 1) - √((j + 1 : ℕ) : ℝ))
          - 3 / 20 * (1 / √((j + 1 : ℕ) : ℝ) - 1 / √(((j + 1 : ℕ) : ℝ) + 1))
        ≤ (GN (j + 1 + 1) - GN (j + 1)) * aN (j + 1) := by
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
      have hG : GN (N + 1) - GN N = ((N : ℝ) + 1 / 2) - 3 - (v ^ 3 - u ^ 3) / 20 := by
        unfold GN
        have e1 : (((N + 1 : ℕ) : ℝ)) * √((N + 1 : ℕ) : ℝ) = v ^ 3 := by
          push_cast; rw [pow_succ, hv2]
        have e2 : (N : ℝ) * √(N : ℝ) = u ^ 3 := by rw [pow_succ, hu2]
        rw [e1, e2]; push_cast; ring
      have ha1 := aN_ge hN
      have ha2 := aN_le hN
      have ha0 := aN_nonneg N
      have hd0 : 0 ≤ v ^ 3 - u ^ 3 := by nlinarith [pow_le_pow_left₀ (by linarith) hvu 3]
      have hhalf : 1 ≤ ((N : ℝ) + 1 / 2) * aN N := by
        have := mul_le_mul_of_nonneg_left ha1 (show (0 : ℝ) ≤ N + 1 / 2 by positivity)
        rw [show ((N : ℝ) + 1 / 2) * (2 / (2 * N + 1)) = 1 by field_simp] at this
        exact this
      have hcub : (v ^ 3 - u ^ 3) * aN N ≤ (v ^ 3 - u ^ 3) / u ^ 2 := by
        rw [hu2, div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left ha2 hd0
      have haeq : aN N = Real.log ((N : ℝ) + 1) - Real.log N := rfl
      rw [hG]
      have : (((N : ℝ) + 1 / 2) - 3 - (v ^ 3 - u ^ 3) / 20) * aN N
          = ((N : ℝ) + 1 / 2) * aN N - 3 * aN N - (v ^ 3 - u ^ 3) * aN N / 20 := by ring
      rw [this, ← haeq]
      linarith
    refine le_trans ?_ (sum_le_sum hterm)
    rw [sum_sub_distrib, sum_sub_distrib, sum_sub_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
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
  push_cast at hG hab hFx ⊢
  nlinarith

end LLS
