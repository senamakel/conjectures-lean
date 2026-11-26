import Erdos233.Gaps

/-!
# Step 9. Dyadic summation over gap sizes

With `h₀ = 16 log²(5x)/log 2` and `h_i = 2^i h₀`, every gap satisfies
`d² ≤ 16 h₀ d + 32 Σ_{i ≤ I} [16 h_i ≤ d] h_i d` (`sq_le_dyadic`). Summing over the block
`x ≤ p_n < 2x` and applying `gap_sum` at each level (`Σ_{d ≥ 16h_i} d ≤ C x log² x / h_i`,
the level is empty once `h_i > x/8`) gives `Σ_{x ≤ p_n < 2x} d_n² ≪ x log³ x`.
-/

namespace Erdos233

open Real

lemma sq_le_dyadic {d h0 : ℝ} (hh0 : 0 < h0) (hd0 : 0 ≤ d) (I : ℕ)
    (hI : d < 16 * h0 * 2 ^ (I + 1)) :
    d ^ 2 ≤ 16 * h0 * d + 32 * ∑ i ∈ Finset.range (I + 1),
      (if 16 * (2 ^ i * h0) ≤ d then 2 ^ i * h0 * d else 0) := by
  have hS0 : 0 ≤ ∑ i ∈ Finset.range (I + 1),
      (if 16 * (2 ^ i * h0) ≤ d then 2 ^ i * h0 * d else 0) :=
    Finset.sum_nonneg fun i _ => by split_ifs <;> positivity
  by_cases hsmall : d < 16 * h0
  · have : d ^ 2 ≤ 16 * h0 * d := by nlinarith
    linarith
  push Not at hsmall
  have h16 : 0 < 16 * h0 := by positivity
  set q := d / (16 * h0) with hq
  have hq1 : 1 ≤ q := by rw [hq, le_div_iff₀ h16]; linarith
  set m := ⌊q⌋₊ with hm
  have hm1 : 1 ≤ m := by rw [hm]; exact Nat.le_floor (by exact_mod_cast hq1)
  set j := Nat.log 2 m with hj
  have hjm : 2 ^ j ≤ m := Nat.pow_log_le_self 2 (by omega)
  have hmj : m < 2 ^ (j + 1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hmq : (m : ℝ) ≤ q := Nat.floor_le (by linarith)
  have hqm : q < m + 1 := Nat.lt_floor_add_one q
  have h2j : (2 : ℝ) ^ j ≤ q := by
    have : ((2 ^ j : ℕ) : ℝ) ≤ m := by exact_mod_cast hjm
    push_cast at this; linarith
  have hq2 : q < (2 : ℝ) ^ (j + 1) := by
    have : ((m + 1 : ℕ) : ℝ) ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by exact_mod_cast hmj
    push_cast at this; linarith
  have hjI : j < I + 1 := by
    have hqI : q < (2 : ℝ) ^ (I + 1) := by
      rw [hq, div_lt_iff₀ h16]; linarith
    have : (2 : ℝ) ^ j < 2 ^ (I + 1) := lt_of_le_of_lt h2j hqI
    exact (pow_lt_pow_iff_right₀ (by norm_num)).1 this
  have hlow : 16 * (2 ^ j * h0) ≤ d := by
    have := mul_le_mul_of_nonneg_left h2j h16.le
    rw [hq, mul_div_cancel₀ _ h16.ne'] at this; linarith
  have hup : d < 32 * (2 ^ j * h0) := by
    have := mul_lt_mul_of_pos_left hq2 h16
    rw [hq, mul_div_cancel₀ _ h16.ne', pow_succ] at this; linarith
  have hterm : 2 ^ j * h0 * d ≤ ∑ i ∈ Finset.range (I + 1),
      (if 16 * (2 ^ i * h0) ≤ d then 2 ^ i * h0 * d else 0) := by
    have := Finset.single_le_sum (f := fun i =>
      (if 16 * (2 ^ i * h0) ≤ d then 2 ^ i * h0 * d else 0))
      (fun i _ => by split_ifs <;> positivity) (Finset.mem_range.2 hjI)
    simp only [hlow, ↓reduceIte] at this
    exact this
  have : d ^ 2 ≤ 32 * (2 ^ j * h0 * d) := by nlinarith
  nlinarith

theorem block_sq (hRH : RiemannHypothesis) : ∃ C X₀ : ℝ, 0 < C ∧ ∀ x : ℕ, X₀ ≤ x →
    ∑ n ∈ block x, (primeGap n : ℝ) ^ 2 ≤ C * x * Real.log x ^ 3 := by
  obtain ⟨Cg, Xg, hCg, hgap⟩ := gap_sum hRH
  refine ⟨6000 + 96 * Cg, max Xg 5, by positivity, fun x hx => ?_⟩
  have hX5 : (5 : ℝ) ≤ x := le_of_max_le_right hx
  have hX0 : (0 : ℝ) < x := by linarith
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : (0.69 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hlX : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hX0]; have := Real.exp_one_lt_d9; linarith
  set h0 := 16 * (Real.log (5 * x) ^ 2 / Real.log 2) with hh0
  have hl5 : Real.log (5 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) hX0.ne']
    have : Real.log 5 ≤ Real.log x := Real.log_le_log (by norm_num) hX5
    linarith
  have hl5' : 1 ≤ Real.log (5 * x) := by
    rw [Real.le_log_iff_exp_le (by positivity)]; have := Real.exp_one_lt_d9; linarith
  have hh0pos : 16 ≤ h0 := by
    rw [hh0]
    have : 1 ≤ Real.log (5 * x) ^ 2 / Real.log 2 := by
      have : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
      rw [le_div_iff₀ hl2]; nlinarith
    linarith
  have hh0le : h0 ≤ 93 * Real.log x ^ 2 := by
    rw [hh0, mul_div_assoc', div_le_iff₀ hl2]
    have : Real.log (5 * x) ^ 2 ≤ 4 * Real.log x ^ 2 := by nlinarith
    nlinarith
  set I := Nat.log 2 x with hI
  have hxI : x < 2 ^ (I + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  -- pointwise
  have hpt : ∀ n ∈ block x, (primeGap n : ℝ) ^ 2 ≤ 16 * h0 * primeGap n + 32 *
      ∑ i ∈ Finset.range (I + 1),
        (if 16 * (2 ^ i * h0) ≤ (primeGap n : ℝ) then 2 ^ i * h0 * primeGap n else 0) := by
    intro n hn
    refine sq_le_dyadic (by linarith) (Nat.cast_nonneg _) I ?_
    have h1 := (mem_block hn).2
    have h2 := nth_succ_le_two_mul n
    have hd : (primeGap n : ℝ) < 2 * x := by
      rw [primeGap_cast]
      have : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ 2 * Nat.nth Nat.Prime n := by exact_mod_cast h2
      have : (Nat.nth Nat.Prime n : ℝ) < 2 * x := by exact_mod_cast h1
      linarith
    have : (x : ℝ) < 2 ^ (I + 1) := by exact_mod_cast hxI
    nlinarith
  have hsum := Finset.sum_le_sum hpt
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm] at hsum
  -- level bounds
  have hlevel : ∀ i ∈ Finset.range (I + 1), ∑ n ∈ block x,
      (if 16 * (2 ^ i * h0) ≤ (primeGap n : ℝ) then 2 ^ i * h0 * primeGap n else 0)
      ≤ Cg * x * Real.log x ^ 2 := by
    intro i _
    have hhi : 0 < 2 ^ i * h0 := by positivity
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    by_cases hbig : 2 ^ i * h0 ≤ x / 8
    · have := hgap x (le_of_max_le_left hx) (2 ^ i * h0) (by
        have : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
        rw [← hh0]; nlinarith) hbig
      rw [le_div_iff₀ hhi] at this
      linarith
    · push Not at hbig
      have hempty : (block x).filter (fun n => 16 * (2 ^ i * h0) ≤ (primeGap n : ℝ)) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro n hn
        have h1 := (mem_block hn).2
        have h2 := nth_succ_le_two_mul n
        rw [primeGap_cast, not_le]
        have : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ 2 * Nat.nth Nat.Prime n := by exact_mod_cast h2
        have : (Nat.nth Nat.Prime n : ℝ) < 2 * x := by exact_mod_cast h1
        linarith
      rw [hempty, Finset.sum_empty, mul_zero]
      positivity
  have hlev := Finset.sum_le_sum hlevel
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hlev
  have hIl : ((I + 1 : ℕ) : ℝ) ≤ 3 * Real.log x := by
    have hI' : (2 : ℝ) ^ I ≤ x := by exact_mod_cast Nat.pow_log_le_self 2 (by
      have : (5 : ℝ) ≤ x := hX5; exact_mod_cast (show x ≠ 0 by rintro rfl; norm_num at this))
    have : (I : ℝ) * Real.log 2 ≤ Real.log x := by
      rw [← Real.log_pow]; exact Real.log_le_log (by positivity) hI'
    push_cast
    have : (I : ℝ) ≤ Real.log x / 0.69 := by
      rw [le_div_iff₀ (by norm_num)]; nlinarith [(Nat.cast_nonneg I : (0 : ℝ) ≤ I)]
    have : Real.log x / 0.69 ≤ 2 * Real.log x := by
      rw [div_le_iff₀ (by norm_num)]; nlinarith
    linarith
  have hgsum := sum_block_primeGap_le x
  have hgsum0 : 0 ≤ ∑ n ∈ block x, (primeGap n : ℝ) :=
    Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  have hA : 16 * h0 * ∑ n ∈ block x, (primeGap n : ℝ) ≤ 6000 * x * Real.log x ^ 3 := by
    have : 16 * h0 * ∑ n ∈ block x, (primeGap n : ℝ) ≤ 16 * (93 * Real.log x ^ 2) * (4 * x) := by
      gcongr
    have : Real.log x ^ 2 ≤ Real.log x ^ 3 := by
      have := pow_le_pow_right₀ hlX (show 2 ≤ 3 by norm_num); exact this
    nlinarith
  have hB : 32 * (((I + 1 : ℕ) : ℝ) * (Cg * x * Real.log x ^ 2))
      ≤ 96 * Cg * x * Real.log x ^ 3 := by
    have h1 : 0 ≤ Cg * x * Real.log x ^ 2 := by positivity
    have := mul_le_mul_of_nonneg_right hIl h1
    nlinarith
  have hB' : 32 * ∑ i ∈ Finset.range (I + 1), ∑ n ∈ block x,
      (if 16 * (2 ^ i * h0) ≤ (primeGap n : ℝ) then 2 ^ i * h0 * primeGap n else 0)
      ≤ 32 * (((I + 1 : ℕ) : ℝ) * (Cg * x * Real.log x ^ 2)) := by
    have := hlev; push_cast at this ⊢; linarith
  nlinarith

end Erdos233
