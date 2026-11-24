import Mathlib

/-!
# The numerical inequality behind the large-`r` case

For `n ≥ 3` put `u = log n`, `K = ⌈420 u²⌉` and `j = ⌊10 u / log K⌋`. Then

* `K ^ j ≤ n ^ 10`, since `j log K ≤ 10 u`;
* `n < (π K).choose j`.

For the second: Chebyshev's bound `π(K) log K ≥ K log 2` (Mathlib, `K ≥ 7`) and `j log K ≤ 10u`
give `π(K) ≥ 29 u j ≥ (21 u + 1) j`, so `(π K).choose j ≥ (π K + 1 - j)^j / j! ≥ (21 u)^j`.
Since `log K ≤ log (441 u²) = 2 log (21 u)` and `10u < (j + 1) log K`,
`j log (21 u) > 5u - log (21 u) ≥ u` (using `log (21 u) ≤ log 21 + u - 1 < 4u`).
-/

namespace Erdos770

open Real

lemma log_twentyone_lt_four : Real.log 21 < 4 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h := Real.exp_one_gt_d9
  have : (4 : ℝ) = 1 + 1 + 1 + 1 := by norm_num
  rw [this, Real.exp_add, Real.exp_add, Real.exp_add]
  have h0 : (0 : ℝ) < 2.7182818283 := by norm_num
  have h1 : (2.7182818283 : ℝ) ^ 4 ≤ Real.exp 1 ^ 4 := by gcongr
  nlinarith [h1]

theorem numeric {n : ℕ} (hn : 3 ≤ n) :
    ∃ j : ℕ, ⌈420 * Real.log n ^ 2⌉₊ ^ j ≤ n ^ 10 ∧
      n < (Nat.primeCounting ⌈420 * Real.log n ^ 2⌉₊).choose j := by
  set u := Real.log n with hu_def
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by linarith
  have hu1 : 1 ≤ u := by
    rw [hu_def, Real.le_log_iff_exp_le hnpos]
    have := Real.exp_one_lt_d9
    linarith
  set K := ⌈420 * u ^ 2⌉₊ with hK_def
  have hK1 : 420 * u ^ 2 ≤ K := Nat.le_ceil _
  have hK2 : (K : ℝ) < 420 * u ^ 2 + 1 := Nat.ceil_lt_add_one (by positivity)
  have hu2 : 1 ≤ u ^ 2 := by nlinarith
  have hK3 : (K : ℝ) ≤ (21 * u) ^ 2 := by nlinarith
  have hK7 : 7 ≤ K := by
    have : (7 : ℝ) ≤ K := by nlinarith
    exact_mod_cast this
  have hKpos : (0 : ℝ) < K := by positivity
  set L := Real.log K with hL_def
  have hL0 : 0 < L := Real.log_pos (by exact_mod_cast (by omega : 1 < K))
  set ℓ := Real.log (21 * u) with hℓ_def
  have hℓ0 : 0 < ℓ := Real.log_pos (by linarith)
  have hLℓ : L ≤ 2 * ℓ := by
    have := Real.log_le_log hKpos hK3
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hℓu : ℓ < 4 * u := by
    rw [hℓ_def, Real.log_mul (by norm_num) (by linarith)]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < u)
    have := log_twentyone_lt_four
    linarith
  -- Chebyshev
  set s := Nat.primeCounting K with hs_def
  have hs : (K : ℝ) * Real.log 2 ≤ s * L :=
    (Chebyshev.psi_ge_of_seven_le hK7).trans (Chebyshev.psi_le_primeCounting_mul_log K)
  have hlog2 := Real.log_two_gt_d9
  set j := ⌊10 * u / L⌋₊ with hj_def
  have hj1 : (j : ℝ) * L ≤ 10 * u := by
    have := Nat.floor_le (by positivity : 0 ≤ 10 * u / L)
    rwa [← hj_def, le_div_iff₀ hL0] at this
  have hj2 : 10 * u < (j + 1) * L := by
    have := Nat.lt_floor_add_one (10 * u / L)
    rwa [← hj_def, div_lt_iff₀ hL0] at this
  refine ⟨j, ?_, ?_⟩
  · -- K ^ j ≤ n ^ 10
    have : ((K : ℝ)) ^ j ≤ (n : ℝ) ^ 10 := by
      rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_pow, Real.log_pow]
      push_cast
      linarith
    exact_mod_cast this
  · -- n < choose s j
    have hjℓ : u < j * ℓ := by nlinarith
    have hj0 : 0 < j := by
      rcases Nat.eq_zero_or_pos j with h | h
      · rw [h] at hjℓ; simp at hjℓ; linarith
      · exact h
    have hjpos : (0 : ℝ) < j := by exact_mod_cast hj0
    -- s ≥ (21 u + 1) j
    have hsj : (21 * u + 1) * j ≤ s := by
      have h1 : (j : ℝ) * L * (29 * u) ≤ s * L := by nlinarith
      have h2 : (j : ℝ) * (29 * u) ≤ s := le_of_mul_le_mul_right (by linarith) hL0
      nlinarith
    have hjs : j ≤ s + 1 := by
      have : (j : ℝ) ≤ s := by nlinarith
      exact_mod_cast (by linarith : (j : ℝ) ≤ s + 1)
    have hcast : ((s + 1 - j : ℕ) : ℝ) = s + 1 - j := by
      rw [Nat.cast_sub hjs]; push_cast; ring
    have hbase : 21 * u * j ≤ ((s + 1 - j : ℕ) : ℝ) := by rw [hcast]; nlinarith
    have hfac : ((j.factorial : ℕ) : ℝ) ≤ (j : ℝ) ^ j := by exact_mod_cast Nat.factorial_le_pow j
    have hfacpos : (0 : ℝ) < (j.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos j
    have hchoose : (21 * u) ^ j ≤ (s.choose j : ℝ) := by
      refine le_trans ?_ (Nat.pow_le_choose j s)
      rw [le_div_iff₀ hfacpos]
      calc (21 * u) ^ j * (j.factorial : ℕ) ≤ (21 * u) ^ j * (j : ℝ) ^ j := by gcongr
        _ = (21 * u * j) ^ j := by ring
        _ ≤ ((s + 1 - j : ℕ) : ℝ) ^ j := by gcongr
    have hpow : (n : ℝ) < (21 * u) ^ j := by
      rw [← Real.log_lt_log_iff hnpos (by positivity), Real.log_pow]
      linarith
    exact_mod_cast hpow.trans_le hchoose

end Erdos770
