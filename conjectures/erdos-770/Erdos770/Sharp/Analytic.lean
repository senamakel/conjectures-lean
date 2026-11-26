import Mathlib

/-!
# The counting inequality for `n ≥ 2^709`

`analytic`: for `n ≥ 2^709`, with `K = ⌈5 log² n⌉`, `x = √K`, `L = log K` and
`j = ⌊(x - 13/4)/L⌋`, we have `j L ≤ x - 13/4` and `n < C(π(K), j)`.

Proof. `u = log n ≥ 491.4`, so `x ≥ 1098` and `L ≥ 14` (`e^14 < 1.21·10⁶ ≤ K`). Chebyshev
(`π(K) L ≥ K log 2`) and `j L ≤ x` give `j (2x/3 + 1) ≤ π(K)`, so
`C(π(K), j) ≥ (π(K) + 1 - j)^j / j! ≥ (2x/3)^j`. Next `log(2x/3) ≥ L/2 - 1/2`,
`j L > x - 13/4 - L` and `L ≥ 14` give `j (L/2 - 1/2) > (13/28)(x - 13/4 - L)`, which is
`≥ 0.4473 x ≥ u` because `L ≤ x/50 + 7.72` (from `log(x/100) ≤ x/100 - 1`, `log 100 < 4.86`).
-/

namespace Erdos770.Sharp

open Real

lemma exp_14_lt : Real.exp 14 < 1205000 := by
  have h := Real.exp_one_lt_d9
  have h0 : 0 ≤ Real.exp 1 := (Real.exp_pos 1).le
  have : Real.exp 14 = Real.exp 1 ^ 14 := by rw [← Real.exp_nat_mul]; norm_num
  rw [this]
  calc Real.exp 1 ^ 14 < 2.7182818286 ^ 14 := by gcongr
    _ < 1205000 := by norm_num

lemma log_100_lt' : Real.log 100 < 4.86 := by
  have h : Real.log 100 < Real.log ((2 : ℝ) ^ 7) := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow] at h
  norm_num at h
  linarith [Real.log_two_lt_d9]

set_option maxHeartbeats 1000000 in
theorem analytic {n : ℕ} (hn : 2 ^ 709 ≤ n) :
    ∃ j : ℕ, (j : ℝ) * Real.log (⌈5 * Real.log n ^ 2⌉₊ : ℕ) ≤
        Real.sqrt (⌈5 * Real.log n ^ 2⌉₊ : ℕ) - 13 / 4 ∧
      n < (Nat.primeCounting ⌈5 * Real.log n ^ 2⌉₊).choose j := by
  set u := Real.log n with hu_def
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := lt_of_lt_of_le (pow_pos (by norm_num) 709) hn
    exact_mod_cast this
  have hu : 491.4 ≤ u := by
    have hn' : (2 : ℝ) ^ 709 ≤ (n : ℝ) := by
      have := (Nat.cast_le (α := ℝ)).2 hn
      rwa [Nat.cast_pow, Nat.cast_ofNat] at this
    have h := Real.log_le_log (by positivity) hn'
    rw [Real.log_pow] at h
    have := Real.log_two_gt_d9
    norm_num at h
    linarith
  set K := ⌈5 * u ^ 2⌉₊ with hK_def
  have hK1 : 5 * u ^ 2 ≤ (K : ℝ) := Nat.le_ceil _
  have hKbig : (1205000 : ℝ) ≤ K := by nlinarith
  have hKpos : (0 : ℝ) < K := by linarith
  set x := Real.sqrt (K : ℝ) with hx_def
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hx2 : x ^ 2 = K := Real.sq_sqrt hKpos.le
  have hx1098 : 1098 ≤ x := by nlinarith
  set L := Real.log (K : ℝ) with hL_def
  have hLx : L = 2 * Real.log x := by
    rw [hL_def, ← hx2, Real.log_pow]; push_cast; ring
  have hL14 : 14 ≤ L := by
    have : (14 : ℝ) < L := by
      rw [hL_def, Real.lt_log_iff_exp_lt hKpos]
      linarith [exp_14_lt]
    linarith
  have hLpos : 0 < L := by linarith
  have hlogx : Real.log x ≤ x / 100 + 3.86 := by
    have h := Real.log_le_sub_one_of_pos (x := x / 100) (by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h
    linarith [log_100_lt']
  have hLup : L ≤ x / 50 + 7.72 := by rw [hLx]; linarith
  -- `j`
  set j := ⌊(x - 13 / 4) / L⌋₊ with hj_def
  have hxL : 0 ≤ (x - 13 / 4) / L := div_nonneg (by linarith) hLpos.le
  have hj1 : (j : ℝ) * L ≤ x - 13 / 4 := by
    have := Nat.floor_le hxL
    rwa [← hj_def, le_div_iff₀ hLpos] at this
  have hj2 : x - 13 / 4 < ((j : ℝ) + 1) * L := by
    have := Nat.lt_floor_add_one ((x - 13 / 4) / L)
    rwa [← hj_def, div_lt_iff₀ hLpos] at this
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  refine ⟨j, hj1, ?_⟩
  -- `u ≤ 0.4473 x`
  have hu0 : 0 ≤ u := by linarith
  have hux : u ≤ 0.4473 * x := by nlinarith
  -- the key inequality `u < j (L/2 - 1/2)`
  have hw : 0 ≤ x - 13 / 4 - L := by linarith
  have hjL : x - 13 / 4 - L < j * L := by linarith
  have hjL1 : (13 / 14) * (j * L) ≤ j * (L - 1) := by nlinarith
  have hkey : u < j * (L / 2 - 1 / 2) := by nlinarith
  -- `log (2x/3) ≥ L/2 - 1/2`
  set Y := 2 * x / 3 with hY_def
  have hYpos : 0 < Y := by positivity
  have hlogY : L / 2 - 1 / 2 ≤ Real.log Y := by
    have : Y = x / (3 / 2) := by rw [hY_def]; ring
    rw [this, Real.log_div (by positivity) (by norm_num)]
    have := Real.log_le_sub_one_of_pos (x := 3 / 2) (by norm_num)
    linarith
  have hnY : (n : ℝ) < Y ^ j := by
    rw [← Real.log_lt_log_iff hnpos (by positivity), Real.log_pow]
    have : (j : ℝ) * (L / 2 - 1 / 2) ≤ j * Real.log Y := mul_le_mul_of_nonneg_left hlogY hj0
    linarith
  -- Chebyshev
  set s := Nat.primeCounting K with hs_def
  have hK7 : 7 ≤ K := by
    have : (7 : ℝ) ≤ K := by linarith
    exact_mod_cast this
  have hs : (K : ℝ) * Real.log 2 ≤ s * L :=
    (Chebyshev.psi_ge_of_seven_le hK7).trans (Chebyshev.psi_le_primeCounting_mul_log K)
  have hl2 := Real.log_two_gt_d9
  have hjs : (j : ℝ) * (Y + 1) ≤ s := by
    have h1 : (j : ℝ) * L * (Y + 1) ≤ x * (Y + 1) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : x * (Y + 1) ≤ (K : ℝ) * Real.log 2 := by rw [hY_def, ← hx2]; nlinarith
    have h3 : (j : ℝ) * (Y + 1) * L ≤ s * L := by nlinarith
    exact le_of_mul_le_mul_right h3 hLpos
  have hjs' : j ≤ s + 1 := by
    have : (j : ℝ) ≤ s := le_trans (le_mul_of_one_le_right hj0 (by linarith)) hjs
    exact_mod_cast (by linarith : (j : ℝ) ≤ s + 1)
  have hcast : ((s + 1 - j : ℕ) : ℝ) = s + 1 - j := by
    rw [Nat.cast_sub hjs']; push_cast; ring
  have hbase : Y * j ≤ ((s + 1 - j : ℕ) : ℝ) := by
    rw [hcast]; linarith [show (j : ℝ) * (Y + 1) = Y * j + j by ring]
  have hfac : ((j.factorial : ℕ) : ℝ) ≤ (j : ℝ) ^ j := by exact_mod_cast Nat.factorial_le_pow j
  have hfacpos : (0 : ℝ) < (j.factorial : ℕ) := by exact_mod_cast Nat.factorial_pos j
  have hchoose : Y ^ j ≤ (s.choose j : ℝ) := by
    refine le_trans ?_ (Nat.pow_le_choose j s)
    rw [le_div_iff₀ hfacpos]
    calc Y ^ j * (j.factorial : ℕ) ≤ Y ^ j * (j : ℝ) ^ j := by gcongr
      _ = (Y * j) ^ j := by ring
      _ ≤ ((s + 1 - j : ℕ) : ℝ) ^ j := by gcongr
  exact_mod_cast hnY.trans_le hchoose

end Erdos770.Sharp
