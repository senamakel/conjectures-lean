import Mathlib

/-!
# The numerical contradiction for `n ≥ 10^8`

With `x = ⌊√n⌋ ≥ 10^4`, `N ≤ 4n` the conductor and `ω` the number of prime factors of `2n`,
the GRH lower bound `x/2 − √x/20 − 3 − B` for the split-prime sum exceeds the sieve upper bound
`2(√x + 1 + ω) log x`, where `B = (√x + 2 + 3/x)(2/3)(log N + 5/3) + log x + 1.6`.
At `x = 10^4` the margin is about 856 (out of 5000).
-/

namespace Weinberger

open Real

/-- `log s ≤ s/100 + 3.8521` for `s > 0`. -/
lemma log_le_linear {s : ℝ} (hs : 0 < s) : Real.log s ≤ s / 100 + 3.8521 := by
  have h1 : Real.log (s / 100) ≤ s / 100 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div hs.ne' (by norm_num)] at h1
  have h2 : Real.log 100 < 4.8521 := by
    have : Real.log 100 < Real.log 128 := Real.log_lt_log (by norm_num) (by norm_num)
    have h7 : Real.log 128 = 7 * Real.log 2 := by
      rw [show (128 : ℝ) = 2 ^ 7 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9
    linarith
  linarith

theorem numerics {x N n ω : ℝ} (hx : 10 ^ 4 ≤ x) (hN1 : 1 ≤ N) (hN : N ≤ 4 * n)
    (hn : n < (x + 1) ^ 2) (hn0 : 0 < n) (hω0 : 0 ≤ ω) (hω : ω * Real.log 2 ≤ Real.log (2 * n)) :
    2 * (√x + 1 + ω) * Real.log x
      < x / 2 - √x / 20 - 3
        - ((√x + 2 + 3 / x) * ((2 / 3) * (Real.log N + 5 / 3)) + (Real.log x + 1) + 0.6) := by
  set s := √x with hs_def
  have hx0 : 0 < x := by linarith
  have hs100 : 100 ≤ s := by
    rw [hs_def, show (100 : ℝ) = √(10 ^ 4) by
      rw [show (10 : ℝ) ^ 4 = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hx
  have hxs : x = s ^ 2 := (Real.sq_sqrt hx0.le).symm
  set L := Real.log s with hL_def
  have hlogx : Real.log x = 2 * L := by
    rw [hxs, Real.log_pow]; push_cast; ring
  have hL0 : 0 ≤ L := Real.log_nonneg (by linarith)
  have hLle : L ≤ s / 100 + 3.8521 := log_le_linear (by linarith)
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  -- `log N ≤ log 5 + 4L ≤ 2.0795 + 4L`
  have hNx : N ≤ 5 * s ^ 4 := by
    have : 4 * (x + 1) ^ 2 ≤ 5 * x ^ 2 := by nlinarith
    rw [hxs] at this; nlinarith
  have hlogN : Real.log N ≤ 2.0795 + 4 * L := by
    have h1 : Real.log N ≤ Real.log (5 * s ^ 4) := Real.log_le_log (by linarith) hNx
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at h1
    have h5 : Real.log 5 < Real.log 8 := Real.log_lt_log (by norm_num) (by norm_num)
    have h8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    push_cast at h1
    linarith
  -- `ω log 2 ≤ log (2n) ≤ log 3 + 4L ≤ 1.3863 + 4L`
  have hlog2n : Real.log (2 * n) ≤ 1.3863 + 4 * L := by
    have h2n : 2 * n ≤ 3 * s ^ 4 := by
      have : 2 * (x + 1) ^ 2 ≤ 3 * x ^ 2 := by nlinarith
      rw [hxs] at this hn; nlinarith
    have h1 : Real.log (2 * n) ≤ Real.log (3 * s ^ 4) := Real.log_le_log (by linarith) h2n
    rw [Real.log_mul (x := 3) (by norm_num) (by positivity), Real.log_pow] at h1
    have h3 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    push_cast at h1
    linarith
  have hωL : ω * L * 0.6931 ≤ (1.3863 + 4 * L) * L := by
    have : ω * 0.6931 ≤ 1.3863 + 4 * L := by nlinarith
    nlinarith
  have h3x : 3 / x ≤ 0.0003 := by
    rw [div_le_iff₀ hx0]; nlinarith
  rw [hlogx]
  -- reduce to a polynomial inequality in `s` and `L`
  have hA : (s + 2 + 3 / x) * ((2 / 3) * (Real.log N + 5 / 3))
      ≤ (s + 2.0003) * ((2 / 3) * (2.0795 + 4 * L + 5 / 3)) := by
    have hlN0 : 0 ≤ Real.log N := Real.log_nonneg hN1
    apply mul_le_mul (by linarith) (by linarith) (by positivity) (by linarith)
  have hxs' : x / 2 = s ^ 2 / 2 := by rw [hxs]
  rw [hxs']
  -- multiply through by `0.6931` to clear `ω`
  have key : 0.6931 * (2 * (s + 1 + ω) * (2 * L)) + 0.6931 * ((s + 2.0003) * ((2 / 3) * (2.0795 + 4 * L + 5 / 3))
      + (2 * L + 1) + 0.6 + s / 20 + 3) < 0.6931 * (s ^ 2 / 2) := by
    have e1 : 0.6931 * (2 * (s + 1 + ω) * (2 * L)) = 4 * 0.6931 * (s + 1) * L + 4 * (ω * L * 0.6931) := by ring
    rw [e1]
    have hsL : s * L ≤ s * (s / 100 + 3.8521) := mul_le_mul_of_nonneg_left hLle (by linarith)
    have hLL : L * L ≤ (s / 100 + 3.8521) * (s / 100 + 3.8521) := mul_self_le_mul_self hL0 hLle
    nlinarith
  nlinarith

end Weinberger
