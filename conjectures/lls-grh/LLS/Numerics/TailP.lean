import LLS.Numerics.Prime
import LLS.Numerics.Tail

/-!
# The tail for prime moduli: every `q ≥ 2^700` is `GoodP 1`

With `x = ⌊L²⌋`, `s = √x` and `l = log x ≥ 12`, clearing the denominator of `K` turns
`Φ₁(x, L) > 0` into `s²(l − 5.452) + s(l² − 1.152 l − 6.647) + 6.002 l + 9.29 > 0`.
-/

namespace LLS

open Real

lemma tailP_poly (s l : ℝ) (hs : 484 ≤ s) (hl : 12 ≤ l) :
    0 < (s - 2) * (s ^ 2 - 0.15 * s - 3 * l - 4.645 - l / 2 * (s + 0.002))
      - s * (s + 1 + l / 2) * (s + 2.302 - 2 * l) := by
  have h1 : 0 ≤ s ^ 2 * (l - 5.452) := mul_nonneg (sq_nonneg s) (by linarith)
  have h2 : 0 ≤ s * (l ^ 2 - 1.152 * l - 6.647) := mul_nonneg (by linarith) (by nlinarith)
  nlinarith

set_option maxHeartbeats 1000000 in
theorem goodP_tail (q : ℕ) (hq : 2 ^ 700 ≤ q) : GoodP 1 q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast lt_of_lt_of_le (by positivity) hq
  set L := Real.log q with hLdef
  have hL : 485.2 ≤ L := by
    have h1 : Real.log ((2 : ℝ) ^ 700) ≤ L := Real.log_le_log (by positivity) (by exact_mod_cast hq)
    rw [Real.log_pow] at h1
    have := Real.log_two_gt_d9
    push_cast at h1
    linarith
  set x := ⌊L ^ 2⌋₊ with hxdef
  have hx1 : (x : ℝ) ≤ L ^ 2 := Nat.floor_le (by positivity)
  have hx2 : L ^ 2 < x + 1 := Nat.lt_floor_add_one _
  have hxbig : (235000 : ℝ) ≤ x := by nlinarith
  have hx64 : 64 ≤ x := by exact_mod_cast (show (64 : ℝ) ≤ x by linarith)
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx64
  refine ⟨x, hx64, by simpa using hx1, ?_⟩
  set s := √(x : ℝ) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = x := Real.sq_sqrt (by positivity)
  have hs484 : 484 ≤ s := by nlinarith
  set l := Real.log x with hldef
  have hl12 : 12 ≤ l := by
    rw [hldef, Real.le_log_iff_exp_le (by linarith)]
    have h := Real.exp_one_lt_d9
    have : Real.exp 12 = Real.exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
    rw [this]
    have : Real.exp 1 ^ 12 ≤ 2.7182818286 ^ 12 := by
      gcongr
    linarith [show (2.7182818286 : ℝ) ^ 12 ≤ 235000 by norm_num]
  have hls : l ≤ 2 * s := by
    have : l = 2 * Real.log s := by
      rw [hldef, ← hss, Real.log_pow]; norm_num
    rw [this]
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < s)
    linarith
  have hLs : L ≤ s + 0.002 := by
    have : L ^ 2 < (s + 0.002) ^ 2 := by nlinarith
    nlinarith
  -- `K`
  set K := Kc x with hKdef
  have hK0 : 0 ≤ K := (Kc_pos hxR).le
  have hden : 1 - 2 / s ≤ 1 + 1 / (x : ℝ) - 2 / s := by
    have : 0 ≤ 1 / (x : ℝ) := by positivity
    linarith
  have hdpos : 0 < 1 + 1 / (x : ℝ) - 2 / s := by
    have : 2 / s ≤ 2 / 484 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs484
    linarith
  have hKe : K * (1 + 1 / (x : ℝ) - 2 / s) = s + 1 + l / 2 := by
    show Kc x * _ = _
    unfold Kc; exact div_mul_cancel₀ _ hdpos.ne'
  have hKhi : (s - 2) * K ≤ s * (s + 1 + l / 2) := by
    have h1 : K * (1 - 2 / s) ≤ s + 1 + l / 2 := by
      rw [← hKe]; exact mul_le_mul_of_nonneg_left hden hK0
    have e : (s - 2) * K = s * (K * (1 - 2 / s)) := by field_simp
    rw [e]
    exact mul_le_mul_of_nonneg_left h1 hs0
  have hkap : kap x ≤ K + l / 2 := by
    have h1x0 : 0 ≤ 1 / (x : ℝ) := by positivity
    have : K * (1 - 1 / (x : ℝ)) ≤ K := by nlinarith
    unfold kap; rw [← hKdef]; linarith
  have hEs : Eshift x ≤ -0.85 := by
    unfold Eshift
    have hpi := Erdos985.Analytic.ZeroSumAux.log_pi_gt
    have hγ := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
    have hx0 : (0 : ℝ) < x := by linarith
    have h1x : 1 / (x : ℝ) ≤ 1 / 235000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hxbig
    have h1x0 : 0 ≤ 1 / (x : ℝ) := by positivity
    have hlx : (Real.log x + 2) / x ≤ 0.005 := by
      rw [div_le_iff₀ hx0]
      have : (2 : ℝ) * s + 2 ≤ 0.005 * s ^ 2 := by nlinarith
      rw [← hss] at *; linarith
    set a := 1 - 1 / (x : ℝ)
    have ha : 0.99 ≤ a := by simp only [a]; linarith
    have h3 : 1.1364 * a ≤ Real.log Real.pi * a := mul_le_mul_of_nonneg_right hpi.le (by linarith)
    have h4 : 0.57688 * a ≤ Real.eulerMascheroniConstant * a :=
      mul_le_mul_of_nonneg_right hγ.le (by linarith)
    have e : -(1 / 2) * a * Real.log Real.pi - Real.eulerMascheroniConstant / 2 * a
        = -(1 / 2) * (Real.log Real.pi * a) - (Real.eulerMascheroniConstant * a) / 2 := by ring
    rw [e]
    linarith
  have hEt := tail_Et x (by linarith)
  have hpi := Erdos985.Analytic.ZeroSumAux.log_pi_gt
  -- the lower bound
  have hL0 : 0 ≤ L := by linarith
  have hlow : x - 0.15 * s - 3 * l - 4.645 - l / 2 * (s + 0.002)
      + K * (2 * (l - 2) - (s + 0.002) + 1.7) ≤ Phi1 x L := by
    unfold Phi1
    rw [← hKdef]
    have t2 : kap x * L ≤ (K + l / 2) * (s + 0.002) :=
      mul_le_mul hkap hLs hL0 (by linarith)
    have t3 : 1.7 * K ≤ -(2 * K * Eshift x) := by nlinarith
    have t4 : 0 ≤ 1 / 2 * Real.log Real.pi * l := by nlinarith
    have : (0.15 : ℝ) * s = 3 / 20 * s := by norm_num
    nlinarith
  have hcoef : 2 * (l - 2) - (s + 0.002) + 1.7 = -(s + 2.302 - 2 * l) := by ring
  rw [hcoef] at hlow
  have hpos : 0 < s + 2.302 - 2 * l := by
    have : l ≤ 2 * Real.log s := by rw [hldef, ← hss, Real.log_pow]; norm_num
    have hlog : Real.log s ≤ s / 8 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < s / 16 by linarith)
      rw [Real.log_div (by linarith) (by norm_num)] at this
      have h16 : Real.log 16 ≤ 3 := by
        have := Real.log_two_lt_d9
        rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith
      linarith
    linarith
  have hK2 : K * (s + 2.302 - 2 * l) * (s - 2) ≤ s * (s + 1 + l / 2) * (s + 2.302 - 2 * l) := by
    have := mul_le_mul_of_nonneg_right hKhi hpos.le
    nlinarith
  have hpoly := tailP_poly s l hs484 hl12
  have hs2 : 0 < s - 2 := by linarith
  by_contra hcon
  push Not at hcon
  have : (s - 2) * (s ^ 2 - 0.15 * s - 3 * l - 4.645 - l / 2 * (s + 0.002))
      - K * (s + 2.302 - 2 * l) * (s - 2) ≤ 0 := by
    have h := mul_le_mul_of_nonneg_left (hlow.trans hcon) hs2.le
    rw [← hss] at h
    nlinarith
  linarith

end LLS
