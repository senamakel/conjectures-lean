import LLS.Bach2.Tail2

/-!
# The tail for `c = 1.657`: every `q ≥ 2^7400` is `GoodQ (1657/1000)`

lls-grh's `LLS.goodQ_tail2` (constant `2`, `q ≥ 2^2500`) with `x = ⌊1.657 L²⌋`,
`L ≤ 0.7769 (√x + 1)` (`0.7769² · 1.657 > 1`) and `z = x^{1/8} ≥ 9`.
-/

namespace BachSharp

open Real Finset LLS

lemma tail_polyS (t : ℝ) (ht : 0 ≤ t) :
    0 < (9 + t) ^ 8 - 0.15 * (9 + t) ^ 4 - 24 * (9 + t) - 4.645
      - (1.1279 * ((9 + t) ^ 4 + 1 + 4 * (9 + t)) + 4 * (9 + t)
          + 64 * (9 + t) ^ 2 / 5.65) * (0.7769 * ((9 + t) ^ 4 + 1))
      - 384 * (9 + t) ^ 2 - 16.85 * ((9 + t) ^ 4 + 1 + 4 * (9 + t)) := by
  ring_nf
  positivity

/-- The final polynomial step. -/
lemma tail_finalS (z K l L : ℝ) (hz : 9 ≤ z) (hK0 : 0 ≤ K) (hl0 : 0 ≤ l) (hL0 : 0 ≤ L)
    (hKhi : K ≤ 1.0025 * (z ^ 4 + 1 + 4 * z)) (hlz : l ≤ 8 * z) (hL : L ≤ 0.7769 * (z ^ 4 + 1)) :
    0 < z ^ 8 - 0.15 * z ^ 4 - 3 * l - 4.645 - (1.125 * K + l / 2 + l ^ 2 / 5.65) * L
      - 6 * l ^ 2 - 16.8 * K := by
  have hl2 : l ^ 2 ≤ 64 * z ^ 2 := by nlinarith
  have hA2 : 1.125 * K + l / 2 + l ^ 2 / 5.65
      ≤ 1.1279 * (z ^ 4 + 1 + 4 * z) + 4 * z + 64 * z ^ 2 / 5.65 := by
    have h1 : 1.125 * K ≤ 1.1279 * (z ^ 4 + 1 + 4 * z) := by
      have := mul_le_mul_of_nonneg_left hKhi (by norm_num : (0:ℝ) ≤ 1.125)
      have hz0 : 0 ≤ z ^ 4 + 1 + 4 * z := by nlinarith [pow_nonneg (show (0:ℝ) ≤ z by linarith) 4]
      nlinarith
    have h2 : l ^ 2 / 5.65 ≤ 64 * z ^ 2 / 5.65 := by gcongr
    linarith
  have hA0 : 0 ≤ 1.125 * K + l / 2 + l ^ 2 / 5.65 := by positivity
  have hprod := mul_le_mul hA2 hL hL0 (by positivity)
  have hpoly := tail_polyS (z - 9) (by linarith)
  simp only [add_sub_cancel] at hpoly
  have h16 : 16.8 * K ≤ 16.85 * (z ^ 4 + 1 + 4 * z) := by
    have := mul_le_mul_of_nonneg_left hKhi (by norm_num : (0:ℝ) ≤ 16.8)
    have hz0 : 0 ≤ z ^ 4 + 1 + 4 * z := by positivity
    calc _ ≤ _ := this
      _ ≤ _ := by nlinarith
  linarith

lemma z_ge9 (z : ℝ) (hz0 : 0 ≤ z) (h : 6561 ≤ z ^ 4) : 9 ≤ z := by
  by_contra hc
  push Not at hc
  have : z ^ 4 < 9 ^ 4 := pow_lt_pow_left₀ hc hz0 (by norm_num)
  norm_num at this
  linarith

set_option maxHeartbeats 1000000 in
theorem goodQ_tailS (q : ℕ) (hq : 2 ^ 7400 ≤ q) : GoodQ (1657 / 1000) q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast lt_of_lt_of_le (by positivity) hq
  set L := Real.log q with hLdef
  have hL : 5129.2 ≤ L := by
    have h1 : Real.log ((2 : ℝ) ^ 7400) ≤ L := Real.log_le_log (by positivity) (by exact_mod_cast hq)
    rw [Real.log_pow] at h1
    have := Real.log_two_gt_d9
    push_cast at h1
    linarith
  set x := ⌊1657 / 1000 * L ^ 2⌋₊ with hxdef
  have hx1 : (x : ℝ) ≤ 1657 / 1000 * L ^ 2 := Nat.floor_le (by positivity)
  have hx2 : 1657 / 1000 * L ^ 2 < x + 1 := Nat.lt_floor_add_one _
  have hxbig : (6000000 : ℝ) ≤ x := by nlinarith
  have hx64 : 64 ≤ x := by exact_mod_cast (show (64 : ℝ) ≤ x by linarith)
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx64
  set s := √(x : ℝ) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = x := Real.sq_sqrt (by positivity)
  have hxbig2 : (43046721 : ℝ) ≤ x := by nlinarith
  have hs804 : 6561 ≤ s := by nlinarith
  set w := √s with hwdef
  set z := √w with hzdef
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hww : w ^ 2 = s := Real.sq_sqrt hs0
  have hzz : z ^ 2 = w := Real.sq_sqrt hw0
  have hz4 : z ^ 4 = s := by rw [← hww, ← hzz]; ring
  have hz8 : z ^ 8 = x := by rw [← hss, ← hz4]; ring
  have hz532 : 9 ≤ z := z_ge9 z hz0 (by rw [hz4]; linarith)
  set l := Real.log x with hldef
  have hl4 : 4 ≤ l := log_ge_four hxR
  have hlz : l ≤ 8 * z := by
    have hzpos : 0 < z := by linarith
    have : l = 8 * Real.log z := by
      rw [hldef, ← hz8]; push_cast; rw [Real.log_pow]; norm_num
    rw [this]
    have := Real.log_le_sub_one_of_pos hzpos
    linarith
  have hLs : L ≤ 0.7769 * (s + 1) := by
    have h : 1657 / 1000 * L ^ 2 < (s + 1) ^ 2 := by nlinarith
    nlinarith
  set K := Kc x with hKdef
  have hden : 1 - 2 / 6561 ≤ 1 + 1 / (x : ℝ) - 2 / s := by
    have : 2 / s ≤ 2 / 6561 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs804
    have : 0 ≤ 1 / (x : ℝ) := by positivity
    linarith
  have hden' : 1 + 1 / (x : ℝ) - 2 / s ≤ 1 + 1 / s := by
    have : 1 / (x : ℝ) ≤ 1 / s := by
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith); nlinarith
    have : 0 ≤ 2 / s := by positivity
    linarith
  have hdpos : 0 < 1 + 1 / (x : ℝ) - 2 / s := by linarith
  have hKe : K * (1 + 1 / (x : ℝ) - 2 / s) = s + 1 + l / 2 := by
    show Kc x * _ = _
    unfold Kc; exact div_mul_cancel₀ _ hdpos.ne'
  have hK0 : 0 ≤ K := (Kc_pos hxR).le
  have hKlo : s ≤ K := by
    have h1 : K * (1 + 1 / (x : ℝ) - 2 / s) ≤ K * (1 + 1 / s) := mul_le_mul_of_nonneg_left hden' hK0
    have h2 : s * (1 + 1 / s) = s + 1 := by field_simp
    by_contra h
    push Not at h
    have : K * (1 + 1 / s) < s * (1 + 1 / s) :=
      mul_lt_mul_of_pos_right h (by positivity)
    linarith
  have hKhi : K ≤ 1.0025 * (s + 1 + 4 * z) := by
    have h1 : K * (1 - 2 / 6561) ≤ s + 1 + l / 2 := by
      rw [← hKe]; exact mul_le_mul_of_nonneg_left hden hK0
    nlinarith
  have h1x : 1 / (x : ℝ) ≤ 1 / 6000000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hxbig
  have h1x0 : 0 ≤ 1 / (x : ℝ) := by positivity
  have hkap : kap x ≤ K + l / 2 := by
    have : K * (1 - 1 / (x : ℝ)) ≤ K := by nlinarith
    unfold kap; rw [← hKdef]; linarith
  have hkaplo : K * (1 - 1 / 6000000) ≤ kap x := by
    have : K * (1 - 1 / 6000000) ≤ K * (1 - 1 / (x : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) hK0
    unfold kap; rw [← hKdef]; linarith
  have hl17 : 2.826 ≤ Real.log 17 := by
    have := lpLo_le 17 (by simp); norm_num [lpLo] at this; push_cast at this; linarith
  have hbet : bet x ≤ l ^ 2 / 5.65 + K / 8 := by
    unfold bet; rw [← hKdef]
    have : l ^ 2 / (2 * Real.log 17) ≤ l ^ 2 / 5.65 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith)
    linarith
  obtain ⟨hz8b, hz4b⟩ := tail_z7 z (by linarith)
  have hl2 : l ^ 2 ≤ 64 * z ^ 2 := by
    have : 0 ≤ l := by linarith
    nlinarith
  have hβκ : bet x ≤ kap x := by
    rw [hz4] at hz4b
    have h1 : l ^ 2 / 5.65 ≤ 64 * z ^ 2 / 5.65 := by gcongr
    have h2 : K / 8 + 0.5 * K ≤ K * (1 - 1 / 6000000) := by nlinarith
    linarith
  have hEs : Eshift x ≤ 0 := tail_Es7 x hxbig (by have h := hz8b; rw [hz8] at h; linarith)
  have hEt : Etil x ≤ 1.645 := tail_Et x (by linarith)
  refine ⟨x, hx64, hx1, ?_, hβκ⟩
  have hPhi := tail_Phi x L (by linarith) (by linarith) hβκ hkap hbet hEs hEt
  rw [← hsdef, ← hldef, ← hKdef] at hPhi
  have hfin := tail_finalS z K l L hz532 hK0 (by linarith) (by linarith) (by rw [hz4]; exact hKhi)
    hlz (by rw [hz4]; exact hLs)
  rw [hz8, hz4] at hfin
  linarith

end BachSharp
