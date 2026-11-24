import LLS.Numerics.Tail

/-!
# The tail for `c = 2`: every `q ≥ 2^2500` is `GoodQ 2`

The argument of `LLS.Numerics.Tail` with `x = ⌊2 L²⌋`, `L ≤ 0.7072 (s + 1)`, `z ≥ 7`.
-/

namespace LLS

open Real Finset

lemma tail_poly2 (t : ℝ) (ht : 0 ≤ t) :
    0 < (7 + t) ^ 8 - 0.15 * (7 + t) ^ 4 - 24 * (7 + t) - 4.645
      - (1.1279 * ((7 + t) ^ 4 + 1 + 4 * (7 + t)) + 4 * (7 + t)
          + 64 * (7 + t) ^ 2 / 5.65) * (0.7072 * ((7 + t) ^ 4 + 1))
      - 384 * (7 + t) ^ 2 - 16.85 * ((7 + t) ^ 4 + 1 + 4 * (7 + t)) := by
  ring_nf
  positivity

/-- The final polynomial step. -/
lemma tail_final2 (z K l L : ℝ) (hz : 7 ≤ z) (hK0 : 0 ≤ K) (hl0 : 0 ≤ l) (hL0 : 0 ≤ L)
    (hKhi : K ≤ 1.0025 * (z ^ 4 + 1 + 4 * z)) (hlz : l ≤ 8 * z) (hL : L ≤ 0.7072 * (z ^ 4 + 1)) :
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
  have hpoly := tail_poly2 (z - 7) (by linarith)
  simp only [add_sub_cancel] at hpoly
  have h16 : 16.8 * K ≤ 16.85 * (z ^ 4 + 1 + 4 * z) := by
    have := mul_le_mul_of_nonneg_left hKhi (by norm_num : (0:ℝ) ≤ 16.8)
    have hz0 : 0 ≤ z ^ 4 + 1 + 4 * z := by positivity
    calc _ ≤ _ := this
      _ ≤ _ := by nlinarith
  linarith

lemma z_ge7 (z : ℝ) (hz0 : 0 ≤ z) (h : 2401 ≤ z ^ 4) : 7 ≤ z := by
  by_contra hc
  push Not at hc
  have : z ^ 4 < 7 ^ 4 := pow_lt_pow_left₀ hc hz0 (by norm_num)
  norm_num at this
  linarith

lemma tail_z7 (z : ℝ) (hz : 7 ≤ z) :
    8 * z + 2 ≤ 0.01 * z ^ 8 ∧ 64 * z ^ 2 / 5.65 ≤ 0.5 * z ^ 4 := by
  have h2 : 49 ≤ z ^ 2 := by nlinarith
  have h4 : 2401 ≤ z ^ 4 := by nlinarith
  constructor
  · have : z ≤ z ^ 4 / 150 := by nlinarith
    nlinarith
  · have : 49 * z ^ 2 ≤ z ^ 2 * z ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg z)
    have e : z ^ 4 = z ^ 2 * z ^ 2 := by ring
    have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
    rw [e, div_le_iff₀ (by norm_num)]
    nlinarith

lemma tail_Es7 (x : ℝ) (hx : 6000000 ≤ x) (hl : Real.log x + 2 ≤ 0.01 * x) : Eshift x ≤ 0 := by
  unfold Eshift
  have hpi := Erdos985.Analytic.ZeroSumAux.log_pi_gt
  have hγ := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
  have hx0 : 0 < x := by linarith
  have h1x : 1 / x ≤ 1 / 6000000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
  have h1x0 : 0 ≤ 1 / x := by positivity
  have hlx : (Real.log x + 2) / x ≤ 0.01 := by rw [div_le_iff₀ hx0]; linarith
  set a := 1 - 1 / x
  have ha : 0.99 ≤ a := by simp only [a]; linarith
  have h3 : 1.1364 * a ≤ Real.log Real.pi * a := mul_le_mul_of_nonneg_right hpi.le (by linarith)
  have h4 : 0.57688 * a ≤ Real.eulerMascheroniConstant * a :=
    mul_le_mul_of_nonneg_right hγ.le (by linarith)
  have e : -(1 / 2) * a * Real.log Real.pi - Real.eulerMascheroniConstant / 2 * a
      = -(1 / 2) * (Real.log Real.pi * a) - (Real.eulerMascheroniConstant * a) / 2 := by ring
  rw [e]
  linarith

set_option maxHeartbeats 1000000 in
theorem goodQ_tail2 (q : ℕ) (hq : 2 ^ 2500 ≤ q) : GoodQ 2 q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast lt_of_lt_of_le (by positivity) hq
  set L := Real.log q with hLdef
  have hL : 1732.8 ≤ L := by
    have h1 : Real.log ((2 : ℝ) ^ 2500) ≤ L := Real.log_le_log (by positivity) (by exact_mod_cast hq)
    rw [Real.log_pow] at h1
    have := Real.log_two_gt_d9
    push_cast at h1
    linarith
  set x := ⌊2 * L ^ 2⌋₊ with hxdef
  have hx1 : (x : ℝ) ≤ 2 * L ^ 2 := Nat.floor_le (by positivity)
  have hx2 : 2 * L ^ 2 < x + 1 := Nat.lt_floor_add_one _
  have hxbig : (6000000 : ℝ) ≤ x := by nlinarith
  have hx64 : 64 ≤ x := by exact_mod_cast (show (64 : ℝ) ≤ x by linarith)
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx64
  set s := √(x : ℝ) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = x := Real.sq_sqrt (by positivity)
  have hs804 : 2450 ≤ s := by nlinarith
  set w := √s with hwdef
  set z := √w with hzdef
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hww : w ^ 2 = s := Real.sq_sqrt hs0
  have hzz : z ^ 2 = w := Real.sq_sqrt hw0
  have hz4 : z ^ 4 = s := by rw [← hww, ← hzz]; ring
  have hz8 : z ^ 8 = x := by rw [← hss, ← hz4]; ring
  have hz532 : 7 ≤ z := z_ge7 z hz0 (by rw [hz4]; linarith)
  set l := Real.log x with hldef
  have hl4 : 4 ≤ l := log_ge_four hxR
  have hlz : l ≤ 8 * z := by
    have hzpos : 0 < z := by linarith
    have : l = 8 * Real.log z := by
      rw [hldef, ← hz8]; push_cast; rw [Real.log_pow]; norm_num
    rw [this]
    have := Real.log_le_sub_one_of_pos hzpos
    linarith
  have hLs : L ≤ 0.7072 * (s + 1) := by
    have h : 2 * L ^ 2 < (s + 1) ^ 2 := by nlinarith
    nlinarith
  set K := Kc x with hKdef
  have hden : 1 - 2 / 2450 ≤ 1 + 1 / (x : ℝ) - 2 / s := by
    have : 2 / s ≤ 2 / 2450 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs804
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
    have h1 : K * (1 - 2 / 2450) ≤ s + 1 + l / 2 := by
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
  obtain ⟨hz8b, hz4b⟩ := tail_z7 z hz532
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
  have hfin := tail_final2 z K l L hz532 hK0 (by linarith) (by linarith) (by rw [hz4]; exact hKhi)
    hlz (by rw [hz4]; exact hLs)
  rw [hz8, hz4] at hfin
  linarith

end LLS
