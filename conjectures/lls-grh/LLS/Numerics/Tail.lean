import LLS.Numerics.Good

/-!
# The tail: every `q ≥ 2^700` is `GoodQ 3`

Take `x = ⌊3 L²⌋` with `L = log q ≥ 485`. Write `s = √x` and `z = x^{1/8}` (two more square
roots), so that `log x = 8 log z ≤ 8z` and `z ≥ 5.38`. Crude bounds for every term of `Φ` then
reduce `Φ(x, L) > 0` to a polynomial inequality in `z` whose coefficients, after the shift
`z = 5.38 + t`, are all positive.
-/

namespace LLS

open Real Finset

lemma lp_div_le (p : ℕ) (hp : p ∈ smallP) : Real.log p / ((p : ℝ) - 1) ≤ 0.7 := by
  have hhi := le_lpHi p (mem_insert_of_mem hp)
  simp only [smallP, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
  · rw [div_le_iff₀ (by norm_num)]
    norm_num [lpHi] at hhi ⊢
    linarith

lemma lp_nonneg' (p : ℕ) (hp : p ∈ smallP) : 0 ≤ Real.log p := by
  have hlo := lpLo_le p (mem_insert_of_mem hp)
  have : 0 ≤ lpLo p := by
    simp only [smallP, mem_insert, mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [lpLo]
  linarith

lemma lp_le_three (p : ℕ) (hp : p ∈ smallP) : Real.log p ≤ 3 := by
  have hhi := le_lpHi p (mem_insert_of_mem hp)
  simp only [smallP, mem_insert, mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [lpHi] at hhi ⊢ <;> linarith

lemma tail_poly (t : ℝ) (ht : 0 ≤ t) :
    0 < (5.38 + t) ^ 8 - 0.15 * (5.38 + t) ^ 4 - 24 * (5.38 + t) - 4.645
      - (1.1277 * ((5.38 + t) ^ 4 + 1 + 4 * (5.38 + t)) + 4 * (5.38 + t)
          + 64 * (5.38 + t) ^ 2 / 5.65) * (0.5774 * ((5.38 + t) ^ 4 + 1))
      - 384 * (5.38 + t) ^ 2 - 16.85 * ((5.38 + t) ^ 4 + 1 + 4 * (5.38 + t)) := by
  ring_nf
  positivity

/-- The small primes cost at most `6 l² + 16.8 K` in total. -/
lemma tail_small (x : ℕ) (hxR : (64 : ℝ) ≤ x) (hβκ : bet x ≤ kap x) :
    ∑ p ∈ smallP, max 0 (Wp x p - bet x * Real.log p)
      ≤ 6 * Real.log x ^ 2 + 16.8 * Kc x := by
  have hl4 := log_ge_four hxR
  have hK0 := (Kc_pos hxR).le
  have hbet0 := bet_nonneg hxR
  have hb : ∀ p ∈ smallP, max 0 (Wp x p - bet x * Real.log p)
      ≤ Real.log x ^ 2 + 2.8 * Kc x := by
    intro p hp
    have hlp0 := lp_nonneg' p hp
    have hlp3 := lp_le_three p hp
    have hdiv := lp_div_le p hp
    have hA : Ap x p ≤ Real.log x ^ 2 / 2 + 1.4 * Kc x := by
      unfold Ap
      have h1 : (Real.log x - Real.log p / 2) ^ 2 ≤ Real.log x ^ 2 := by nlinarith
      have h2 : Kc x * (Real.log p / ((p : ℝ) - 1)) ≤ Kc x * 0.7 :=
        mul_le_mul_of_nonneg_left hdiv hK0
      nlinarith
    have hp1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by
      simp only [smallP, Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
    have hA0 : 0 ≤ Ap x p := by unfold Ap; positivity
    have hkl : 0 ≤ kap x * Real.log p := mul_nonneg (le_trans hbet0 hβκ) hlp0
    have hW : Wp x p ≤ 2 * Ap x p := by
      unfold Wp
      rcases le_total 0 (Ap x p - kap x * Real.log p) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    have : 0 ≤ bet x * Real.log p := mul_nonneg hbet0 hlp0
    exact max_le (by positivity) (by linarith)
  calc _ ≤ ∑ p ∈ smallP, (Real.log x ^ 2 + 2.8 * Kc x) := Finset.sum_le_sum hb
    _ = 6 * Real.log x ^ 2 + 16.8 * Kc x := by simp [smallP]; ring

/-- A crude lower bound for `Φ`. -/
lemma tail_Phi (x : ℕ) (L : ℝ) (hxR : (64 : ℝ) ≤ x) (hL : 0 ≤ L) (hβκ : bet x ≤ kap x)
    (hkap : kap x ≤ Kc x + Real.log x / 2) (hbet : bet x ≤ Real.log x ^ 2 / 5.65 + Kc x / 8)
    (hEs : Eshift x ≤ 0) (hEt : Etil x ≤ 1.645) :
    x - 0.15 * √(x : ℝ) - 3 * Real.log x - 4.645
      - (1.125 * Kc x + Real.log x / 2 + Real.log x ^ 2 / 5.65) * L - 6 * Real.log x ^ 2
      - 16.8 * Kc x ≤ Phi x L := by
  have hx64 : (64 : ℝ) ≤ x := hxR
  have hl4 := log_ge_four hx64
  have hK0 := (Kc_pos hx64).le
  have hpi := Erdos985.Analytic.ZeroSumAux.log_pi_gt
  have hs := tail_small x hx64 hβκ
  unfold Phi
  have t1 : 0 ≤ 2 * Kc x * (Real.log x - 2) := by nlinarith
  have t2 : kap x * L ≤ (Kc x + Real.log x / 2) * L := mul_le_mul_of_nonneg_right hkap hL
  have t3 : 0 ≤ -(2 * Kc x * Eshift x) := by nlinarith
  have t4 : 0 ≤ 1 / 2 * Real.log Real.pi * Real.log x := by nlinarith
  have t5 : bet x * L ≤ (Real.log x ^ 2 / 5.65 + Kc x / 8) * L := mul_le_mul_of_nonneg_right hbet hL
  have e : (1.125 * Kc x + Real.log x / 2 + Real.log x ^ 2 / 5.65) * L
      = (Kc x + Real.log x / 2) * L + (Real.log x ^ 2 / 5.65 + Kc x / 8) * L := by ring
  have : (0.15 : ℝ) * √(x : ℝ) = 3 / 20 * √(x : ℝ) := by norm_num
  linarith

lemma z_ge (z : ℝ) (hz0 : 0 ≤ z) (h : 840 ≤ z ^ 4) : 5.38 ≤ z := by
  by_contra hc
  push Not at hc
  have : z ^ 4 < 5.38 ^ 4 := pow_lt_pow_left₀ hc hz0 (by norm_num)
  norm_num at this
  linarith

/-- The final polynomial step. -/
lemma tail_final (z K l L : ℝ) (hz : 5.38 ≤ z) (hK0 : 0 ≤ K) (hl0 : 0 ≤ l) (hL0 : 0 ≤ L)
    (hKhi : K ≤ 1.0024 * (z ^ 4 + 1 + 4 * z)) (hlz : l ≤ 8 * z) (hL : L ≤ 0.5774 * (z ^ 4 + 1)) :
    0 < z ^ 8 - 0.15 * z ^ 4 - 3 * l - 4.645 - (1.125 * K + l / 2 + l ^ 2 / 5.65) * L
      - 6 * l ^ 2 - 16.8 * K := by
  have hl2 : l ^ 2 ≤ 64 * z ^ 2 := by nlinarith
  have hA2 : 1.125 * K + l / 2 + l ^ 2 / 5.65
      ≤ 1.1277 * (z ^ 4 + 1 + 4 * z) + 4 * z + 64 * z ^ 2 / 5.65 := by
    have h1 : 1.125 * K ≤ 1.1277 * (z ^ 4 + 1 + 4 * z) := by
      have := mul_le_mul_of_nonneg_left hKhi (by norm_num : (0:ℝ) ≤ 1.125)
      calc _ ≤ _ := this
        _ = _ := by ring
    have h2 : l ^ 2 / 5.65 ≤ 64 * z ^ 2 / 5.65 := by gcongr
    linarith
  have hA0 : 0 ≤ 1.125 * K + l / 2 + l ^ 2 / 5.65 := by positivity
  have hprod := mul_le_mul hA2 hL hL0 (by positivity)
  have hpoly := tail_poly (z - 5.38) (by linarith)
  simp only [add_sub_cancel] at hpoly
  have h16 : 16.8 * K ≤ 16.85 * (z ^ 4 + 1 + 4 * z) := by
    have := mul_le_mul_of_nonneg_left hKhi (by norm_num : (0:ℝ) ≤ 16.8)
    have hz0 : 0 ≤ z ^ 4 + 1 + 4 * z := by positivity
    calc _ ≤ _ := this
      _ ≤ _ := by nlinarith
  linarith

lemma tail_Es (x : ℝ) (hx : 706000 ≤ x) (hl : Real.log x + 2 ≤ 0.01 * x) : Eshift x ≤ 0 := by
  unfold Eshift
  have hpi := Erdos985.Analytic.ZeroSumAux.log_pi_gt
  have hγ := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
  have hx0 : 0 < x := by linarith
  have h1x : 1 / x ≤ 1 / 706000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hx
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

lemma tail_Et (x : ℝ) (hx : 1 ≤ x) : Etil x ≤ 1.645 := by
  unfold Etil
  have h1 := Real.pi_lt_d4
  have h2 := Real.pi_pos
  have hγ := Erdos985.Analytic.DigammaAux.eulerMascheroniConstant_gt
  have h3 : Real.pi ^ 2 < 3.1416 ^ 2 := by nlinarith
  have h4 : 0 ≤ Real.eulerMascheroniConstant / 2 * Real.log x :=
    mul_nonneg (by linarith) (Real.log_nonneg hx)
  nlinarith

lemma tail_z (z : ℝ) (hz : 5.38 ≤ z) : 8 * z + 2 ≤ 0.01 * z ^ 8 ∧ 64 * z ^ 2 / 5.65 ≤ 0.5 * z ^ 4 := by
  have h2 : 28.9 ≤ z ^ 2 := by nlinarith
  have h4 : 835 ≤ z ^ 4 := by nlinarith
  constructor
  · have : z ≤ z ^ 4 / 150 := by nlinarith
    nlinarith
  · have : 28.9 * z ^ 2 ≤ z ^ 2 * z ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg z)
    have e : z ^ 4 = z ^ 2 * z ^ 2 := by ring
    have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
    rw [e, div_le_iff₀ (by norm_num)]
    nlinarith

set_option maxHeartbeats 1000000 in
theorem goodQ_tail (q : ℕ) (hq : 2 ^ 700 ≤ q) : GoodQ 3 q := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast lt_of_lt_of_le (by positivity) hq
  set L := Real.log q with hLdef
  have hL : 485.2 ≤ L := by
    have h1 : Real.log ((2 : ℝ) ^ 700) ≤ L := Real.log_le_log (by positivity) (by exact_mod_cast hq)
    rw [Real.log_pow] at h1
    have := Real.log_two_gt_d9
    push_cast at h1
    linarith
  set x := ⌊3 * L ^ 2⌋₊ with hxdef
  have hx1 : (x : ℝ) ≤ 3 * L ^ 2 := Nat.floor_le (by positivity)
  have hx2 : 3 * L ^ 2 < x + 1 := Nat.lt_floor_add_one _
  have hxbig : (706000 : ℝ) ≤ x := by nlinarith
  have hx64 : 64 ≤ x := by exact_mod_cast (show (64 : ℝ) ≤ x by linarith)
  have hxR : (64 : ℝ) ≤ x := by exact_mod_cast hx64
  set s := √(x : ℝ) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hss : s ^ 2 = x := Real.sq_sqrt (by positivity)
  have hs840 : 840 ≤ s := by nlinarith
  set w := √s with hwdef
  set z := √w with hzdef
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hww : w ^ 2 = s := Real.sq_sqrt hs0
  have hzz : z ^ 2 = w := Real.sq_sqrt hw0
  have hz4 : z ^ 4 = s := by rw [← hww, ← hzz]; ring
  have hz8 : z ^ 8 = x := by rw [← hss, ← hz4]; ring
  have hz538 : 5.38 ≤ z := z_ge z hz0 (by rw [hz4]; exact hs840)
  set l := Real.log x with hldef
  have hl4 : 4 ≤ l := log_ge_four hxR
  have hlz : l ≤ 8 * z := by
    have hzpos : 0 < z := by linarith
    have : l = 8 * Real.log z := by
      rw [hldef, ← hz8]; push_cast; rw [Real.log_pow]; norm_num
    rw [this]
    have := Real.log_le_sub_one_of_pos hzpos
    linarith
  have hLs : L ≤ 0.5774 * (s + 1) := by
    have h : 3 * L ^ 2 < (s + 1) ^ 2 := by nlinarith
    nlinarith
  set K := Kc x with hKdef
  have hden : 1 - 2 / 840 ≤ 1 + 1 / (x : ℝ) - 2 / s := by
    have : 2 / s ≤ 2 / 840 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hs840
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
  have hKhi : K ≤ 1.0024 * (s + 1 + 4 * z) := by
    have h1 : K * (1 - 2 / 840) ≤ s + 1 + l / 2 := by
      rw [← hKe]; exact mul_le_mul_of_nonneg_left hden hK0
    nlinarith
  have h1x : 1 / (x : ℝ) ≤ 1 / 706000 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hxbig
  have h1x0 : 0 ≤ 1 / (x : ℝ) := by positivity
  have hkap : kap x ≤ K + l / 2 := by
    have : K * (1 - 1 / (x : ℝ)) ≤ K := by nlinarith
    unfold kap; rw [← hKdef]; linarith
  have hkaplo : K * (1 - 1 / 706000) ≤ kap x := by
    have : K * (1 - 1 / 706000) ≤ K * (1 - 1 / (x : ℝ)) := mul_le_mul_of_nonneg_left (by linarith) hK0
    unfold kap; rw [← hKdef]; linarith
  have hl17 : 2.826 ≤ Real.log 17 := by
    have := lpLo_le 17 (by simp); norm_num [lpLo] at this; push_cast at this; linarith
  have hbet : bet x ≤ l ^ 2 / 5.65 + K / 8 := by
    unfold bet; rw [← hKdef]
    have : l ^ 2 / (2 * Real.log 17) ≤ l ^ 2 / 5.65 :=
      div_le_div_of_nonneg_left (sq_nonneg _) (by norm_num) (by linarith)
    linarith
  obtain ⟨hz8b, hz4b⟩ := tail_z z hz538
  have hl2 : l ^ 2 ≤ 64 * z ^ 2 := by
    have : 0 ≤ l := by linarith
    nlinarith
  have hβκ : bet x ≤ kap x := by
    rw [hz4] at hz4b
    have h1 : l ^ 2 / 5.65 ≤ 64 * z ^ 2 / 5.65 := by gcongr
    have h2 : K / 8 + 0.5 * K ≤ K * (1 - 1 / 706000) := by nlinarith
    linarith
  have hEs : Eshift x ≤ 0 := tail_Es x hxbig (by have h := hz8b; rw [hz8] at h; linarith)
  have hEt : Etil x ≤ 1.645 := tail_Et x (by linarith)
  refine ⟨x, hx64, hx1, ?_, hβκ⟩
  have hPhi := tail_Phi x L (by linarith) (by linarith) hβκ hkap hbet hEs hEt
  rw [← hsdef, ← hldef, ← hKdef] at hPhi
  have hfin := tail_final z K l L hz538 hK0 (by linarith) (by linarith) (by rw [hz4]; exact hKhi)
    hlz (by rw [hz4]; exact hLs)
  rw [hz8, hz4] at hfin
  linarith

end LLS
