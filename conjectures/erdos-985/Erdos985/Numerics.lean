import Erdos985.Bach

namespace Erdos985

/-!
# For `p ≥ 10^8`, Bach's bound beats the character-sum error  (MTT Theorem 2 at `x = p`)

Write `ω = ω(p - 1)`.  We split into `ω ≤ 8` (use `p ≥ 10^8`), `ω = 9` (then `p - 1 ≥ 23 · 9699690`,
the product of the first nine primes) and `ω ≥ 10` (then `16^ω ≤ 559 p`, so `2^ω ≤ 4.87 p^{1/4}`).
In each case `log` is bounded by a tangent line and the rest is polynomial arithmetic.
-/

open Real

/-- If `n ≠ 0` then `B^ω(n) · ∏_{r < B prime} r ≤ n · B^{π(B-1)}`. -/
lemma pow_card_primeFactors_mul_le (B n : ℕ) (hn : n ≠ 0) :
    B ^ n.primeFactors.card * ∏ r ∈ (Finset.range B).filter Nat.Prime, r
      ≤ n * B ^ ((Finset.range B).filter Nat.Prime).card := by
  set S := n.primeFactors
  set T := (Finset.range B).filter Nat.Prime
  have hS : ∏ r ∈ S, r ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) (Nat.prod_primeFactors_dvd n)
  have hset : T.filter (· ∈ S) = S.filter (· < B) := by
    ext r
    simp only [T, S, Finset.mem_filter, Finset.mem_range, Nat.mem_primeFactors]
    tauto
  have e1 := Finset.prod_filter_mul_prod_filter_not S (· < B) (fun r => r)
  have e2 := Finset.prod_filter_mul_prod_filter_not T (· ∈ S) (fun r => r)
  have c1 := Finset.card_filter_add_card_filter_not (s := S) (p := (· < B))
  have c2 := Finset.card_filter_add_card_filter_not (s := T) (p := (· ∈ S))
  rw [hset] at e2 c2
  have b1 : B ^ (S.filter (fun r => ¬ r < B)).card ≤ ∏ r ∈ S.filter (fun r => ¬ r < B), r :=
    Finset.pow_card_le_prod _ _ _ (fun x hx => by
      simp only [Finset.mem_filter] at hx; omega)
  have b2 : ∏ r ∈ T.filter (fun r => ¬ r ∈ S), r ≤ B ^ (T.filter (fun r => ¬ r ∈ S)).card :=
    Finset.prod_le_pow_card _ _ _ (fun x hx => by
      simp only [T, Finset.mem_filter, Finset.mem_range] at hx; omega)
  rw [← e2, ← c1, ← c2]
  set P := ∏ r ∈ S.filter (· < B), r
  set a := (S.filter (· < B)).card
  set b := (S.filter (fun r => ¬ r < B)).card
  set d := (T.filter (fun r => ¬ r ∈ S)).card
  calc B ^ (a + b) * (P * ∏ r ∈ T.filter (fun r => ¬ r ∈ S), r)
      ≤ B ^ (a + b) * (P * B ^ d) := by gcongr
    _ = (P * B ^ b) * B ^ (a + d) := by ring
    _ ≤ (P * ∏ r ∈ S.filter (fun r => ¬ r < B), r) * B ^ (a + d) := by gcongr
    _ ≤ n * B ^ (a + d) := by rw [e1]; gcongr

/-- Bound on `bachC p p` in terms of lower bounds for `√p`, `p`, `log p`. -/
lemma bachC_le (p s0 L0 : ℝ) (hp : 1 ≤ p) (hs0 : 0 < s0) (hL0 : 0 < L0)
    (hs : s0 ≤ √p) (hL : L0 ≤ Real.log p) :
    bachC p p ≤ (2/3) * (1 + 2 / s0 + 3 / p) * (1 + (5/3) / L0) + (1 / s0 + 2 / (s0 * L0)) := by
  have hpp : p ≤ p ^ (3/2 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hp (by norm_num : (1:ℝ) ≤ 3/2)
  have hp0 : 0 < p := by linarith
  have hsp : 0 < √p := lt_of_lt_of_le hs0 hs
  have hLp : 0 < Real.log p := lt_of_lt_of_le hL0 hL
  have e : (Real.log p + 2) / (√p * Real.log p) = 1 / √p + 2 / (√p * Real.log p) := by
    field_simp
  unfold bachC
  rw [e]
  gcongr

lemma log_le_tangent (x a : ℝ) (hx : 0 < x) (ha : 0 < a) :
    Real.log x ≤ Real.log a + x / a - 1 := by
  have := Real.log_le_sub_one_of_pos (div_pos hx ha)
  rw [Real.log_div hx.ne' ha.ne'] at this
  linarith

lemma bachC_pos (p : ℝ) (hp : 1 < p) : 0 < bachC p p := by
  have := Real.log_pos hp
  unfold bachC
  have : 0 < p := by linarith
  positivity

lemma finish_aux (A c s L Aa c0 U : ℝ) (hs : 0 < s) (hA0 : 0 ≤ A) (hA : A ≤ Aa)
    (hc0 : 0 ≤ c) (hc : c ≤ c0) (hL0 : 0 ≤ L) (hL : L ≤ U)
    (h : s * (Aa * c0 * U) < s ^ 2 / 2 - s / 20 - 3) :
    A * (c * s * L) < s ^ 2 / 2 - (s / 20 + 3) := by
  have h1 : A * c * L ≤ Aa * c0 * U := by
    have := hA0.trans hA
    have := hc0.trans hc
    gcongr
  have h2 : s * (A * c * L) ≤ s * (Aa * c0 * U) := mul_le_mul_of_nonneg_left h1 hs.le
  nlinarith

theorem bach_inequality_large (p : ℕ) (_hp : p.Prime) (hp0 : 10 ^ 8 ≤ p) :
    ((2 : ℝ) ^ (p - 1).primeFactors.card - 1) * (bachC p p * √p * Real.log p)
      < p / 2 - (√p / 20 + 3) := by
  set k := (p - 1).primeFactors.card with hk
  have hpR : (10 ^ 8 : ℝ) ≤ p := by exact_mod_cast hp0
  have hp1 : (1 : ℝ) < p := by linarith
  have hp0' : (0 : ℝ) < p := by linarith
  set s := √(p : ℝ) with hs_def
  have hs2 : s ^ 2 = p := Real.sq_sqrt hp0'.le
  have hspos : 0 < s := Real.sqrt_pos.2 hp0'
  have hsge : (10000 : ℝ) ≤ s := (Real.le_sqrt (by norm_num) hp0'.le).2 (by linarith)
  have hLpos : 0 < Real.log p := Real.log_pos hp1
  have hc0 : 0 ≤ bachC p p := (bachC_pos p hp1).le
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hlogs : Real.log p = 2 * Real.log s := by
    rw [hs_def, Real.log_sqrt hp0'.le]; ring
  have hX1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  have hA0 : (0 : ℝ) ≤ 2 ^ k - 1 := by linarith
  rw [show (p : ℝ) / 2 = s ^ 2 / 2 by rw [hs2]]
  -- tangent bound for log s at 2^14
  have hU14 : Real.log p ≤ 2 * (14 * 0.6931471808 + s / 16384 - 1) := by
    have h := log_le_tangent s 16384 hspos (by norm_num)
    have : Real.log (16384 : ℝ) = 14 * Real.log 2 := by
      rw [show (16384 : ℝ) = 2 ^ 14 by norm_num, Real.log_pow]; norm_num
    rw [hlogs]; linarith
  have hpnz : p - 1 ≠ 0 := by omega
  rcases (show k ≤ 8 ∨ k = 9 ∨ 10 ≤ k by omega) with h8 | h9 | h10
  · -- ω ≤ 8
    have hL : (18.02 : ℝ) ≤ Real.log p := by
      have : Real.log ((2 : ℝ) ^ 26) ≤ Real.log p := Real.log_le_log (by norm_num) (by linarith)
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hc := bachC_le p 10000 18.02 hp1.le (by norm_num) (by norm_num) hsge hL
    have h3 : 3 / (p : ℝ) ≤ 3 / 10 ^ 8 := by gcongr
    have hc' : bachC p p ≤ 0.7286 := by
      have : (2/3 : ℝ) * (1 + 2 / 10000 + 3 / p) * (1 + (5/3) / 18.02)
          ≤ (2/3) * (1 + 2 / 10000 + 3 / 10^8) * (1 + (5/3) / 18.02) := by gcongr
      norm_num at hc this ⊢; linarith
    have hA : (2 : ℝ) ^ k - 1 ≤ 255 := by
      have : (2 : ℝ) ^ k ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) h8
      norm_num at this; linarith
    refine finish_aux _ _ _ _ 255 0.7286 _ hspos hA0 hA hc0 hc' hLpos.le hU14 ?_
    nlinarith
  · -- ω = 9
    have hnat := pow_card_primeFactors_mul_le 23 (p - 1) hpnz
    rw [← hk, h9, show ∏ r ∈ (Finset.range 23).filter Nat.Prime, r = 9699690 by decide,
      show ((Finset.range 23).filter Nat.Prime).card = 8 by decide] at hnat
    norm_num at hnat
    have hp9 : 223092871 ≤ p := by omega
    have hpR9 : (223092871 : ℝ) ≤ p := by exact_mod_cast hp9
    have hsge' : (14936 : ℝ) ≤ s := (Real.le_sqrt (by norm_num) hp0'.le).2 (by linarith)
    have hL : (18.71 : ℝ) ≤ Real.log p := by
      have : Real.log ((2 : ℝ) ^ 27) ≤ Real.log p := Real.log_le_log (by norm_num) (by linarith)
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hc := bachC_le p 14936 18.71 hp1.le (by norm_num) (by norm_num) hsge' hL
    have hc' : bachC p p ≤ 0.7265 := by
      have : (2/3 : ℝ) * (1 + 2 / 14936 + 3 / p) * (1 + (5/3) / 18.71)
          ≤ (2/3) * (1 + 2 / 14936 + 3 / 223092871) * (1 + (5/3) / 18.71) := by gcongr
      norm_num at hc this ⊢; linarith
    have hA : (2 : ℝ) ^ k - 1 ≤ 511 := by rw [h9]; norm_num
    refine finish_aux _ _ _ _ 511 0.7265 _ hspos hA0 hA hc0 hc' hLpos.le hU14 ?_
    nlinarith
  · -- ω ≥ 10
    have hnat := pow_card_primeFactors_mul_le 16 (p - 1) hpnz
    rw [← hk, show ∏ r ∈ (Finset.range 16).filter Nat.Prime, r = 30030 by decide,
      show ((Finset.range 16).filter Nat.Prime).card = 6 by decide] at hnat
    have h16 : 16 ^ 10 ≤ 16 ^ k := Nat.pow_le_pow_right (by norm_num) h10
    have hp10 : 1600000000 ≤ p := by
      have := Nat.mul_le_mul_right 30030 h16
      norm_num at hnat this; omega
    have hpR10 : (1600000000 : ℝ) ≤ p := by exact_mod_cast hp10
    have hX4 : ((2 : ℝ) ^ k) ^ 4 * 30030 ≤ p * 16 ^ 6 := by
      have : 16 ^ k * 30030 ≤ p * 16 ^ 6 :=
        hnat.trans (Nat.mul_le_mul_right _ (Nat.sub_le p 1))
      rw [← pow_mul, mul_comm k 4, pow_mul]
      exact_mod_cast (by norm_num at this ⊢; exact this)
    have hsge2 : (40000 : ℝ) ≤ s := (Real.le_sqrt (by norm_num) hp0'.le).2 (by linarith)
    set t := √s with ht_def
    have ht2 : t ^ 2 = s := Real.sq_sqrt hspos.le
    have htpos : 0 < t := Real.sqrt_pos.2 hspos
    have htge : (200 : ℝ) ≤ t := (Real.le_sqrt (by norm_num) hspos.le).2 (by linarith)
    have ht4 : (p : ℝ) = t ^ 4 := by rw [← hs2, ← ht2]; ring
    have hX : (2 : ℝ) ^ k - 1 ≤ 4.87 * t := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 : 4.87 * t ≤ (2 : ℝ) ^ k := by linarith
      have h2 : (4.87 * t) ^ 4 ≤ ((2 : ℝ) ^ k) ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
      rw [ht4] at hX4
      have : (0:ℝ) < t ^ 4 := by positivity
      nlinarith
    have hU : Real.log p ≤ 4 * (5.5451774464 + t / 256 - 1) := by
      have h := log_le_tangent t 256 htpos (by norm_num)
      have : Real.log (256 : ℝ) = 8 * Real.log 2 := by
        rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
      rw [ht4, Real.log_pow]; push_cast; linarith
    have hL : (18.02 : ℝ) ≤ Real.log p := by
      have : Real.log ((2 : ℝ) ^ 26) ≤ Real.log p := Real.log_le_log (by norm_num) (by linarith)
      rw [Real.log_pow] at this; push_cast at this; linarith
    have hc := bachC_le p 10000 18.02 hp1.le (by norm_num) (by norm_num) hsge hL
    have h3 : 3 / (p : ℝ) ≤ 3 / 10 ^ 8 := by gcongr
    have hc' : bachC p p ≤ 0.7286 := by
      have : (2/3 : ℝ) * (1 + 2 / 10000 + 3 / p) * (1 + (5/3) / 18.02)
          ≤ (2/3) * (1 + 2 / 10000 + 3 / 10^8) * (1 + (5/3) / 18.02) := by gcongr
      norm_num at hc this ⊢; linarith
    refine finish_aux _ _ _ _ (4.87 * t) 0.7286 _ hspos hA0 hX hc0 hc' hLpos.le hU ?_
    rw [← ht2]
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 htge) (sub_nonneg.2 htge)) (sub_nonneg.2 htge),
      mul_nonneg (sub_nonneg.2 htge) (sub_nonneg.2 htge)]

end Erdos985
