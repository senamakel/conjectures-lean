import Erdos985.Numerics

/-!
# For `p ≥ 10^8`, the inequality of `PrimitiveRootSq.key_inequality` is impossible

With `s = √p`, `L = log p`, `A = s + 2 + 3/p`, `ω = ω(p - 1)`,
`B₁ = A (2/3)(L + 5/3) + L + 1.6` (modulus `p`) and `B₂ = A (2/3)(2L + 5/3) + L + 1.6`
(modulus `p²`), we show

`(p/2 + √p/20 + 3)/p + B₂ < θ (p/2 - √p/20 - 3 - (2^ω - 1) B₁)`

whenever `θ ≥ (36495360/223092870)(28/29)^ω`. The cases are erdos-985's: `ω ≤ 8`, `ω = 9`
(then `p - 1 ≥ 223092870`) and `ω ≥ 10` (then `16^ω · 30030 ≤ 16^6 p`); `log` is bounded by a
tangent line. The tight case is `ω = 9`, with a relative margin of about 1.6% at
`p = 223092871`.
-/

namespace PrimitiveRootSq

open Real

/-- `B(c)` is monotone in `A` and `L`. -/
lemma bach_mono (A A' L L' c : ℝ) (hA0 : 0 ≤ A) (hA : A ≤ A') (hL0 : 0 ≤ L) (hL : L ≤ L')
    (hc : 0 ≤ c) :
    A * ((2 / 3) * (c * L + 5 / 3)) + (L + 1) + 0.6
      ≤ A' * ((2 / 3) * (c * L' + 5 / 3)) + (L' + 1) + 0.6 := by
  have h1 : (2 / 3) * (c * L + 5 / 3) ≤ (2 / 3) * (c * L' + 5 / 3) := by nlinarith
  have h2 : 0 ≤ (2 / 3) * (c * L + 5 / 3) := by positivity
  nlinarith [mul_le_mul hA h1 h2 (hA0.trans hA)]

/-- Abstract finish for the cases `ω ≤ 9`. -/
lemma finish_small (θ θ₀ X B1 B1u B2 B2u Su M S : ℝ) (hθ : θ₀ ≤ θ) (hθ₀ : 0 < θ₀)
    (hX : 0 ≤ X - 1) (hXM : X - 1 ≤ M) (hB1 : 0 ≤ B1) (hB1u : B1 ≤ B1u) (hB2 : B2 ≤ B2u)
    (hB2u : 0 ≤ B2u) (hSu : Su ≤ 0.5001) (hpoly : 0.5001 + B2u < θ₀ * (S - M * B1u)) :
    Su + B2 < θ * (S - (X - 1) * B1) := by
  have hD0 : 0 < S - M * B1u := by
    by_contra h; rw [not_lt] at h; nlinarith
  have hD : S - M * B1u ≤ S - (X - 1) * B1 := by
    have : (X - 1) * B1 ≤ M * B1u := mul_le_mul hXM hB1u hB1 (by linarith)
    linarith
  have := mul_le_mul hθ hD hD0.le (by linarith)
  linarith

/-- The polynomial inequality for `ω ≤ 8`. -/
lemma poly8 (s : ℝ) (hs : 10000 ≤ s) :
    0.5001 + ((s + 2.0001) * ((2 / 3) * (2 * (2 * (14 * 0.6931471808 + s / 16384 - 1)) + 5 / 3))
        + (2 * (14 * 0.6931471808 + s / 16384 - 1) + 1) + 0.6)
      < 0.1235 * (s ^ 2 / 2 - (s / 20 + 3) - 255 * ((s + 2.0001) * ((2 / 3) *
        (1 * (2 * (14 * 0.6931471808 + s / 16384 - 1)) + 5 / 3))
        + (2 * (14 * 0.6931471808 + s / 16384 - 1) + 1) + 0.6)) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hs) (sub_nonneg.2 hs)]

/-- The polynomial inequality for `ω = 9`. -/
lemma poly9 (s : ℝ) (hs : 14936 ≤ s) :
    0.5001 + ((s + 2.0001) * ((2 / 3) * (2 * (2 * (14 * 0.6931471808 + s / 16384 - 1)) + 5 / 3))
        + (2 * (14 * 0.6931471808 + s / 16384 - 1) + 1) + 0.6)
      < 0.1192 * (s ^ 2 / 2 - (s / 20 + 3) - 511 * ((s + 2.0001) * ((2 / 3) *
        (1 * (2 * (14 * 0.6931471808 + s / 16384 - 1)) + 5 / 3))
        + (2 * (14 * 0.6931471808 + s / 16384 - 1) + 1) + 0.6)) := by
  nlinarith [mul_nonneg (sub_nonneg.2 hs) (sub_nonneg.2 hs)]

/-- The polynomial inequality for `ω ≥ 10` (`s = t²`). -/
lemma poly10 (t : ℝ) (ht : 200 ≤ t) :
    (4.87 * t + 1) * (0.5001 + ((t ^ 2 + 2.0001) * ((2 / 3) *
        (2 * (4 * (5.5451774464 + t / 256 - 1)) + 5 / 3)) + (4 * (5.5451774464 + t / 256 - 1) + 1)
        + 0.6))
      < 117 * ((t ^ 2) ^ 2 / 2 - (t ^ 2 / 20 + 3) - 4.87 * t * ((t ^ 2 + 2.0001) * ((2 / 3) *
        (1 * (4 * (5.5451774464 + t / 256 - 1)) + 5 / 3)) + (4 * (5.5451774464 + t / 256 - 1) + 1)
        + 0.6)) := by
  have h0 := sub_nonneg.2 ht
  nlinarith [mul_nonneg (mul_nonneg (mul_nonneg h0 h0) h0) h0, mul_nonneg (mul_nonneg h0 h0) h0,
    mul_nonneg h0 h0]

theorem numerics (p : ℕ) (hp0 : 10 ^ 8 ≤ p) (θ : ℝ)
    (hθ : (36495360 / 223092870 : ℝ) * (28 / 29) ^ (p - 1).primeFactors.card ≤ θ) :
    ((p : ℝ) / 2 + (√(p : ℝ) / 20 + 3)) / p
        + ((√(p : ℝ) + 2 + 3 / p) * ((2 / 3) * (2 * Real.log p + 5 / 3)) + (Real.log p + 1) + 0.6)
      < θ * ((p : ℝ) / 2 - (√(p : ℝ) / 20 + 3)
        - ((2 : ℝ) ^ (p - 1).primeFactors.card - 1)
          * ((√(p : ℝ) + 2 + 3 / p) * ((2 / 3) * (Real.log p + 5 / 3)) + (Real.log p + 1) + 0.6)) := by
  have hpR : (10 ^ 8 : ℝ) ≤ p := by exact_mod_cast hp0
  have hp0' : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  have hs2 : √(p : ℝ) ^ 2 = p := Real.sq_sqrt hp0'.le
  have hspos : 0 < √(p : ℝ) := Real.sqrt_pos.2 hp0'
  have hsge : (10000 : ℝ) ≤ √(p : ℝ) := (Real.le_sqrt (by norm_num) hp0'.le).2 (by linarith)
  have hL0 : 0 ≤ Real.log p := (Real.log_pos hp1).le
  have hl2b := Real.log_two_lt_d9
  have hlogs : Real.log p = 2 * Real.log (√(p : ℝ)) := by
    rw [Real.log_sqrt hp0'.le]; ring
  have hA0 : 0 ≤ √(p : ℝ) + 2 + 3 / p := by positivity
  have hA : √(p : ℝ) + 2 + 3 / p ≤ √(p : ℝ) + 2.0001 := by
    have : 3 / (p : ℝ) ≤ 3 / 10 ^ 8 := by gcongr
    norm_num at this ⊢; linarith
  have hSu : ((p : ℝ) / 2 + (√(p : ℝ) / 20 + 3)) / p ≤ 0.5001 := by
    rw [div_le_iff₀ hp0']; nlinarith
  have hpd : (p : ℝ) / 2 = √(p : ℝ) ^ 2 / 2 := by rw [hs2]
  rw [hpd]
  have hX1 : (1 : ℝ) ≤ 2 ^ (p - 1).primeFactors.card := one_le_pow₀ (by norm_num)
  have hpnz : p - 1 ≠ 0 := by omega
  have hB10 : 0 ≤ (√(p : ℝ) + 2 + 3 / p) * ((2 / 3) * (Real.log p + 5 / 3)) + (Real.log p + 1) + 0.6 := by
    positivity
  -- the tangent bound at `2^14`, used for `ω ≤ 9`
  have hU14 : Real.log p ≤ 2 * (14 * 0.6931471808 + √(p : ℝ) / 16384 - 1) := by
    have h := Erdos985.log_le_tangent (√(p : ℝ)) 16384 hspos (by norm_num)
    have : Real.log (16384 : ℝ) = 14 * Real.log 2 := by
      rw [show (16384 : ℝ) = 2 ^ 14 by norm_num, Real.log_pow]; norm_num
    rw [hlogs]; linarith
  have hU0 : (0 : ℝ) ≤ 2 * (14 * 0.6931471808 + √(p : ℝ) / 16384 - 1) := by
    have : (0 : ℝ) ≤ √(p : ℝ) / 16384 := by positivity
    linarith
  have hB1 := bach_mono _ _ _ _ 1 hA0 hA hL0 hU14 (by norm_num)
  have hB2 := bach_mono _ _ _ _ 2 hA0 hA hL0 hU14 (by norm_num)
  simp only [one_mul] at hB1
  have hB2u0 : (0 : ℝ) ≤ (√(p : ℝ) + 2.0001) * ((2 / 3) *
      (2 * (2 * (14 * 0.6931471808 + √(p : ℝ) / 16384 - 1)) + 5 / 3))
      + (2 * (14 * 0.6931471808 + √(p : ℝ) / 16384 - 1) + 1) + 0.6 := by positivity
  rcases (show (p - 1).primeFactors.card ≤ 8 ∨ (p - 1).primeFactors.card = 9 ∨
      10 ≤ (p - 1).primeFactors.card by omega) with h8 | h9 | h10
  · -- ω ≤ 8
    have hXle : (2 : ℝ) ^ (p - 1).primeFactors.card - 1 ≤ 255 := by
      have : (2 : ℝ) ^ (p - 1).primeFactors.card ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) h8
      norm_num at this; linarith
    have hθ8 : (0.1235 : ℝ) ≤ θ := by
      have : (28 / 29 : ℝ) ^ 8 ≤ (28 / 29) ^ (p - 1).primeFactors.card :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) h8
      have h' : (0.1235 : ℝ) ≤ 36495360 / 223092870 * (28 / 29) ^ 8 := by norm_num
      nlinarith
    have hpoly := poly8 _ hsge
    simp only [one_mul] at hpoly
    exact finish_small _ _ _ _ _ _ _ _ _ _ hθ8 (by norm_num) (by linarith) hXle hB10 hB1 hB2
      hB2u0 hSu hpoly
  · -- ω = 9
    have hnat := Erdos985.pow_card_primeFactors_mul_le 23 (p - 1) hpnz
    rw [h9, show ∏ r ∈ (Finset.range 23).filter Nat.Prime, r = 9699690 by decide,
      show ((Finset.range 23).filter Nat.Prime).card = 8 by decide] at hnat
    norm_num at hnat
    have hp9 : 223092871 ≤ p := by omega
    have hpR9 : (223092871 : ℝ) ≤ p := by exact_mod_cast hp9
    have hsge' : (14936 : ℝ) ≤ √(p : ℝ) := (Real.le_sqrt (by norm_num) hp0'.le).2 (by linarith)
    have hXe : (2 : ℝ) ^ (p - 1).primeFactors.card - 1 ≤ 511 := by rw [h9]; norm_num
    have hθ9 : (0.1192 : ℝ) ≤ θ := by
      rw [h9] at hθ
      have h' : (0.1192 : ℝ) ≤ 36495360 / 223092870 * (28 / 29) ^ 9 := by norm_num
      linarith
    have hpoly := poly9 _ hsge'
    simp only [one_mul] at hpoly
    exact finish_small _ _ _ _ _ _ _ _ _ _ hθ9 (by norm_num) (by linarith) hXe hB10 hB1 hB2
      hB2u0 hSu hpoly
  · -- ω ≥ 10
    set k := (p - 1).primeFactors.card with hk
    set X : ℝ := 2 ^ k with hX
    have hnat := Erdos985.pow_card_primeFactors_mul_le 16 (p - 1) hpnz
    rw [← hk, show ∏ r ∈ (Finset.range 16).filter Nat.Prime, r = 30030 by decide,
      show ((Finset.range 16).filter Nat.Prime).card = 6 by decide] at hnat
    have h16 : 16 ^ 10 ≤ 16 ^ k := Nat.pow_le_pow_right (by norm_num) h10
    have hp10 : 1600000000 ≤ p := by
      have := Nat.mul_le_mul_right 30030 h16
      norm_num at hnat this; omega
    have hpR10 : (1600000000 : ℝ) ≤ p := by exact_mod_cast hp10
    have hX4 : X ^ 4 * 30030 ≤ p * 16 ^ 6 := by
      have : 16 ^ k * 30030 ≤ p * 16 ^ 6 :=
        hnat.trans (Nat.mul_le_mul_right _ (Nat.sub_le p 1))
      rw [hX, ← pow_mul, mul_comm k 4, pow_mul]
      exact_mod_cast (by norm_num at this ⊢; exact this)
    have hsge2 : (40000 : ℝ) ≤ √(p : ℝ) := (Real.le_sqrt (by norm_num) hp0'.le).2 (by linarith)
    set s := √(p : ℝ) with hs_def
    set t := √s with ht_def
    have ht2 : t ^ 2 = s := Real.sq_sqrt hspos.le
    have htpos : 0 < t := Real.sqrt_pos.2 hspos
    have htge : (200 : ℝ) ≤ t := (Real.le_sqrt (by norm_num) hspos.le).2 (by linarith)
    have ht4 : (p : ℝ) = t ^ 4 := by rw [← hs2, ← ht2]; ring
    have hXle : X ≤ 4.87 * t + 1 := by
      by_contra hcon
      rw [not_le] at hcon
      have h1 : 4.87 * t ≤ X := by linarith
      have h2 : (4.87 * t) ^ 4 ≤ X ^ 4 := pow_le_pow_left₀ (by positivity) h1 4
      rw [ht4] at hX4
      have : (0:ℝ) < t ^ 4 := by positivity
      nlinarith
    have hU : Real.log p ≤ 4 * (5.5451774464 + t / 256 - 1) := by
      have h := Erdos985.log_le_tangent t 256 htpos (by norm_num)
      have : Real.log (256 : ℝ) = 8 * Real.log 2 := by
        rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
      rw [ht4, Real.log_pow]; push_cast; linarith
    have hA' : s + 2 + 3 / p ≤ t ^ 2 + 2.0001 := by rw [ht2]; exact hA
    have hB1t := bach_mono _ _ _ _ 1 hA0 hA' hL0 hU (by norm_num)
    have hB2t := bach_mono _ _ _ _ 2 hA0 hA' hL0 hU (by norm_num)
    simp only [one_mul] at hB1t
    have hθX : (117 : ℝ) ≤ θ * X := by
      have e : (36495360 / 223092870 : ℝ) * (28 / 29) ^ k * X
          = 36495360 / 223092870 * (56 / 29) ^ k := by
        rw [hX, mul_assoc, ← mul_pow]; norm_num
      have : (56 / 29 : ℝ) ^ 10 ≤ (56 / 29) ^ k := pow_le_pow_right₀ (by norm_num) h10
      have h' : (117 : ℝ) ≤ 36495360 / 223092870 * (56 / 29) ^ 10 := by norm_num
      have hX0 : 0 ≤ X := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hθ hX0]
    have hpoly := poly10 t htge
    simp only [one_mul] at hpoly
    rw [ht2] at hpoly
    set B1 := (s + 2 + 3 / (p : ℝ)) * ((2 / 3) * (Real.log p + 5 / 3)) + (Real.log p + 1) + 0.6
    set B1u := (s + 2.0001) * ((2 / 3) * (4 * (5.5451774464 + t / 256 - 1) + 5 / 3))
      + (4 * (5.5451774464 + t / 256 - 1) + 1) + 0.6
    set B2u := (s + 2.0001) * ((2 / 3) * (2 * (4 * (5.5451774464 + t / 256 - 1)) + 5 / 3))
      + (4 * (5.5451774464 + t / 256 - 1) + 1) + 0.6
    rw [ht2] at hB1t hB2t
    have hB2u0 : 0 ≤ B2u := by positivity
    have hD : s ^ 2 / 2 - (s / 20 + 3) - 4.87 * t * B1u ≤ s ^ 2 / 2 - (s / 20 + 3) - (X - 1) * B1 := by
      have : (X - 1) * B1 ≤ 4.87 * t * B1u :=
        mul_le_mul (by linarith) hB1t hB10 (by positivity)
      linarith
    have hD0pos : 0 < s ^ 2 / 2 - (s / 20 + 3) - 4.87 * t * B1u := by nlinarith
    have hXpos : 0 < X := by linarith
    have hmain : X * (0.5001 + B2u) < X * (θ * (s ^ 2 / 2 - (s / 20 + 3) - (X - 1) * B1)) := by
      have e1 : X * (0.5001 + B2u) ≤ (4.87 * t + 1) * (0.5001 + B2u) :=
        mul_le_mul_of_nonneg_right hXle (by positivity)
      have e2 : 117 * (s ^ 2 / 2 - (s / 20 + 3) - 4.87 * t * B1u)
          ≤ (θ * X) * (s ^ 2 / 2 - (s / 20 + 3) - (X - 1) * B1) :=
        mul_le_mul hθX hD hD0pos.le (by positivity)
      nlinarith
    have hfin := lt_of_mul_lt_mul_left hmain hXpos.le
    linarith

end PrimitiveRootSq
