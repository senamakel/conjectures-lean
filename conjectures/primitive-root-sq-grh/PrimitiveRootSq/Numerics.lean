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

theorem numerics (p : ℕ) (hp0 : 10 ^ 8 ≤ p) (θ : ℝ)
    (hθ : (36495360 / 223092870 : ℝ) * (28 / 29) ^ (p - 1).primeFactors.card ≤ θ) :
    ((p : ℝ) / 2 + (√(p : ℝ) / 20 + 3)) / p
        + ((√(p : ℝ) + 2 + 3 / p) * ((2 / 3) * (2 * Real.log p + 5 / 3)) + (Real.log p + 1) + 0.6)
      < θ * ((p : ℝ) / 2 - (√(p : ℝ) / 20 + 3)
        - ((2 : ℝ) ^ (p - 1).primeFactors.card - 1)
          * ((√(p : ℝ) + 2 + 3 / p) * ((2 / 3) * (Real.log p + 5 / 3)) + (Real.log p + 1) + 0.6)) := by
  set k := (p - 1).primeFactors.card with hk
  have hpR : (10 ^ 8 : ℝ) ≤ p := by exact_mod_cast hp0
  have hp0' : (0 : ℝ) < p := by linarith
  have hp1 : (1 : ℝ) < p := by linarith
  set s := √(p : ℝ) with hs_def
  have hs2 : s ^ 2 = p := Real.sq_sqrt hp0'.le
  have hspos : 0 < s := Real.sqrt_pos.2 hp0'
  have hsge : (10000 : ℝ) ≤ s := (Real.le_sqrt (by norm_num) hp0'.le).2 (by linarith)
  set L := Real.log p with hL_def
  have hL0 : 0 ≤ L := (Real.log_pos hp1).le
  have hl2b := Real.log_two_lt_d9
  have hlogs : L = 2 * Real.log s := by
    rw [hL_def, hs_def, Real.log_sqrt hp0'.le]; ring
  set A := s + 2 + 3 / (p : ℝ) with hA_def
  have hA0 : 0 ≤ A := by positivity
  have hA : A ≤ s + 2.0001 := by
    have : 3 / (p : ℝ) ≤ 3 / 10 ^ 8 := by gcongr
    simp only [hA_def]; norm_num at this ⊢; linarith
  -- the principal terms, in terms of `s`
  have hSu : ((p : ℝ) / 2 + (s / 20 + 3)) / p ≤ 0.5001 := by
    rw [div_le_iff₀ hp0', ← hs2]; nlinarith
  rw [show (p : ℝ) / 2 = s ^ 2 / 2 by rw [hs2]]
  have hX1 : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
  set X : ℝ := 2 ^ k with hX
  -- `θ > 0`
  have hθ0 : 0 < θ := lt_of_lt_of_le (by positivity) hθ
  have hpnz : p - 1 ≠ 0 := by omega
  rcases (show k ≤ 8 ∨ k = 9 ∨ 10 ≤ k by omega) with h8 | h9 | h10
  · -- ω ≤ 8
    have hU : L ≤ 2 * (14 * 0.6931471808 + s / 16384 - 1) := by
      have h := Erdos985.log_le_tangent s 16384 hspos (by norm_num)
      have : Real.log (16384 : ℝ) = 14 * Real.log 2 := by
        rw [show (16384 : ℝ) = 2 ^ 14 by norm_num, Real.log_pow]; norm_num
      rw [hlogs]; linarith
    set U := 2 * (14 * 0.6931471808 + s / 16384 - 1) with hU_def
    have hB1 := bach_mono A (s + 2.0001) L U 1 hA0 hA hL0 hU (by norm_num)
    have hB2 := bach_mono A (s + 2.0001) L U 2 hA0 hA hL0 hU (by norm_num)
    have hXle : X - 1 ≤ 255 := by
      have : (2 : ℝ) ^ k ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) h8
      norm_num at this; linarith
    have hθ8 : (0.1235 : ℝ) ≤ θ := by
      have : (28 / 29 : ℝ) ^ 8 ≤ (28 / 29) ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num) h8
      have h' : (0.1235 : ℝ) ≤ 36495360 / 223092870 * (28 / 29) ^ 8 := by norm_num
      nlinarith
    set B1 := A * ((2 / 3) * (L + 5 / 3)) + (L + 1) + 0.6
    set B1u := (s + 2.0001) * ((2 / 3) * (1 * U + 5 / 3)) + (U + 1) + 0.6 with hB1u
    set B2u := (s + 2.0001) * ((2 / 3) * (2 * U + 5 / 3)) + (U + 1) + 0.6 with hB2u
    have hB1' : B1 ≤ B1u := by simpa using hB1
    have hB10 : 0 ≤ B1 := by positivity
    have hD : s ^ 2 / 2 - (s / 20 + 3) - 255 * B1u ≤ s ^ 2 / 2 - (s / 20 + 3) - (X - 1) * B1 := by
      have : (X - 1) * B1 ≤ 255 * B1u := by
        have hX0 : 0 ≤ X - 1 := by linarith
        nlinarith
      linarith
    have hpoly : 0.5001 + B2u < 0.1235 * (s ^ 2 / 2 - (s / 20 + 3) - 255 * B1u) := by
      simp only [hB1u, hB2u, hU_def]
      nlinarith [mul_nonneg (sub_nonneg.2 hsge) (sub_nonneg.2 hsge)]
    have hD0 : 0 < s ^ 2 / 2 - (s / 20 + 3) - 255 * B1u := by
      have : 0 ≤ B2u := by simp only [hB2u, hU_def]; positivity
      linarith
    have h2 : 0.1235 * (s ^ 2 / 2 - (s / 20 + 3) - 255 * B1u)
        ≤ θ * (s ^ 2 / 2 - (s / 20 + 3) - (X - 1) * B1) :=
      mul_le_mul hθ8 hD hD0.le hθ0.le
    have hB2' : A * ((2 / 3) * (2 * L + 5 / 3)) + (L + 1) + 0.6 ≤ B2u := hB2
    linarith
  · -- ω = 9
    have hnat := Erdos985.pow_card_primeFactors_mul_le 23 (p - 1) hpnz
    rw [← hk, h9, show ∏ r ∈ (Finset.range 23).filter Nat.Prime, r = 9699690 by decide,
      show ((Finset.range 23).filter Nat.Prime).card = 8 by decide] at hnat
    norm_num at hnat
    have hp9 : 223092871 ≤ p := by omega
    have hpR9 : (223092871 : ℝ) ≤ p := by exact_mod_cast hp9
    have hsge' : (14936 : ℝ) ≤ s := (Real.le_sqrt (by norm_num) hp0'.le).2 (by linarith)
    have hU : L ≤ 2 * (14 * 0.6931471808 + s / 16384 - 1) := by
      have h := Erdos985.log_le_tangent s 16384 hspos (by norm_num)
      have : Real.log (16384 : ℝ) = 14 * Real.log 2 := by
        rw [show (16384 : ℝ) = 2 ^ 14 by norm_num, Real.log_pow]; norm_num
      rw [hlogs]; linarith
    set U := 2 * (14 * 0.6931471808 + s / 16384 - 1) with hU_def
    have hB1 := bach_mono A (s + 2.0001) L U 1 hA0 hA hL0 hU (by norm_num)
    have hB2 := bach_mono A (s + 2.0001) L U 2 hA0 hA hL0 hU (by norm_num)
    have hXe : X - 1 = 511 := by simp only [hX, h9]; norm_num
    have hθ9 : (0.1192 : ℝ) ≤ θ := by
      rw [h9] at hθ
      have h' : (0.1192 : ℝ) ≤ 36495360 / 223092870 * (28 / 29) ^ 9 := by norm_num
      linarith
    set B1 := A * ((2 / 3) * (L + 5 / 3)) + (L + 1) + 0.6
    set B1u := (s + 2.0001) * ((2 / 3) * (1 * U + 5 / 3)) + (U + 1) + 0.6 with hB1u
    set B2u := (s + 2.0001) * ((2 / 3) * (2 * U + 5 / 3)) + (U + 1) + 0.6 with hB2u
    have hB1' : B1 ≤ B1u := by simpa using hB1
    have hD : s ^ 2 / 2 - (s / 20 + 3) - 511 * B1u ≤ s ^ 2 / 2 - (s / 20 + 3) - (X - 1) * B1 := by
      rw [hXe]; linarith
    have hpoly : 0.5001 + B2u < 0.1192 * (s ^ 2 / 2 - (s / 20 + 3) - 511 * B1u) := by
      simp only [hB1u, hB2u, hU_def]
      nlinarith [mul_nonneg (sub_nonneg.2 hsge') (sub_nonneg.2 hsge')]
    have hD0 : 0 < s ^ 2 / 2 - (s / 20 + 3) - 511 * B1u := by
      have : 0 ≤ B2u := by simp only [hB2u, hU_def]; positivity
      linarith
    have h2 : 0.1192 * (s ^ 2 / 2 - (s / 20 + 3) - 511 * B1u)
        ≤ θ * (s ^ 2 / 2 - (s / 20 + 3) - (X - 1) * B1) :=
      mul_le_mul hθ9 hD hD0.le hθ0.le
    have hB2' : A * ((2 / 3) * (2 * L + 5 / 3)) + (L + 1) + 0.6 ≤ B2u := hB2
    linarith
  · -- ω ≥ 10
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
    have hsge2 : (40000 : ℝ) ≤ s := (Real.le_sqrt (by norm_num) hp0'.le).2 (by linarith)
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
    have hU : L ≤ 4 * (5.5451774464 + t / 256 - 1) := by
      have h := Erdos985.log_le_tangent t 256 htpos (by norm_num)
      have : Real.log (256 : ℝ) = 8 * Real.log 2 := by
        rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
      rw [hL_def, ht4, Real.log_pow]; push_cast; linarith
    set U := 4 * (5.5451774464 + t / 256 - 1) with hU_def
    have hB1 := bach_mono A (s + 2.0001) L U 1 hA0 hA hL0 hU (by norm_num)
    have hB2 := bach_mono A (s + 2.0001) L U 2 hA0 hA hL0 hU (by norm_num)
    -- `θ · 2^ω ≥ 117`
    have hθX : (117 : ℝ) ≤ θ * X := by
      have e : (36495360 / 223092870 : ℝ) * (28 / 29) ^ k * X
          = 36495360 / 223092870 * (56 / 29) ^ k := by
        rw [hX, mul_assoc, ← mul_pow]; norm_num
      have : (56 / 29 : ℝ) ^ 10 ≤ (56 / 29) ^ k := pow_le_pow_right₀ (by norm_num) h10
      have h' : (117 : ℝ) ≤ 36495360 / 223092870 * (56 / 29) ^ 10 := by norm_num
      have hX0 : 0 ≤ X := by positivity
      nlinarith [mul_le_mul_of_nonneg_right hθ hX0]
    set B1 := A * ((2 / 3) * (L + 5 / 3)) + (L + 1) + 0.6
    set B1u := (s + 2.0001) * ((2 / 3) * (1 * U + 5 / 3)) + (U + 1) + 0.6 with hB1u
    set B2u := (s + 2.0001) * ((2 / 3) * (2 * U + 5 / 3)) + (U + 1) + 0.6 with hB2u
    have hB1' : B1 ≤ B1u := by simpa using hB1
    have hB10 : 0 ≤ B1 := by positivity
    have hB1u0 : 0 ≤ B1u := hB10.trans hB1'
    have hD : s ^ 2 / 2 - (s / 20 + 3) - 4.87 * t * B1u
        ≤ s ^ 2 / 2 - (s / 20 + 3) - (X - 1) * B1 := by
      have : (X - 1) * B1 ≤ 4.87 * t * B1u := by
        have hX0 : 0 ≤ X - 1 := by linarith
        exact mul_le_mul (by linarith) hB1' hB10 (by positivity)
      linarith
    set D0 := s ^ 2 / 2 - (s / 20 + 3) - 4.87 * t * B1u with hD0_def
    have hB2u0 : 0 ≤ B2u := by simp only [hB2u, hU_def]; positivity
    have hpoly : (4.87 * t + 1) * (0.5001 + B2u) < 117 * D0 := by
      simp only [hD0_def, hB1u, hB2u, hU_def]
      rw [← ht2]
      have h0 := sub_nonneg.2 htge
      nlinarith [mul_nonneg (mul_nonneg (mul_nonneg h0 h0) h0) h0, mul_nonneg (mul_nonneg h0 h0) h0,
        mul_nonneg h0 h0, mul_nonneg (mul_nonneg (mul_nonneg h0 h0) h0) htpos.le,
        mul_nonneg (mul_nonneg h0 h0) htpos.le]
    have hD0pos : 0 < D0 := by nlinarith
    have hXpos : 0 < X := by linarith
    -- `X θ D ≥ 117 D ≥ 117 D0 > X (0.5001 + B2u)`
    have hmain : X * (0.5001 + B2u) < X * (θ * (s ^ 2 / 2 - (s / 20 + 3) - (X - 1) * B1)) := by
      have hDpos : 0 ≤ s ^ 2 / 2 - (s / 20 + 3) - (X - 1) * B1 := by linarith
      have e1 : X * (0.5001 + B2u) ≤ (4.87 * t + 1) * (0.5001 + B2u) :=
        mul_le_mul_of_nonneg_right hXle (by positivity)
      have e2 : 117 * D0 ≤ (θ * X) * (s ^ 2 / 2 - (s / 20 + 3) - (X - 1) * B1) :=
        mul_le_mul hθX hD hD0pos.le (by positivity)
      nlinarith
    have hfin := lt_of_mul_lt_mul_left hmain hXpos.le
    have hB2' : A * ((2 / 3) * (2 * L + 5 / 3)) + (L + 1) + 0.6 ≤ B2u := hB2
    linarith

end PrimitiveRootSq
