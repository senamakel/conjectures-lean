import BachSorenson.Two.Large

/-!
# `NumericOK2 q` for every `q ≥ 2^15`

Write `L = log q ≥ 15 log 2`, `U = q L`, `x = ⌊2U²⌋`, `s = √x`, `u = x^{1/12}` (so `s = u⁶`,
`x^{1/3} = u⁴`, `x^{1/4} = u³`), `ℓ = log u`. Then

* `s ≥ 1.41421 U` and `U ≥ 10.397 q`, so `x − 1.1 s q (L + log 2 − 7/5) − 2 log 4 · q s
  ≥ s (s − 1.1 U − 1.9951 q) ≥ 1.2717 q s`;
* `u ≥ 8.8`, `ℓ ≤ 3 log 2 − 1 + u/8 ≤ 0.248 u` (tangent of `log` at `8`),
  `log x = 12 ℓ`, `⌊log₂ x⌋ ≤ 17.32 ℓ`, `L ≤ 6 ℓ`, `ω(q) ≤ L/log 2 ≤ 8.66 ℓ`;
* every other term of `NumericOK2` is at most `q` times a polynomial in `u` of degree `4`,
  plus `0.1102 q s` (the `3280` from `Σ Λ(n) n^{-21/20}`), and the polynomial is below
  `1.16 u⁶` for `u ≥ 8.8`.
-/

namespace BachSorenson.Two

open Real

lemma card_primeFactors_le_log (q : ℕ) (hq : 1 ≤ q) :
    (q.primeFactors.card : ℝ) * Real.log 2 ≤ Real.log q := by
  have h1 : 2 ^ q.primeFactors.card ≤ ∏ p ∈ q.primeFactors, p :=
    Finset.pow_card_le_prod _ _ _ fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le
  have h2 : ∏ p ∈ q.primeFactors, p ≤ q := Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  have h3 : ((2 : ℝ) ^ q.primeFactors.card) ≤ q := by exact_mod_cast h1.trans h2
  have := Real.log_le_log (by positivity) h3
  rwa [Real.log_pow] at this

/-- The numerical core, in abstract real variables. -/
lemma numeric_core {q L U s u ℓ K ω l2 l4 : ℝ} (hq : 32768 ≤ q) (hUdef : U = q * L)
    (hU : 10.397 * q ≤ U) (hsU : 1.41421 * U ≤ s) (hsu : s = u ^ 6) (hu : 8.8 ≤ u)
    (hℓ0 : 0 ≤ ℓ) (hℓu : ℓ ≤ 0.248 * u) (hK0 : 0 ≤ K) (hK : K ≤ 17.32 * ℓ) (hω0 : 0 ≤ ω)
    (hω : ω ≤ 8.66 * ℓ) (hLℓ : L ≤ 6 * ℓ) (hl2a : 0.6931 ≤ l2) (hl2b : l2 ≤ 0.6932)
    (hl40 : 0 ≤ l4) (hl4 : l4 ≤ 1.3863) :
    q * (l4 * (2 * s + 3 * u ^ 4 + 60 * u ^ 3 + K ^ 2 * u)) + 3 / 20 * s + 3 * (12 * ℓ) + 3
      + ω * (12 * ℓ) ^ 2 + (s + 1 + 12 * ℓ) * (11 / 10 * (q * (L + l2 - 7 / 5) + 3280))
      + q * ((L + 2.52) * (12 * ℓ) + ((12 * ℓ) ^ 2 / 2 + 5 * (12 * ℓ) + 2) + ω * (12 * ℓ) ^ 2)
      < s ^ 2 := by
  have hq0 : 0 < q := by linarith
  have hu0 : 0 ≤ u := by linarith
  -- powers of `u`
  have hu2 : 77.44 ≤ u ^ 2 := by
    have := mul_le_mul hu hu (by norm_num) hu0; rw [sq]; linarith
  have hu3 : 681.4 ≤ u ^ 3 := by
    have := mul_le_mul hu2 hu (by norm_num) (by positivity)
    have e : u ^ 3 = u ^ 2 * u := by ring
    rw [e]; linarith
  have hu4' : 5996 ≤ u ^ 4 := by
    have := mul_le_mul hu2 hu2 (by norm_num) (by positivity)
    have e : u ^ 4 = u ^ 2 * u ^ 2 := by ring
    rw [e]; linarith
  have hu5' : 52700 ≤ u ^ 5 := by
    have := mul_le_mul hu4' hu (by norm_num) (by positivity)
    have e : u ^ 5 = u ^ 4 * u := by ring
    rw [e]; linarith
  have h64 : 77.44 * u ^ 4 ≤ u ^ 6 := by
    have := mul_le_mul_of_nonneg_right hu2 (by positivity : (0 : ℝ) ≤ u ^ 4)
    have e : u ^ 6 = u ^ 2 * u ^ 4 := by ring
    rw [e]; linarith
  have h63 : 681.4 * u ^ 3 ≤ u ^ 6 := by
    have := mul_le_mul_of_nonneg_right hu3 (by positivity : (0 : ℝ) ≤ u ^ 3)
    have e : u ^ 6 = u ^ 3 * u ^ 3 := by ring
    rw [e]; linarith
  have h62 : 5996 * u ^ 2 ≤ u ^ 6 := by
    have := mul_le_mul_of_nonneg_right hu4' (by positivity : (0 : ℝ) ≤ u ^ 2)
    have e : u ^ 6 = u ^ 4 * u ^ 2 := by ring
    rw [e]; linarith
  have h61 : 52700 * u ≤ u ^ 6 := by
    have := mul_le_mul_of_nonneg_right hu5' hu0
    have e : u ^ 6 = u ^ 5 * u := by ring
    rw [e]; linarith
  have h60 : 464000 ≤ u ^ 6 := by linarith
  have hs0 : 0 ≤ s := by rw [hsu]; positivity
  -- `ℓ` in terms of `u`
  have hℓ2 : ℓ ^ 2 ≤ 0.0616 * u ^ 2 := by
    have := pow_le_pow_left₀ hℓ0 hℓu 2
    have e : (0.248 * u) ^ 2 = 0.061504 * u ^ 2 := by ring
    have : 0 ≤ u ^ 2 := by positivity
    linarith
  have hℓ3 : ℓ ^ 3 ≤ 0.01526 * u ^ 3 := by
    have := pow_le_pow_left₀ hℓ0 hℓu 3
    have e : (0.248 * u) ^ 3 = 0.015252992 * u ^ 3 := by ring
    have : 0 ≤ u ^ 3 := by positivity
    linarith
  have hK2 : K ^ 2 ≤ 18.48 * u ^ 2 := by
    have := pow_le_pow_left₀ hK0 hK 2
    have e : (17.32 * ℓ) ^ 2 = 299.9824 * ℓ ^ 2 := by ring
    linarith
  have hωl : ω * (12 * ℓ) ^ 2 ≤ 19.04 * u ^ 3 := by
    have h1 : ω * (12 * ℓ) ^ 2 ≤ 8.66 * ℓ * (12 * ℓ) ^ 2 :=
      mul_le_mul_of_nonneg_right hω (by positivity)
    have h2 : 8.66 * ℓ * (12 * ℓ) ^ 2 = 1247.04 * ℓ ^ 3 := by ring
    linarith
  -- the main term
  have hM : q * (l4 * (2 * s)) + s * (11 / 10 * (q * (L + l2 - 7 / 5)))
      ≤ s ^ 2 - 1.27 * (q * s) := by
    have hql2 : q * l2 ≤ 0.6932 * q := by
      have := mul_le_mul_of_nonneg_left hl2b hq0.le; linarith
    have e1 : q * (L + l2 - 7 / 5) ≤ U - 0.7068 * q := by
      have : q * (L + l2 - 7 / 5) = q * L + q * l2 - 1.4 * q := by ring
      rw [hUdef]; linarith
    have e2 : q * (l4 * (2 * s)) ≤ 2.7726 * (q * s) := by
      have h := mul_le_mul_of_nonneg_right hl4 (by positivity : (0 : ℝ) ≤ 2 * (q * s))
      have : q * (l4 * (2 * s)) = l4 * (2 * (q * s)) := by ring
      linarith
    have e3 : s * (11 / 10 * (q * (L + l2 - 7 / 5))) ≤ s * (11 / 10 * (U - 0.7068 * q)) :=
      mul_le_mul_of_nonneg_left (by linarith) hs0
    have e4 : 1.2717 * q ≤ s - 1.1 * U - 1.9951 * q := by linarith
    have e5 : s * (1.2717 * q) ≤ s * (s - 1.1 * U - 1.9951 * q) := mul_le_mul_of_nonneg_left e4 hs0
    have x1 : s * (11 / 10 * (U - 0.7068 * q)) = 1.1 * (s * U) - 0.77748 * (q * s) := by ring
    have x2 : s * (s - 1.1 * U - 1.9951 * q) = s ^ 2 - 1.1 * (s * U) - 1.9951 * (q * s) := by ring
    have x3 : s * (1.2717 * q) = 1.2717 * (q * s) := by ring
    have hqs0 : 0 ≤ q * s := by positivity
    linarith
  -- the other terms
  have hT1 : q * (l4 * (3 * u ^ 4 + 60 * u ^ 3 + K ^ 2 * u)) ≤ q * (4.16 * u ^ 4 + 108.8 * u ^ 3) := by
    apply mul_le_mul_of_nonneg_left _ hq0.le
    have hK2u : K ^ 2 * u ≤ 18.48 * u ^ 3 := by
      have := mul_le_mul_of_nonneg_right hK2 hu0
      have e : 18.48 * u ^ 2 * u = 18.48 * u ^ 3 := by ring
      linarith
    have h0 : 0 ≤ 3 * u ^ 4 + 60 * u ^ 3 + K ^ 2 * u := by positivity
    have h1 := mul_le_mul_of_nonneg_right hl4 h0
    have : 0 ≤ u ^ 4 := by positivity
    linarith
  have hT2 : 3 / 20 * s + 3 * (12 * ℓ) + 3 + ω * (12 * ℓ) ^ 2
      ≤ q * (0.0000046 * u ^ 6 + 0.0003 * u + 0.0001 + 0.00059 * u ^ 3) := by
    have h0 : 0 ≤ 0.0000046 * u ^ 6 + 0.0003 * u + 0.0001 + 0.00059 * u ^ 3 := by positivity
    have h1 := mul_le_mul_of_nonneg_right hq h0
    rw [hsu]; linarith
  have hT3 : (1 + 12 * ℓ) * (11 / 10 * (q * (L + l2 - 7 / 5))) ≤ q * (1.64 * u + 4.88 * u ^ 2) := by
    have h1 : (1 + 12 * ℓ) * (11 / 10 * (q * (L + l2 - 7 / 5)))
        ≤ (1 + 12 * ℓ) * (11 / 10 * (q * (6 * ℓ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have : q * (L + l2 - 7 / 5) ≤ q * (6 * ℓ) := mul_le_mul_of_nonneg_left (by linarith) hq0.le
      linarith
    have h2 : (1 + 12 * ℓ) * (11 / 10 * (q * (6 * ℓ))) = q * (6.6 * ℓ + 79.2 * ℓ ^ 2) := by ring
    have h3 : q * (6.6 * ℓ + 79.2 * ℓ ^ 2) ≤ q * (1.64 * u + 4.88 * u ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hq0.le
    linarith
  have hT4 : (1 + 12 * ℓ) * (11 / 10 * 3280) ≤ q * (0.1102 + 0.328 * u) := by
    have h0 : 0 ≤ 0.1102 + 0.328 * u := by positivity
    have h1 := mul_le_mul_of_nonneg_right hq h0
    linarith
  have hT5 : s * (11 / 10 * 3280) ≤ 0.1102 * (q * s) := by
    have h1 := mul_le_mul_of_nonneg_right hq hs0
    linarith
  have hT6 : q * ((L + 2.52) * (12 * ℓ) + ((12 * ℓ) ^ 2 / 2 + 5 * (12 * ℓ) + 2) + ω * (12 * ℓ) ^ 2)
      ≤ q * (8.88 * u ^ 2 + 22.4 * u + 2 + 19.04 * u ^ 3) := by
    apply mul_le_mul_of_nonneg_left _ hq0.le
    have h1 : (L + 2.52) * (12 * ℓ) ≤ (6 * ℓ + 2.52) * (12 * ℓ) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have e : (6 * ℓ + 2.52) * (12 * ℓ) + ((12 * ℓ) ^ 2 / 2 + 5 * (12 * ℓ) + 2)
        = 144 * ℓ ^ 2 + 90.24 * ℓ + 2 := by ring
    linarith
  have hpoly : 4.16 * u ^ 4 + 108.8 * u ^ 3 + (0.0000046 * u ^ 6 + 0.0003 * u + 0.0001
      + 0.00059 * u ^ 3) + (1.64 * u + 4.88 * u ^ 2) + (0.1102 + 0.328 * u)
      + (8.88 * u ^ 2 + 22.4 * u + 2 + 19.04 * u ^ 3) ≤ 0.3 * s := by
    rw [hsu]; linarith
  have hsum : q * (4.16 * u ^ 4 + 108.8 * u ^ 3) + q * (0.0000046 * u ^ 6 + 0.0003 * u + 0.0001
      + 0.00059 * u ^ 3) + q * (1.64 * u + 4.88 * u ^ 2) + q * (0.1102 + 0.328 * u)
      + q * (8.88 * u ^ 2 + 22.4 * u + 2 + 19.04 * u ^ 3) ≤ 0.3 * (q * s) := by
    have h := mul_le_mul_of_nonneg_left hpoly hq0.le
    have e : q * (4.16 * u ^ 4 + 108.8 * u ^ 3 + (0.0000046 * u ^ 6 + 0.0003 * u + 0.0001
      + 0.00059 * u ^ 3) + (1.64 * u + 4.88 * u ^ 2) + (0.1102 + 0.328 * u)
      + (8.88 * u ^ 2 + 22.4 * u + 2 + 19.04 * u ^ 3)) = q * (4.16 * u ^ 4 + 108.8 * u ^ 3)
      + q * (0.0000046 * u ^ 6 + 0.0003 * u + 0.0001 + 0.00059 * u ^ 3)
      + q * (1.64 * u + 4.88 * u ^ 2) + q * (0.1102 + 0.328 * u)
      + q * (8.88 * u ^ 2 + 22.4 * u + 2 + 19.04 * u ^ 3) := by ring
    have e2 : q * (0.3 * s) = 0.3 * (q * s) := by ring
    linarith
  have hqs : 0 < q * s := by
    have : 0 < s := by rw [hsu]; positivity
    positivity
  have e : q * (l4 * (2 * s + 3 * u ^ 4 + 60 * u ^ 3 + K ^ 2 * u)) + 3 / 20 * s + 3 * (12 * ℓ) + 3
      + ω * (12 * ℓ) ^ 2 + (s + 1 + 12 * ℓ) * (11 / 10 * (q * (L + l2 - 7 / 5) + 3280))
      + q * ((L + 2.52) * (12 * ℓ) + ((12 * ℓ) ^ 2 / 2 + 5 * (12 * ℓ) + 2) + ω * (12 * ℓ) ^ 2)
      = (q * (l4 * (2 * s)) + s * (11 / 10 * (q * (L + l2 - 7 / 5))))
        + q * (l4 * (3 * u ^ 4 + 60 * u ^ 3 + K ^ 2 * u))
        + (3 / 20 * s + 3 * (12 * ℓ) + 3 + ω * (12 * ℓ) ^ 2)
        + (1 + 12 * ℓ) * (11 / 10 * (q * (L + l2 - 7 / 5)))
        + (1 + 12 * ℓ) * (11 / 10 * 3280) + s * (11 / 10 * 3280)
        + q * ((L + 2.52) * (12 * ℓ) + ((12 * ℓ) ^ 2 / 2 + 5 * (12 * ℓ) + 2) + ω * (12 * ℓ) ^ 2) := by
    ring
  rw [e]
  linarith

set_option maxHeartbeats 4000000 in
theorem numericOK2_of_ge (q : ℕ) (hq : 2 ^ 15 ≤ q) : NumericOK2 q := by
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hqR : (32768 : ℝ) ≤ q := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < q := by linarith
  set L := Real.log q with hLdef
  have hL : 15 * 0.6931471803 ≤ L := by
    have : Real.log ((2 : ℝ) ^ 15) ≤ L := Real.log_le_log (by norm_num) (by exact_mod_cast hq)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  set U := (q : ℝ) * L with hUdef
  have hU : 10.397 * (q : ℝ) ≤ U := by
    rw [hUdef]; nlinarith
  have hU0 : (340690 : ℝ) ≤ U := by nlinarith
  set x := xOf 2 q with hxdef
  have hx1 : (x : ℝ) ≤ 2 * U ^ 2 := Nat.floor_le (by positivity)
  have hx2 : 2 * U ^ 2 < x + 1 := Nat.lt_floor_add_one _
  have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg _
  have hxbig : (2.3e11 : ℝ) ≤ x := by nlinarith
  have hxN : 1 ≤ x := by
    have : (0 : ℝ) < x := by linarith
    exact_mod_cast this
  set s := √(x : ℝ) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0
  have hsU : 1.41421 * U ≤ s := by
    by_contra h
    push Not at h
    have : s ^ 2 < (1.41421 * U) ^ 2 := by gcongr
    nlinarith
  have hsq : 14.7 * (q : ℝ) ≤ s := by nlinarith
  have hsge : (481000 : ℝ) ≤ s := by nlinarith
  -- the twelfth root
  set u := (x : ℝ) ^ ((12 : ℝ)⁻¹) with hudef
  have hu0 : 0 ≤ u := Real.rpow_nonneg hx0 _
  have hu12 : u ^ 12 = x := Real.rpow_inv_natCast_pow hx0 (by norm_num)
  have hsu : s = u ^ 6 := by
    rw [hsdef, ← hu12, show u ^ 12 = (u ^ 6) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hu : (8.8 : ℝ) ≤ u := by
    by_contra h
    push Not at h
    have : u ^ 6 < 8.8 ^ 6 := by gcongr
    norm_num at this
    linarith
  have hr2 : (x : ℝ) ^ ((2 : ℝ)⁻¹) = s := by
    rw [hsdef, Real.sqrt_eq_rpow]; norm_num
  have hr3 : (x : ℝ) ^ ((3 : ℝ)⁻¹) = u ^ 4 := by
    rw [← hu12, ← Real.rpow_natCast u 12, ← Real.rpow_mul hu0,
      show ((12 : ℕ) : ℝ) * (3 : ℝ)⁻¹ = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hr4 : (x : ℝ) ^ ((4 : ℝ)⁻¹) = u ^ 3 := by
    rw [← hu12, ← Real.rpow_natCast u 12, ← Real.rpow_mul hu0,
      show ((12 : ℕ) : ℝ) * (4 : ℝ)⁻¹ = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  -- logarithms
  set ℓ := Real.log u with hℓdef
  have hu0' : 0 < u := by linarith
  have hlx : Real.log x = 12 * ℓ := by
    rw [← hu12, Real.log_pow]; push_cast; ring
  have hℓ0 : 0 ≤ ℓ := Real.log_nonneg (by linarith)
  have hℓ : ℓ ≤ 3 * 0.6931471808 - 1 + u / 8 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < u / 8 by positivity)
    rw [Real.log_div hu0'.ne' (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num,
      Real.log_pow] at h
    push_cast at h
    linarith
  have hℓu : ℓ ≤ 0.248 * u := by linarith
  have hlogs : Real.log s = 6 * ℓ := by rw [hsu, Real.log_pow]; push_cast; ring
  have hLℓ : L ≤ 6 * ℓ := by
    rw [← hlogs]; exact Real.log_le_log hq0 (by linarith)
  have hω := card_primeFactors_le_log q (by omega)
  rw [← hLdef] at hω
  have hω' : (q.primeFactors.card : ℝ) ≤ 8.66 * ℓ := by
    have : (q.primeFactors.card : ℝ) * 0.6931471803 ≤ 6 * ℓ := by
      have := mul_le_mul_of_nonneg_left hl2a.le (Nat.cast_nonneg q.primeFactors.card)
      linarith
    nlinarith
  have hω0 : (0 : ℝ) ≤ q.primeFactors.card := Nat.cast_nonneg _
  set K : ℝ := ((Nat.log 2 x : ℕ) : ℝ) with hKdef
  have hK0 : 0 ≤ K := Nat.cast_nonneg _
  have hK : K ≤ 17.32 * ℓ := by
    have h1 : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 (by omega)
    have h2 : ((2 : ℝ) ^ Nat.log 2 x) ≤ x := by exact_mod_cast h1
    have h3 := Real.log_le_log (by positivity) h2
    rw [Real.log_pow, hlx] at h3
    have : K * 0.6931471803 ≤ 12 * ℓ := by
      have := mul_le_mul_of_nonneg_left hl2a.le hK0
      rw [hKdef]; linarith
    nlinarith
  have hl4 : Real.log 4 ≤ 1.3862943616 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  -- assemble
  refine ⟨hxN, ?_⟩
  rw [← hxdef, hr2, hr3, hr4, ← hudef, ← hsdef, ← hKdef, hlx, ← hs2]
  exact numeric_core hqR hUdef hU hsU hsu hu hℓ0 hℓu hK0 hK hω0 hω' hLℓ
    (by linarith) (by linarith) hl40 (by linarith)

end BachSorenson.Two
