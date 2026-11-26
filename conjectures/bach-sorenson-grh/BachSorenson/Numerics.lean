import BachSorenson.Large

/-!
# Step 6: the numerical inequality for `q ≥ 2^15`, with `c = 7/2`

Write `L = log q ≥ 15 log 2 = L₀`, `U = q L ≥ 2^15 L₀`, `x = ⌊(7/2) U²⌋`, `s = √x`,
`y = x^{1/3}`, `t = x^{1/4}` (so `s = t²`, `x = y³`). Then
* `s ≥ 637000`, `1.8708 U < s + 1`, `q ≤ (s + 1)/19.45`, `L + 5/3 ≤ 1.1604 L`;
* `86 y ≤ s` (as `x ≥ 86^6`) and `t ≥ 790`;
* `log x = 4 log t ≤ 4 (9 log 2 − 1) + t/128` (tangent of `log` at `512`), so
  `t log x ≤ 0.03434 s` and `log x ≤ 20.96 + s/101120`;
* `ppBound x ≤ log 4 · 1.0613 s`.
Substituting, the claim becomes a quadratic inequality in `s` (`quadratic_bound`) whose leading
coefficient is `0.4892 < 1/2`.
-/

namespace BachSorenson

open Real

/-- The analytic argument covers `q ≥ Q₀ = 2^13`. -/
abbrev Q₀ : ℕ := 2 ^ 15

lemma card_primeFactors_le_self (q : ℕ) : (q.primeFactors.card : ℝ) ≤ q := by
  have : q.primeFactors ⊆ Finset.Icc 1 q := fun p hp => by
    have h := Nat.mem_primeFactors.1 hp
    exact Finset.mem_Icc.2 ⟨h.1.one_lt.le, Nat.le_of_dvd (Nat.pos_of_ne_zero h.2.2) h.2.1⟩
  have := Finset.card_le_card this
  simp only [Nat.card_Icc, add_tsub_cancel_right] at this
  exact_mod_cast this

lemma quadratic_bound (s : ℝ) (hs : 637000 ≤ s) :
    (2 / 3) * (s + 3) * (1.1604 * ((s + 1) / 1.8708)) + (s + 1) / 19.45 * (1.3862943616 * (1.0613 * s))
      + 2 * ((s + 1) / 19.45) * (20.96 + s / 101120 + 1.6) + s / 20 + 3 < s ^ 2 / 2 := by
  have h := mul_nonneg (by linarith : (0:ℝ) ≤ s) (by linarith : (0:ℝ) ≤ s - 637000)
  norm_num at h ⊢
  nlinarith [h]

set_option maxHeartbeats 1000000 in
theorem numericOK_of_ge (q : ℕ) (hq : Q₀ ≤ q) : NumericOK (7 / 2) q := by
  have hl2a := Real.log_two_gt_d9
  have hl2b := Real.log_two_lt_d9
  have hqR : (32768 : ℝ) ≤ q := by exact_mod_cast hq
  set L := Real.log q with hLdef
  have hL : 15 * 0.6931471803 ≤ L := by
    have : Real.log ((2 : ℝ) ^ 15) ≤ L := Real.log_le_log (by norm_num) (by exact_mod_cast hq)
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  set U := (q : ℝ) * L with hUdef
  have hU : 32768 * (15 * 0.6931471803) ≤ U := by
    rw [hUdef]; exact mul_le_mul hqR hL (by norm_num) (by positivity)
  set x := xOf (7 / 2) q with hxdef
  have hx1 : (x : ℝ) ≤ 7 / 2 * U ^ 2 := Nat.floor_le (by positivity)
  have hx2 : 7 / 2 * U ^ 2 < x + 1 := Nat.lt_floor_add_one _
  have hxbig : (4.0625e11 : ℝ) ≤ x := by
    have : (32768 * (15 * 0.6931471803) : ℝ) ^ 2 ≤ U ^ 2 := by gcongr
    norm_num at this
    linarith
  have hx144 : 144 ≤ x := by
    have : (143 : ℝ) < x := by linarith
    exact_mod_cast this
  have hx0 : (0 : ℝ) ≤ x := by positivity
  set s := √(x : ℝ) with hsdef
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = x := Real.sq_sqrt hx0
  have hsge : (637000 : ℝ) ≤ s := by
    by_contra h
    push Not at h
    have : s ^ 2 < 637000 ^ 2 := by gcongr
    norm_num at this
    linarith
  have hUs : 1.8708 * U < s + 1 := by
    by_contra h
    push Not at h
    have : (s + 1) ^ 2 ≤ (1.8708 * U) ^ 2 := by gcongr
    nlinarith
  have hU0 : 0 ≤ U := by linarith
  -- `q ≤ U / L₀`
  have hqU : (q : ℝ) * (15 * 0.6931471803) ≤ U := by
    rw [hUdef]; exact mul_le_mul_of_nonneg_left hL (by positivity)
  -- cube root
  set y := (x : ℝ) ^ ((1 : ℝ) / 3) with hydef
  have hy0 : 0 ≤ y := rpow_nonneg hx0 _
  have hy3 : y ^ 3 = x := by
    rw [hydef, one_div]; exact rpow_inv_natCast_pow hx0 (by norm_num)
  have hyge : (7396 : ℝ) ≤ y := by
    by_contra h
    push Not at h
    have : y ^ 3 < 7396 ^ 3 := by gcongr
    norm_num at this
    linarith
  have hy52 : 86 * y ≤ s := by
    rw [hsdef]
    refine (Real.le_sqrt (by positivity) hx0).2 ?_
    rw [← hy3]
    have : 0 ≤ y ^ 2 * (y - 7396) := mul_nonneg (sq_nonneg y) (by linarith)
    nlinarith
  -- fourth root
  set t := (x : ℝ) ^ ((1 : ℝ) / 4) with htdef
  have ht0 : 0 ≤ t := rpow_nonneg hx0 _
  have ht4 : t ^ 4 = x := by
    rw [htdef, one_div]; exact rpow_inv_natCast_pow hx0 (by norm_num)
  have hst : s = t ^ 2 := by
    rw [hsdef, ← ht4, show t ^ 4 = (t ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have htge : (790 : ℝ) ≤ t := by
    by_contra h
    push Not at h
    have : t ^ 4 < 790 ^ 4 := by gcongr
    norm_num at this
    linarith
  have ht0' : 0 < t := by linarith
  have hlogx : Real.log x = 4 * Real.log t := by
    rw [← ht4, Real.log_pow]; norm_num
  have hlogt : Real.log t ≤ 9 * 0.6931471808 - 1 + t / 512 := by
    have h := Real.log_le_sub_one_of_pos (show 0 < t / 512 by positivity)
    rw [Real.log_div ht0'.ne' (by norm_num), show (512 : ℝ) = 2 ^ 9 by norm_num,
      Real.log_pow] at h
    push_cast at h
    linarith
  have hts : 790 * t ≤ s := by rw [hst]; nlinarith
  have hlx : Real.log x ≤ 20.96 + s / 101120 := by
    rw [hlogx]; linarith
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have htlx : t * Real.log x ≤ 0.03434 * s := by
    rw [hlogx]
    have : t * (4 * Real.log t) ≤ t * (4 * (9 * 0.6931471808 - 1 + t / 512)) := by
      apply mul_le_mul_of_nonneg_left _ ht0; linarith
    have e : t * (4 * (9 * 0.6931471808 - 1 + t / 512))
        = 4 * (9 * 0.6931471808 - 1) * t + t ^ 2 / 128 := by ring
    rw [e, ← hst] at this
    linarith
  have htlx2 : t * (Real.log x / Real.log 2) ≤ 0.0496 * s := by
    rw [← mul_div_assoc, div_le_iff₀ (by linarith)]
    have : 0.0496 * s * 0.6931471803 ≤ 0.0496 * s * Real.log 2 :=
      mul_le_mul_of_nonneg_left hl2a.le (by positivity)
    linarith
  -- the three pieces
  have hl4 : Real.log 4 ≤ 1.3862943616 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hl40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hpp : ppBound x ≤ 1.3862943616 * (1.0613 * s) := by
    unfold ppBound
    rw [← hsdef, ← hydef, ← htdef]
    have : s + y + t * (Real.log x / Real.log 2) ≤ 1.0613 * s := by linarith
    have h0 : 0 ≤ s + y + t * (Real.log x / Real.log 2) := by
      have : 0 ≤ Real.log x / Real.log 2 := div_nonneg hlx0 (by linarith)
      positivity
    calc Real.log 4 * (s + y + t * (Real.log x / Real.log 2))
        ≤ 1.3862943616 * (s + y + t * (Real.log x / Real.log 2)) :=
          mul_le_mul_of_nonneg_right hl4 h0
      _ ≤ _ := by gcongr
  have hω := card_primeFactors_le_self q
  have hx3 : 3 / (x : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hx30 : 0 ≤ 3 / (x : ℝ) := by positivity
  have hqLc : (q : ℝ) * (L + 5 / 3) ≤ 1.1604 * U := by
    rw [hUdef]
    have : (q : ℝ) * (5 / 3) ≤ q * (0.1604 * L) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hA : (q : ℝ) * ((s + 2 + 3 / x) * ((2 / 3) * (L + 5 / 3)))
      ≤ (2 / 3) * (s + 3) * (1.1604 * U) := by
    have e : (q : ℝ) * ((s + 2 + 3 / x) * ((2 / 3) * (L + 5 / 3)))
        = (2 / 3) * (s + 2 + 3 / x) * ((q : ℝ) * (L + 5 / 3)) := by ring
    rw [e]
    have hLq : 0 ≤ (q : ℝ) * (L + 5 / 3) := by
      have : 0 ≤ L := by linarith
      positivity
    apply mul_le_mul (by linarith) hqLc hLq (by positivity)
  have hP : (q : ℝ) * ppBound x ≤ q * (1.3862943616 * (1.0613 * s)) :=
    mul_le_mul_of_nonneg_left hpp hq0
  refine ⟨hx144, ?_⟩
  unfold charBound
  rw [← hxdef, ← hsdef, ← hLdef]
  -- everything in terms of `s`, `U` and `q`
  have hlin : (q : ℝ) * (Real.log x + 1 + 0.6) + q.primeFactors.card * Real.log x
      ≤ 2 * q * (20.96 + s / 101120 + 1.6) := by
    have h1 : (q.primeFactors.card : ℝ) * Real.log x ≤ q * Real.log x :=
      mul_le_mul_of_nonneg_right hω hlx0
    have h2 : (q : ℝ) * Real.log x ≤ q * (20.96 + s / 101120) :=
      mul_le_mul_of_nonneg_left hlx hq0
    linarith
  have hqs : (q : ℝ) ≤ (s + 1) / 19.45 := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  have hfinal : (2 / 3) * (s + 3) * (1.1604 * U) + q * (1.3862943616 * (1.0613 * s))
      + 2 * q * (20.96 + s / 101120 + 1.6) + s / 20 + 3 < s ^ 2 / 2 := by
    have h1 : (2 / 3) * (s + 3) * (1.1604 * U) ≤ (2 / 3) * (s + 3) * (1.1604 * ((s + 1) / 1.8708)) :=
      mul_le_mul_of_nonneg_left (by
        have : U ≤ (s + 1) / 1.8708 := by rw [le_div_iff₀ (by norm_num)]; linarith
        linarith) (by positivity)
    have h2 : (q : ℝ) * (1.3862943616 * (1.0613 * s))
        ≤ (s + 1) / 19.45 * (1.3862943616 * (1.0613 * s)) :=
      mul_le_mul_of_nonneg_right hqs (by positivity)
    have h3 : 2 * (q : ℝ) * (20.96 + s / 101120 + 1.6)
        ≤ 2 * ((s + 1) / 19.45) * (20.96 + s / 101120 + 1.6) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h4 := quadratic_bound s hsge
    linarith only [h1, h2, h3, h4]
  have e : (q : ℝ) * ((s + 2 + 3 / x) * ((2 / 3) * (L + 5 / 3)) + (Real.log x + 1) + 0.6
      + ppBound x) = q * ((s + 2 + 3 / x) * ((2 / 3) * (L + 5 / 3)))
      + q * (Real.log x + 1 + 0.6) + q * ppBound x := by ring
  rw [e]
  rw [hs2] at hfinal
  linarith only [hfinal, hA, hP, hlin]

end BachSorenson
