import Cramer.Shift.Interval
import Cramer.Shift.Bucket

/-!
# The analytic range `x ≥ 10^8`: a prime in `(x, x + (107/100)√x log x]` under RH

Take `a = ⌊x⌋ + 1`, `h = ⌈(107/200)√x log x⌉ − 1`, `m = a + h`. With `x = t⁶` (`t ≥ 21.5`),
`u = t³ = √x`, `ℓ = log x ∈ [18, 6.48 + 0.75t]`:

* `800h ≤ a + h`;
* `majZ ≤ (4m/h)(SS · ½ log(m/h) + NS · ½ log 2)` with `SS ≤ 0.5336`, `NS ≤ 0.207`
  (`Cramer.Shift.majZ_le`), and `log(m/h) ≤ ℓ/2 − 2`, so
  `h m^{−1/2} majZ ≤ √m (0.5336 ℓ − 1.847)` and `√m ≤ u + ℓ/3`;
* the prime powers cost at most `(ℓ + 0.7)(0.535ℓ + 2 + 1.26 t²)`;

so `IntervalConditionShift maj a h` reduces to
`(ℓ + 0.7)(0.535ℓ + 2 + 1.26t²) + 0.18ℓ² + 3 < 1.847 t³`.
-/

namespace Cramer.Shift

open Real

/-- The final polynomial inequality. -/
lemma poly_final_shift {t ℓ : ℝ} (ht : 21.5 ≤ t) (hℓ1 : 18 ≤ ℓ) (hℓ2 : ℓ ≤ 6.48 + 0.75 * t) :
    (ℓ + 0.7) * (0.535 * ℓ + 2 + 1.26 * t ^ 2) + 0.18 * ℓ ^ 2 + 3 < 1.847 * t ^ 3 := by
  have h1 : (ℓ + 0.7) * (0.535 * ℓ + 2 + 1.26 * t ^ 2)
      ≤ (7.18 + 0.75 * t) * (0.535 * (6.48 + 0.75 * t) + 2 + 1.26 * t ^ 2) :=
    mul_le_mul (by linarith) (by nlinarith) (by positivity) (by positivity)
  have h2 : 0.18 * ℓ ^ 2 ≤ 0.18 * (6.48 + 0.75 * t) ^ 2 := by
    have := pow_le_pow_left₀ (by linarith) hℓ2 2; linarith
  have h3 : 21.5 * t ^ 2 ≤ t ^ 3 := by
    have := mul_le_mul_of_nonneg_left ht (sq_nonneg t)
    nlinarith
  have h4 : 21.5 * t ≤ t ^ 2 := by nlinarith
  nlinarith

/-- `log 7.4 ≥ 2`. -/
lemma two_le_log_seven_four : 2 ≤ Real.log 7.4 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_one_lt_d9
  have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  rw [this]
  have h0 := Real.exp_pos 1
  nlinarith

set_option maxHeartbeats 4000000 in
/-- The numerical core. -/
lemma key_ineq_shift {maj : List (ℕ × ℕ × ℕ)}
    (hb : ∀ c ∈ maj, bucketOK c.2.1 c.2.2 (nb c.2.1 c.2.2) = true)
    (hSS : (SSn maj : ℝ) / (KC * NN) ≤ 0.5336) (hNS : (NSn maj : ℝ) / (KC * NN) ≤ 0.207)
    {t ℓ a h : ℝ} (ht : 21.5 ≤ t) (hℓ : ℓ = Real.log (t ^ 6)) (hℓ1 : 18 ≤ ℓ)
    (hℓ2 : ℓ ≤ 6.48 + 0.75 * t) (ha1 : t ^ 6 < a) (ha2 : a ≤ t ^ 6 + 1)
    (hh1 : 107 / 200 * (t ^ 3 * ℓ) - 1 ≤ h) (hh2 : h ≤ 107 / 200 * (t ^ 3 * ℓ)) :
    800 * h ≤ a + h ∧
    Real.log (a + 2 * h) * ((√(a + 2 * h) - √a + 1) + ((a + 2 * h) ^ ((1 : ℝ) / 3) + 1))
      < h - h * (a + h) ^ (-(1 / 2 : ℝ)) * majZ maj (a + h) h - 3 / h := by
  set u := t ^ 3 with hu
  set b := a + 2 * h with hb'
  set m := a + h with hm'
  have ht0 : 0 < t := by linarith
  have hu1 : 9938 ≤ u := by rw [hu]; nlinarith [sq_nonneg t]
  have hu0 : 0 < u := by linarith
  have hy : t ^ 6 = u ^ 2 := by rw [hu]; ring
  have hℓu : 428 * ℓ ≤ u := by
    rw [hu]; nlinarith [sq_nonneg (t - 21.5), mul_nonneg (sq_nonneg (t - 21.5)) ht0.le]
  have hh0 : 90000 ≤ h := by nlinarith
  have ha0 : 0 < a := by nlinarith
  have h800 : 800 * h ≤ a + h := by nlinarith
  refine ⟨h800, ?_⟩
  have hm0 : 0 < m := by rw [hm']; linarith
  have hh00 : 0 < h := by linarith
  have hε : h / m ≤ 1 / 800 := by rw [div_le_iff₀ hm0, hm']; linarith
  have hsa : u ≤ √a := Real.le_sqrt_of_sq_le (by rw [← hy]; linarith)
  have hsa0 : 0 < √a := by linarith
  have hb2 : b ≤ 2 * u ^ 2 := by nlinarith
  have hbpos : 0 < b := by rw [hb']; linarith
  -- `√b − √a ≤ 0.535 ℓ`
  have hsqrt : √b - √a ≤ 0.535 * ℓ := by
    have h1 : √b ≤ √a + h / √a := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have : (√a + h / √a) ^ 2 = a + 2 * h + h ^ 2 / a := by
        field_simp
        rw [Real.sq_sqrt ha0.le]
        ring
      rw [this, hb']
      have : 0 ≤ h ^ 2 / a := by positivity
      linarith
    have h2 : h / √a ≤ 0.535 * ℓ := by
      rw [div_le_iff₀ hsa0]; nlinarith
    linarith
  have hlogb : Real.log b ≤ ℓ + 0.7 := by
    have : Real.log b ≤ Real.log (2 * u ^ 2) := Real.log_le_log hbpos hb2
    rw [Real.log_mul (by norm_num) (by positivity), ← hy, ← hℓ] at this
    linarith [Real.log_two_lt_d9]
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg (by nlinarith)
  have hcube : b ^ ((1 : ℝ) / 3) ≤ 1.26 * t ^ 2 := by
    have hb3 : b ≤ (1.26 * t ^ 2) ^ (3 : ℕ) := by
      have : 2 * u ^ 2 ≤ (1.26 * t ^ 2) ^ (3 : ℕ) := by rw [hu]; nlinarith [pow_pos ht0 6]
      linarith
    calc b ^ ((1 : ℝ) / 3) ≤ ((1.26 * t ^ 2) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow hbpos.le hb3 (by norm_num)
      _ = 1.26 * t ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  -- `log(m/h) ≤ ℓ/2 − 2`
  have hmh : m / h ≤ u / 7.4 := by
    rw [div_le_div_iff₀ hh00 (by norm_num)]
    have : m ≤ u ^ 2 + 1 + h := by rw [hm', ← hy]; linarith
    have hh9 : 9.63 * u - 1 ≤ h := by nlinarith
    nlinarith
  have hL : Real.log (m / h) ≤ ℓ / 2 - 2 := by
    have h1 := Real.log_le_log (by positivity) hmh
    rw [Real.log_div hu0.ne' (by norm_num)] at h1
    have hlu : Real.log u = ℓ / 2 := by
      have e : Real.log (u ^ 2) = 2 * Real.log u := by rw [Real.log_pow]; push_cast; ring
      rw [hℓ, hy, e]; ring
    linarith [two_le_log_seven_four]
  have hL0 : 0 ≤ Real.log (m / h) := by
    apply Real.log_nonneg; rw [le_div_iff₀ hh00]; linarith
  -- the zero term
  have hZ := majZ_le maj hb hm0 hh00 hε
  have hl2 := Real.log_two_lt_d9
  have hl2' := Real.log_two_gt_d9
  have hSS0 : 0 ≤ (SSn maj : ℝ) / (KC * NN) := by positivity
  have hbr : (SSn maj : ℝ) / (KC * NN) * (1 / 2 * Real.log (m / h))
      + (NSn maj : ℝ) / (KC * NN) * (Real.log 2 / 2) ≤ 0.5336 * (1 / 2 * (ℓ / 2 - 2)) + 0.207 * 0.3466 := by
    have e1 : (SSn maj : ℝ) / (KC * NN) * (1 / 2 * Real.log (m / h)) ≤ 0.5336 * (1 / 2 * (ℓ / 2 - 2)) :=
      mul_le_mul hSS (by linarith) (by positivity) (by norm_num)
    have e2 : (NSn maj : ℝ) / (KC * NN) * (Real.log 2 / 2) ≤ 0.207 * 0.3466 := by
      have hl : Real.log 2 / 2 ≤ 0.3466 := by linarith
      have hl0 : 0 ≤ Real.log 2 / 2 := by linarith
      rcases le_total 0 ((NSn maj : ℝ) / (KC * NN)) with hn | hn
      · exact mul_le_mul hNS hl hl0 (by norm_num)
      · have : (NSn maj : ℝ) / (KC * NN) * (Real.log 2 / 2) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn hl0
        linarith
    linarith
  have hsm : 0 < √m := Real.sqrt_pos.mpr hm0
  have hmrp : h * m ^ (-(1 / 2 : ℝ)) * majZ maj m h ≤ √m * (0.5336 * ℓ - 1.847) := by
    rw [rpow_neg_half hm0]
    have hpos : 0 ≤ h * (1 / √m) := by positivity
    have := mul_le_mul_of_nonneg_left hZ hpos
    have e : h * (1 / √m) * (4 * m / h * ((SSn maj : ℝ) / (KC * NN) * (1 / 2 * Real.log (m / h))
        + (NSn maj : ℝ) / (KC * NN) * (Real.log 2 / 2)))
        = 4 * √m * ((SSn maj : ℝ) / (KC * NN) * (1 / 2 * Real.log (m / h))
        + (NSn maj : ℝ) / (KC * NN) * (Real.log 2 / 2)) := by
      set X := (SSn maj : ℝ) / (KC * NN) * (1 / 2 * Real.log (m / h))
        + (NSn maj : ℝ) / (KC * NN) * (Real.log 2 / 2)
      rw [show h * (1 / √m) * (4 * m / h * X) = 4 * (m / √m) * X by field_simp, Real.div_sqrt]
    rw [e] at this
    refine this.trans ?_
    have := mul_le_mul_of_nonneg_left hbr (by positivity : (0 : ℝ) ≤ 4 * √m)
    nlinarith
  -- `√m ≤ u + ℓ/3`
  have hsmu : √m ≤ u + ℓ / 3 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : m ≤ u ^ 2 + 1 + h := by rw [hm', ← hy]; linarith
    nlinarith
  have hcoef : 0 ≤ 0.5336 * ℓ - 1.847 := by linarith
  have hZ2 : h * m ^ (-(1 / 2 : ℝ)) * majZ maj m h ≤ u * (0.5336 * ℓ - 1.847) + 0.18 * ℓ ^ 2 := by
    have := mul_le_mul_of_nonneg_right hsmu hcoef
    nlinarith
  have h3h : 3 / h ≤ 1 := by rw [div_le_one hh00]; linarith
  have hLHS : Real.log b * ((√b - √a + 1) + (b ^ ((1 : ℝ) / 3) + 1))
      ≤ (ℓ + 0.7) * (0.535 * ℓ + 2 + 1.26 * t ^ 2) := by
    have h1 : (√b - √a + 1) + (b ^ ((1 : ℝ) / 3) + 1) ≤ 0.535 * ℓ + 2 + 1.26 * t ^ 2 := by linarith
    have h0 : 0 ≤ (√b - √a + 1) + (b ^ ((1 : ℝ) / 3) + 1) := by
      have : √a ≤ √b := Real.sqrt_le_sqrt (by rw [hb']; linarith)
      have : 0 ≤ b ^ ((1 : ℝ) / 3) := by positivity
      linarith
    exact (mul_le_mul_of_nonneg_left h1 hlogb0).trans
      (mul_le_mul_of_nonneg_right hlogb (by positivity))
  have hfinal := poly_final_shift ht hℓ1 hℓ2
  rw [← hu] at hfinal
  have : 107 / 200 * (u * ℓ) - 1 ≤ h := by rw [hu]; exact hh1
  nlinarith

/-- **Under RH, with a good majorant, every `(x, x + (107/100)√x log x]` with `x ≥ 10^8`
contains a prime.** -/
theorem exists_prime_of_RH_large_shift (hRH : RiemannHypothesis) {maj : List (ℕ × ℕ × ℕ)}
    (hgood : ∀ y : ℝ, 0 ≤ y → CellGood maj y)
    (hb : ∀ c ∈ maj, bucketOK c.2.1 c.2.2 (nb c.2.1 c.2.2) = true)
    (hSS : (SSn maj : ℝ) / (KC * NN) ≤ 0.5336) (hNS : (NSn maj : ℝ) / (KC * NN) ≤ 0.207)
    {x : ℝ} (hx : 10 ^ 8 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + 107 / 100 * √x * Real.log x := by
  have hσ : ∀ c ∈ maj, 1000 ≤ c.2.1 := by
    intro c hc
    have := hb c hc
    unfold bucketOK at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    omega
  have hx0 : 0 < x := by linarith
  set t := x ^ ((1 : ℝ) / 6) with ht
  have ht6 : t ^ 6 = x := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have ht20 : 21.5 ≤ t := by
    have : (21.5 : ℝ) = ((21.5 : ℝ) ^ 6) ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [this, ht]
    exact Real.rpow_le_rpow (by norm_num) (by norm_num; linarith) (by norm_num)
  have ht0 : 0 < t := by linarith
  have hsx : √x = t ^ 3 := by
    rw [← ht6, show t ^ 6 = (t ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  set ℓ := Real.log x with hℓdef
  have hℓ : ℓ = Real.log (t ^ 6) := by rw [ht6]
  have hℓ1 : 18 ≤ ℓ := by
    have : Real.log ((2 : ℝ) ^ 26) ≤ ℓ := Real.log_le_log (by norm_num) (by norm_num; linarith)
    rw [Real.log_pow] at this
    push_cast at this
    linarith [Real.log_two_gt_d9]
  have hℓ2 : ℓ ≤ 6.48 + 0.75 * t := by
    have h1 : Real.log (t / 8) ≤ t / 8 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div ht0.ne' (by norm_num)] at h1
    have e : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have e2 : ℓ = 6 * Real.log t := by rw [hℓ, Real.log_pow]; norm_num
    linarith [Real.log_two_lt_d9]
  set a : ℕ := ⌊x⌋₊ + 1 with ha
  have ha1 : x < (a : ℝ) := by rw [ha]; push_cast; exact Nat.lt_floor_add_one x
  have ha2 : (a : ℝ) ≤ x + 1 := by rw [ha]; push_cast; linarith [Nat.floor_le hx0.le]
  set v := 107 / 200 * (√x * ℓ) with hv
  have hv0 : 90000 ≤ v := by
    rw [hv, hsx]
    have : 9938 ≤ t ^ 3 := by nlinarith [sq_nonneg t]
    nlinarith
  set h : ℕ := ⌈v⌉₊ - 1 with hh
  have hc1 : v ≤ (⌈v⌉₊ : ℝ) := Nat.le_ceil v
  have hc2 : (⌈v⌉₊ : ℝ) < v + 1 := Nat.ceil_lt_add_one (by linarith)
  have hc0 : 1 ≤ ⌈v⌉₊ := by
    have : (1 : ℝ) ≤ ⌈v⌉₊ := by linarith
    exact_mod_cast this
  have hhR : (h : ℝ) = (⌈v⌉₊ : ℝ) - 1 := by rw [hh, Nat.cast_sub hc0]; push_cast; ring
  have hh1 : v - 1 ≤ (h : ℝ) := by linarith
  have hh2 : (h : ℝ) < v := by linarith
  have hh1' : 1 ≤ h := by
    have : (1 : ℝ) ≤ h := by linarith
    exact_mod_cast this
  have hC : IntervalConditionShift maj a h := by
    unfold IntervalConditionShift
    obtain ⟨k1, k2⟩ := key_ineq_shift (a := (a : ℝ)) (h := (h : ℝ)) hb hSS hNS ht20 hℓ hℓ1 hℓ2
      (by rw [ht6]; exact ha1) (by rw [ht6]; exact ha2) (by rw [← hsx]; exact hh1)
      (by rw [← hsx]; exact hh2.le)
    exact ⟨by exact_mod_cast k1, k2⟩
  obtain ⟨p, hp, hap, hpb⟩ := exists_prime_Ico_shift hRH hgood hσ hh1' hC
  refine ⟨p, hp, lt_of_lt_of_le ha1 (by exact_mod_cast hap), ?_⟩
  have : (p : ℝ) + 1 ≤ a + 2 * h := by exact_mod_cast hpb
  have e : 107 / 100 * √x * Real.log x = 2 * v := by rw [hv]; ring
  rw [e]
  linarith

end Cramer.Shift
