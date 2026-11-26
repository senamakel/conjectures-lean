import Cramer.Interval

/-!
# The analytic range `x ≥ 10^6`: a prime in `(x, x + 2√x log x]` under RH

Take `a = ⌊x⌋ + 1` and `h = ⌈√x log x⌉ − 1`. Writing `x = t⁶` (`t ≥ 10`), `u = t³ = √x` and
`ℓ = log x ∈ [13, 6.48 + 0.75 t]`, every term of `IntervalCondition a h` is bounded by a
polynomial in `t` and `ℓ`:

* `√b − √a ≤ ℓ`, `b ≤ 2t⁶`, `log b ≤ ℓ + 0.7`, `b^{1/3} ≤ 1.26 t²`;
* `L(1/2 + 2b/h) + 1/40 ≤ ℓ/4 − 1.46` and `4b/√a ≤ 4u + 4/u + 8ℓ`;

so the condition reduces to `(ℓ + 0.7)(ℓ + 2 + 1.26t²) + 2ℓ² + 2 < 5.84 t³`, true for `t ≥ 10`.
-/

namespace Cramer

open Real

lemma log_two_bounds : 0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808 :=
  ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩

/-- The final polynomial inequality. -/
lemma poly_final {t ℓ : ℝ} (ht : 10 ≤ t) (hℓ1 : 13 ≤ ℓ) (hℓ2 : ℓ ≤ 6.48 + 0.75 * t) :
    (ℓ + 0.7) * (ℓ + 2 + 1.26 * t ^ 2) + 2 * ℓ ^ 2 + 3 < 5.84 * t ^ 3 := by
  have ht0 : 0 ≤ t := by linarith
  have h1 : (ℓ + 0.7) * (ℓ + 2 + 1.26 * t ^ 2)
      ≤ (7.18 + 0.75 * t) * (8.48 + 0.75 * t + 1.26 * t ^ 2) :=
    mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  have h2 : ℓ ^ 2 ≤ (6.48 + 0.75 * t) ^ 2 := pow_le_pow_left₀ (by linarith) hℓ2 2
  have h3 : 10 * t ^ 2 ≤ t ^ 3 := by
    have := mul_le_mul_of_nonneg_left ht (sq_nonneg t)
    calc 10 * t ^ 2 = t ^ 2 * 10 := by ring
      _ ≤ t ^ 2 * t := this
      _ = t ^ 3 := by ring
  have h4 : 10 * t ≤ t ^ 2 := by nlinarith
  nlinarith

set_option maxHeartbeats 1000000 in
/-- The polynomial core of the numerical condition. -/
lemma key_ineq {t ℓ a h : ℝ} (ht : 10 ≤ t) (hℓ : ℓ = Real.log (t ^ 6)) (hℓ1 : 13 ≤ ℓ)
    (hℓ2 : ℓ ≤ 6.48 + 0.75 * t) (ha1 : t ^ 6 < a) (ha2 : a ≤ t ^ 6 + 1)
    (hh1 : t ^ 3 * ℓ - 1 ≤ h) (hh2 : h ≤ t ^ 3 * ℓ) :
    Real.log (a + 2 * h) * ((√(a + 2 * h) - √a + 1) + ((a + 2 * h) ^ ((1 : ℝ) / 3) + 1))
      < h - 4 * (a + 2 * h) / √a * (Lup (1 / 2 + 2 * (a + 2 * h) / h) + 1 / 40) - 3 / h := by
  set u := t ^ 3 with hu
  set b := a + 2 * h with hb
  have ht0 : 0 < t := by linarith
  have hu1 : 1000 ≤ u := by rw [hu]; nlinarith [sq_nonneg t]
  have hu0 : 0 < u := by linarith
  have hy : t ^ 6 = u ^ 2 := by rw [hu]; ring
  have hℓu : ℓ ≤ u / 50 := by
    rw [hu]; nlinarith [sq_nonneg (t - 10), mul_nonneg (sq_nonneg (t - 10)) ht0.le]
  have hh0 : 12000 ≤ h := by nlinarith
  have ha0 : 0 < a := by nlinarith
  have hsa : u ≤ √a := Real.le_sqrt_of_sq_le (by rw [← hy]; linarith)
  have hsa0 : 0 < √a := by linarith
  have hb1 : b ≤ u ^ 2 + 1 + 2 * u * ℓ := by rw [hb]; nlinarith
  have hb2 : b ≤ 2 * u ^ 2 := by nlinarith
  have hbpos : 0 < b := by rw [hb]; linarith
  -- (ii) `√b − √a ≤ ℓ`
  have hsqrt : √b - √a ≤ ℓ := by
    have h1 : √b ≤ √a + h / √a := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have : (√a + h / √a) ^ 2 = a + 2 * h + h ^ 2 / a := by
        field_simp
        rw [Real.sq_sqrt ha0.le]
        ring
      rw [this, hb]
      have : 0 ≤ h ^ 2 / a := by positivity
      linarith
    have h2 : h / √a ≤ ℓ := by
      rw [div_le_iff₀ hsa0]; nlinarith
    linarith
  -- (iii) `log b ≤ ℓ + 0.7`
  have hlogb : Real.log b ≤ ℓ + 0.7 := by
    have : Real.log b ≤ Real.log (2 * u ^ 2) := Real.log_le_log hbpos hb2
    rw [Real.log_mul (by norm_num) (by positivity), ← hy, ← hℓ] at this
    linarith [log_two_bounds.2]
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg (by nlinarith)
  -- (iv) `b^{1/3} ≤ 1.26 t²`
  have hcube : b ^ ((1 : ℝ) / 3) ≤ 1.26 * t ^ 2 := by
    have hb3 : b ≤ (1.26 * t ^ 2) ^ (3 : ℕ) := by
      have : 2 * u ^ 2 ≤ (1.26 * t ^ 2) ^ (3 : ℕ) := by rw [hu]; nlinarith [pow_pos ht0 6]
      linarith
    calc b ^ ((1 : ℝ) / 3) ≤ ((1.26 * t ^ 2) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow hbpos.le hb3 (by norm_num)
      _ = 1.26 * t ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  -- (v) the `L` bound
  set s := 1 / 2 + 2 * b / h with hs
  have hbh : 2 * u / ℓ ≤ 2 * b / h := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hs100 : 99 ≤ s - 1 := by
    have : 100 ≤ 2 * u / ℓ := by rw [le_div_iff₀ (by linarith)]; linarith
    rw [hs]; linarith
  have hfrac : 1 / s + 1 / (s - 1) ≤ 0.021 := by
    have h1 : 1 / s ≤ 1 / 99 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : 1 / (s - 1) ≤ 1 / 99 := one_div_le_one_div_of_le (by norm_num) hs100
    linarith
  have hs2 : s / 2 ≤ u / ℓ + 3 := by
    have : b / h ≤ u / ℓ + 2.75 := by
      rw [div_le_iff₀ (by linarith)]
      have e : (u / ℓ + 2.75) * h ≥ (u / ℓ + 2.75) * (u * ℓ - 1) :=
        mul_le_mul_of_nonneg_left (by rw [hu]; linarith) (by positivity)
      have e2 : (u / ℓ + 2.75) * (u * ℓ - 1) = u ^ 2 + 2.75 * u * ℓ - u / ℓ - 2.75 := by
        field_simp; ring
      have e3 : u / ℓ ≤ u := by rw [div_le_iff₀ (by linarith)]; nlinarith
      nlinarith
    rw [hs]
    have : 2 * b / h / 2 = b / h := by ring
    linarith [show (1 / 2 + 2 * b / h) / 2 = 1 / 4 + b / h by ring]
  have hlogs : Real.log (s / 2) ≤ ℓ / 2 - Real.log ℓ + 3 * ℓ / u := by
    have hpos : 0 < s / 2 := by linarith
    have h1 : Real.log (s / 2) ≤ Real.log (u / ℓ + 3) := Real.log_le_log hpos hs2
    have h2 : Real.log (u / ℓ + 3) = Real.log (u / ℓ) + Real.log (1 + 3 * ℓ / u) := by
      rw [← Real.log_mul (by positivity) (by positivity)]
      congr 1
      field_simp
    have h3 : Real.log (1 + 3 * ℓ / u) ≤ 3 * ℓ / u := by
      have := Real.log_le_sub_one_of_pos (show 0 < 1 + 3 * ℓ / u by positivity)
      linarith
    have h4 : Real.log (u / ℓ) = ℓ / 2 - Real.log ℓ := by
      rw [Real.log_div (by positivity) (by positivity)]
      have : Real.log u = ℓ / 2 := by
        have e : Real.log (u ^ 2) = 2 * Real.log u := by rw [Real.log_pow]; push_cast; ring
        rw [hℓ, hy, e]; ring
      rw [this]
    linarith
  have hlogℓ : 2.0794 ≤ Real.log ℓ := by
    have : Real.log 8 ≤ Real.log ℓ := Real.log_le_log (by norm_num) (by linarith)
    have e : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    linarith [log_two_bounds.1]
  have hlogπ : 1 ≤ Real.log Real.pi := by
    rw [Real.le_log_iff_exp_le Real.pi_pos]
    linarith [Real.exp_one_lt_d9, Real.pi_gt_three]
  have hℓu' : 3 * ℓ / u ≤ 0.06 := by rw [div_le_iff₀ hu0]; linarith
  have hL : Lup s + 1 / 40 ≤ ℓ / 4 - 1.46 := by
    unfold Lup
    linarith
  -- (vi) the weight
  have hW : 4 * b / √a ≤ 4 * u + 4 / u + 8 * ℓ := by
    rw [div_le_iff₀ hsa0]
    have e : (4 * u + 4 / u + 8 * ℓ) * √a ≥ (4 * u + 4 / u + 8 * ℓ) * u :=
      mul_le_mul_of_nonneg_left hsa (by positivity)
    have e2 : (4 * u + 4 / u + 8 * ℓ) * u = 4 * u ^ 2 + 4 + 8 * u * ℓ := by field_simp
    linarith
  have hW0 : 0 ≤ 4 * b / √a := by positivity
  have hLpos : 0 ≤ ℓ / 4 - 1.46 := by linarith
  have hWL : 4 * b / √a * (Lup s + 1 / 40) ≤ (4 * u + 4 / u + 8 * ℓ) * (ℓ / 4 - 1.46) :=
    (mul_le_mul_of_nonneg_left hL hW0).trans (mul_le_mul_of_nonneg_right hW hLpos)
  have hWL' : (4 * u + 4 / u + 8 * ℓ) * (ℓ / 4 - 1.46) ≤ u * ℓ - 5.84 * u + 2 * ℓ ^ 2 + 1 := by
    have e : (4 / u) * (ℓ / 4 - 1.46) ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hu0]; linarith
    have expand : (4 * u + 4 / u + 8 * ℓ) * (ℓ / 4 - 1.46)
        = u * ℓ - 5.84 * u + (4 / u) * (ℓ / 4 - 1.46) + 2 * ℓ ^ 2 - 11.68 * ℓ := by ring
    rw [expand]; linarith
  have h3h : 3 / h ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  -- (vii) left side
  have hLHS : Real.log b * ((√b - √a + 1) + (b ^ ((1 : ℝ) / 3) + 1))
      ≤ (ℓ + 0.7) * (ℓ + 2 + 1.26 * t ^ 2) := by
    have h1 : (√b - √a + 1) + (b ^ ((1 : ℝ) / 3) + 1) ≤ ℓ + 2 + 1.26 * t ^ 2 := by linarith
    have h0 : 0 ≤ (√b - √a + 1) + (b ^ ((1 : ℝ) / 3) + 1) := by
      have : √a ≤ √b := Real.sqrt_le_sqrt (by rw [hb]; linarith)
      have : 0 ≤ b ^ ((1 : ℝ) / 3) := by positivity
      linarith
    exact (mul_le_mul_of_nonneg_left h1 hlogb0).trans
      (mul_le_mul_of_nonneg_right hlogb (by positivity))
  have hfinal := poly_final ht hℓ1 hℓ2
  rw [← hu] at hfinal
  linarith

/-- **Under RH, every `(x, x + 2√x log x]` with `x ≥ 10^6` contains a prime.** -/
theorem exists_prime_of_RH_large (hRH : RiemannHypothesis) {x : ℝ} (hx : 10 ^ 6 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + 2 * √x * Real.log x := by
  have hx0 : 0 < x := by linarith
  set t := x ^ ((1 : ℝ) / 6) with ht
  have ht6 : t ^ 6 = x := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have ht10 : 10 ≤ t := by
    have : (10 : ℝ) = ((10 : ℝ) ^ 6) ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [this, ht]
    exact Real.rpow_le_rpow (by norm_num) hx (by norm_num)
  have ht0 : 0 < t := by linarith
  have hsx : √x = t ^ 3 := by
    rw [← ht6, show t ^ 6 = (t ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  set ℓ := Real.log x with hℓdef
  have hℓ : ℓ = Real.log (t ^ 6) := by rw [ht6]
  have hℓ1 : 13 ≤ ℓ := by
    have : Real.log ((2 : ℝ) ^ 19) ≤ ℓ := Real.log_le_log (by norm_num) (by linarith)
    rw [Real.log_pow] at this
    push_cast at this
    linarith [log_two_bounds.1]
  have hℓ2 : ℓ ≤ 6.48 + 0.75 * t := by
    have h1 : Real.log (t / 8) ≤ t / 8 - 1 := Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div ht0.ne' (by norm_num)] at h1
    have e : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    have e2 : ℓ = 6 * Real.log t := by rw [hℓ, Real.log_pow]; norm_num
    linarith [log_two_bounds.2]
  set a : ℕ := ⌊x⌋₊ + 1 with ha
  have ha1 : x < (a : ℝ) := by rw [ha]; push_cast; exact Nat.lt_floor_add_one x
  have ha2 : (a : ℝ) ≤ x + 1 := by rw [ha]; push_cast; linarith [Nat.floor_le hx0.le]
  set v := √x * ℓ with hv
  have hv0 : 13000 ≤ v := by
    rw [hv, hsx]
    have : 1000 ≤ t ^ 3 := by nlinarith [sq_nonneg t]
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
  have h2v : 2 * v ≤ x := by
    rw [hv, hsx, ← ht6]
    have : ℓ ≤ t ^ 3 / 2 := by nlinarith [sq_nonneg t]
    nlinarith [pow_pos ht0 3]
  have h2a : 2 * h ≤ a := by
    have : ((2 * h : ℕ) : ℝ) < a := by push_cast; linarith
    exact_mod_cast this.le
  have hC : IntervalCondition a h := by
    unfold IntervalCondition
    refine key_ineq ht10 hℓ hℓ1 hℓ2 (by rw [ht6]; exact ha1) (by rw [ht6]; exact ha2)
      (by rw [← hsx]; exact hh1) (by rw [← hsx]; exact hh2.le)
  obtain ⟨p, hp, hap, hpb⟩ := exists_prime_Ico_of_RH hRH hh1' h2a hC
  refine ⟨p, hp, lt_of_lt_of_le ha1 (by exact_mod_cast hap), ?_⟩
  have : (p : ℝ) + 1 ≤ a + 2 * h := by exact_mod_cast hpb
  have e : 2 * √x * Real.log x = 2 * v := by rw [hv]; ring
  rw [e]
  linarith

end Cramer
