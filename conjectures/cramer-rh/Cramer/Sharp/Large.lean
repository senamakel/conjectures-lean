import Cramer.Sharp.Interval
import Cramer.Large

/-!
# The analytic range `x ≥ 6.4·10^7`: a prime in `(x, x + (3/2)√x log x]` under RH

Take `a = ⌊x⌋ + 1` and `h = ⌈(3/4)√x log x⌉ − 1`. Writing `x = t⁶` (`t ≥ 20`), `u = t³ = √x`,
`ℓ = log x ∈ [16, 6.48 + 0.75 t]`:

* `400 h ≤ a`, since `300 ℓ ≤ t³`;
* `√b − √a ≤ (3/4)ℓ`, `log b ≤ ℓ + 0.7`, `b^{1/3} ≤ 1.26 t²`;
* `L(1/2 + 7a/(3h)) + 1/40 ≤ ℓ/4 − 1.6` and `3√a ≤ 3u + 3/u`;

so `IntervalCondition32 a h` reduces to `(ℓ + 0.7)(0.75ℓ + 2 + 1.26t²) + 3 < 4.8 t³`.
-/

namespace Cramer

open Real

/-- The final polynomial inequality. -/
lemma poly_final_32 {t ℓ : ℝ} (ht : 20 ≤ t) (hℓ1 : 16 ≤ ℓ) (hℓ2 : ℓ ≤ 6.48 + 0.75 * t) :
    (ℓ + 0.7) * (0.75 * ℓ + 2 + 1.26 * t ^ 2) + 3 < 4.8 * t ^ 3 := by
  have h1 : (ℓ + 0.7) * (0.75 * ℓ + 2 + 1.26 * t ^ 2)
      ≤ (7.18 + 0.75 * t) * (0.75 * (6.48 + 0.75 * t) + 2 + 1.26 * t ^ 2) :=
    mul_le_mul (by linarith) (by nlinarith) (by positivity) (by positivity)
  have h3 : 20 * t ^ 2 ≤ t ^ 3 := by
    have := mul_le_mul_of_nonneg_left ht (sq_nonneg t)
    nlinarith
  have h4 : 20 * t ≤ t ^ 2 := by nlinarith
  nlinarith

set_option maxHeartbeats 2000000 in
/-- The numerical core. -/
lemma key_ineq_32 {t ℓ a h : ℝ} (ht : 20 ≤ t) (hℓ : ℓ = Real.log (t ^ 6)) (hℓ1 : 16 ≤ ℓ)
    (hℓ2 : ℓ ≤ 6.48 + 0.75 * t) (ha1 : t ^ 6 < a) (ha2 : a ≤ t ^ 6 + 1)
    (hh1 : 3 / 4 * (t ^ 3 * ℓ) - 1 ≤ h) (hh2 : h ≤ 3 / 4 * (t ^ 3 * ℓ)) :
    400 * h ≤ a ∧
    Real.log (a + 2 * h) * ((√(a + 2 * h) - √a + 1) + ((a + 2 * h) ^ ((1 : ℝ) / 3) + 1))
      < h - 3 * √a * (Lup (1 / 2 + 7 * a / (3 * h)) + 1 / 40) - 3 / h := by
  set u := t ^ 3 with hu
  set b := a + 2 * h with hb
  have ht0 : 0 < t := by linarith
  have hu1 : 8000 ≤ u := by rw [hu]; nlinarith [sq_nonneg t]
  have hu0 : 0 < u := by linarith
  have hy : t ^ 6 = u ^ 2 := by rw [hu]; ring
  have hℓu : 300 * ℓ ≤ u := by
    rw [hu]; nlinarith [sq_nonneg (t - 20), mul_nonneg (sq_nonneg (t - 20)) ht0.le]
  have hh0 : 9000 ≤ h := by nlinarith
  have ha0 : 0 < a := by nlinarith
  have h400 : 400 * h ≤ a := by nlinarith
  refine ⟨h400, ?_⟩
  have hsa : u ≤ √a := Real.le_sqrt_of_sq_le (by rw [← hy]; linarith)
  have hsa0 : 0 < √a := by linarith
  have hb2 : b ≤ 2 * u ^ 2 := by nlinarith
  have hbpos : 0 < b := by rw [hb]; linarith
  -- `√b − √a ≤ (3/4) ℓ`
  have hsqrt : √b - √a ≤ 3 / 4 * ℓ := by
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
    have h2 : h / √a ≤ 3 / 4 * ℓ := by
      rw [div_le_iff₀ hsa0]; nlinarith
    linarith
  -- `log b ≤ ℓ + 0.7`
  have hlogb : Real.log b ≤ ℓ + 0.7 := by
    have : Real.log b ≤ Real.log (2 * u ^ 2) := Real.log_le_log hbpos hb2
    rw [Real.log_mul (by norm_num) (by positivity), ← hy, ← hℓ] at this
    linarith [log_two_bounds.2]
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg (by nlinarith)
  -- `b^{1/3} ≤ 1.26 t²`
  have hcube : b ^ ((1 : ℝ) / 3) ≤ 1.26 * t ^ 2 := by
    have hb3 : b ≤ (1.26 * t ^ 2) ^ (3 : ℕ) := by
      have : 2 * u ^ 2 ≤ (1.26 * t ^ 2) ^ (3 : ℕ) := by rw [hu]; nlinarith [pow_pos ht0 6]
      linarith
    calc b ^ ((1 : ℝ) / 3) ≤ ((1.26 * t ^ 2) ^ (3 : ℕ)) ^ ((1 : ℝ) / 3) :=
          Real.rpow_le_rpow hbpos.le hb3 (by norm_num)
      _ = 1.26 * t ^ 2 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  -- the `L` bound
  set s := 1 / 2 + 7 * a / (3 * h) with hs
  have hh00 : 0 < h := by linarith
  have hsbig : 899 ≤ s - 1 := by
    have : 900 ≤ 7 * a / (3 * h) := by
      rw [le_div_iff₀ (by positivity)]; nlinarith
    rw [hs]; linarith
  have hfrac : 1 / s + 1 / (s - 1) ≤ 0.003 := by
    have h1 : 1 / s ≤ 1 / 899 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have h2 : 1 / (s - 1) ≤ 1 / 899 := one_div_le_one_div_of_le (by norm_num) hsbig
    linarith
  have hs2 : s / 2 ≤ 14 / 9 * (u / ℓ) * 1.002 := by
    have hℓ0 : 0 < ℓ := by linarith
    have key : 7 * a / (6 * h) ≤ 14 / 9 * (u / ℓ) * 1.001 := by
      rw [div_le_iff₀ (by positivity)]
      have e : 14 / 9 * (u / ℓ) * 1.001 * (6 * h) ≥ 14 / 9 * (u / ℓ) * 1.001 * (6 * (3 / 4 * (u * ℓ) - 1)) :=
        mul_le_mul_of_nonneg_left (by rw [hu] at *; linarith) (by positivity)
      have e2 : 14 / 9 * (u / ℓ) * 1.001 * (6 * (3 / 4 * (u * ℓ) - 1))
          = 7 * 1.001 * u ^ 2 - 14 / 9 * 1.001 * 6 * (u / ℓ) := by
        field_simp; ring
      have e3 : u / ℓ ≤ u := by rw [div_le_iff₀ hℓ0]; nlinarith
      nlinarith
    have hq : 1 / 4 ≤ 14 / 9 * (u / ℓ) * 0.001 := by
      have : 300 ≤ u / ℓ := by rw [le_div_iff₀ hℓ0]; linarith
      nlinarith
    have : s / 2 = 1 / 4 + 7 * a / (6 * h) := by rw [hs]; field_simp; ring
    rw [this]; nlinarith
  have hlogs : Real.log (s / 2) ≤ ℓ / 2 - Real.log ℓ + (14 / 9 - 1) + 0.002 := by
    have hℓ0 : 0 < ℓ := by linarith
    have hpos : 0 < s / 2 := by linarith
    have h1 : Real.log (s / 2) ≤ Real.log (14 / 9 * (u / ℓ) * 1.002) := Real.log_le_log hpos hs2
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_mul (by norm_num) (by positivity),
      Real.log_div hu0.ne' hℓ0.ne'] at h1
    have hlu : Real.log u = ℓ / 2 := by
      have e : Real.log (u ^ 2) = 2 * Real.log u := by rw [Real.log_pow]; push_cast; ring
      rw [hℓ, hy, e]; ring
    have h149 : Real.log (14 / 9) ≤ 14 / 9 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    have h1002 : Real.log 1.002 ≤ 1.002 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    linarith
  have hlogℓ : 2.7725 ≤ Real.log ℓ := by
    have : Real.log 16 ≤ Real.log ℓ := Real.log_le_log (by norm_num) (by linarith)
    have e : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    linarith [log_two_bounds.1]
  have hlogπ : 1.144 ≤ Real.log Real.pi := le_of_lt Erdos985.Analytic.PrincipalAux.log_pi_gt'
  have hL : Lup s + 1 / 40 ≤ ℓ / 4 - 1.6 := by
    unfold Lup
    linarith
  -- the factor `3√a`
  have hW : 3 * √a ≤ 3 * u + 3 / u := by
    have : √a ≤ u + 1 / u := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have : (u + 1 / u) ^ 2 = u ^ 2 + 2 + 1 / u ^ 2 := by field_simp; ring
      rw [this]; have : 0 ≤ 1 / u ^ 2 := by positivity
      have : a ≤ u ^ 2 + 1 := by rw [← hy]; exact ha2
      linarith
    have e : 3 * (u + 1 / u) = 3 * u + 3 / u := by ring
    linarith
  have hW0 : 0 ≤ 3 * √a := by positivity
  have hLpos : 0 ≤ ℓ / 4 - 1.6 := by linarith
  have hWL : 3 * √a * (Lup s + 1 / 40) ≤ (3 * u + 3 / u) * (ℓ / 4 - 1.6) :=
    (mul_le_mul_of_nonneg_left hL hW0).trans (mul_le_mul_of_nonneg_right hW hLpos)
  have hWL' : (3 * u + 3 / u) * (ℓ / 4 - 1.6) ≤ 3 / 4 * (u * ℓ) - 4.8 * u + 1 := by
    have e : (3 / u) * (ℓ / 4 - 1.6) ≤ 1 := by
      rw [div_mul_eq_mul_div, div_le_one hu0]; nlinarith
    have expand : (3 * u + 3 / u) * (ℓ / 4 - 1.6)
        = 3 / 4 * (u * ℓ) - 4.8 * u + (3 / u) * (ℓ / 4 - 1.6) := by ring
    rw [expand]; linarith
  have h3h : 3 / h ≤ 1 := by rw [div_le_one hh00]; linarith
  -- left side
  have hLHS : Real.log b * ((√b - √a + 1) + (b ^ ((1 : ℝ) / 3) + 1))
      ≤ (ℓ + 0.7) * (0.75 * ℓ + 2 + 1.26 * t ^ 2) := by
    have h1 : (√b - √a + 1) + (b ^ ((1 : ℝ) / 3) + 1) ≤ 0.75 * ℓ + 2 + 1.26 * t ^ 2 := by linarith
    have h0 : 0 ≤ (√b - √a + 1) + (b ^ ((1 : ℝ) / 3) + 1) := by
      have : √a ≤ √b := Real.sqrt_le_sqrt (by rw [hb]; linarith)
      have : 0 ≤ b ^ ((1 : ℝ) / 3) := by positivity
      linarith
    exact (mul_le_mul_of_nonneg_left h1 hlogb0).trans
      (mul_le_mul_of_nonneg_right hlogb (by positivity))
  have hfinal := poly_final_32 ht hℓ1 hℓ2
  rw [← hu] at hfinal
  rw [hu] at hh1
  linarith

/-- **Under RH, every `(x, x + (3/2)√x log x]` with `x ≥ 6.4·10^7` contains a prime.** -/
theorem exists_prime_of_RH_large_32 (hRH : RiemannHypothesis) {x : ℝ} (hx : 64 * 10 ^ 6 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x < p ∧ (p : ℝ) ≤ x + 3 / 2 * √x * Real.log x := by
  have hx0 : 0 < x := by linarith
  set t := x ^ ((1 : ℝ) / 6) with ht
  have ht6 : t ^ 6 = x := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have ht20 : 20 ≤ t := by
    have : (20 : ℝ) = ((20 : ℝ) ^ 6) ^ ((1 : ℝ) / 6) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; norm_num
    rw [this, ht]
    exact Real.rpow_le_rpow (by norm_num) (by norm_num; linarith) (by norm_num)
  have ht0 : 0 < t := by linarith
  have hsx : √x = t ^ 3 := by
    rw [← ht6, show t ^ 6 = (t ^ 3) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  set ℓ := Real.log x with hℓdef
  have hℓ : ℓ = Real.log (t ^ 6) := by rw [ht6]
  have hℓ1 : 16 ≤ ℓ := by
    have : Real.log ((2 : ℝ) ^ 24) ≤ ℓ := Real.log_le_log (by norm_num) (by norm_num; linarith)
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
  set v := 3 / 4 * (√x * ℓ) with hv
  have hv0 : 9000 ≤ v := by
    rw [hv, hsx]
    have : 8000 ≤ t ^ 3 := by nlinarith [sq_nonneg t]
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
  have hC : IntervalCondition32 a h := by
    unfold IntervalCondition32
    obtain ⟨k1, k2⟩ := key_ineq_32 (a := (a : ℝ)) (h := (h : ℝ)) ht20 hℓ hℓ1 hℓ2 (by rw [ht6]; exact ha1) (by rw [ht6]; exact ha2)
      (by rw [← hsx]; exact hh1) (by rw [← hsx]; exact hh2.le)
    exact ⟨by exact_mod_cast k1, k2⟩
  obtain ⟨p, hp, hap, hpb⟩ := exists_prime_Ico_of_RH_32 hRH hh1' hC
  refine ⟨p, hp, lt_of_lt_of_le ha1 (by exact_mod_cast hap), ?_⟩
  have : (p : ℝ) + 1 ≤ a + 2 * h := by exact_mod_cast hpb
  have e : 3 / 2 * √x * Real.log x = 2 * v := by rw [hv]; ring
  rw [e]
  linarith

end Cramer
