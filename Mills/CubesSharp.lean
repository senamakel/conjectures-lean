import Mathlib
import Schoenfeld.Rosser
import Mills.Statement2
import Mills.Upper

/-!
# Caldwell–Cheng's Lemma 5: under RH, a prime between `x³` and `(x+1)³` for every real `x ≥ 0.26`

From Schoenfeld's own θ bound, `Schoenfeld.schoenfeldTheta_of_RH : RiemannHypothesis →
SchoenfeldTheta`, i.e. `|θ(y) − y| < √y log² y / (8π)` for `y ≥ 599`, proved in schoenfeld-rh.
(Caldwell–Cheng use Schoenfeld's `π(x)` bound from `2657`; the θ bound reaches lower.)

* **Analytic range, real `x ≥ 9`.** Put `a = x³ ≥ 599`, `b = (x+1)³ − 1`, `u = x + 1`, `t = u^{1/4}`.
  Then `√b ≤ t⁶`, `log b ≤ 3 log u = 12 log t ≤ 12 t / e`, so
  `2 · √b log² b / (8π) ≤ 288 t⁸ / (8π e²) < 1.56 u²`, which is `< 3x² + 3x = b − a` once
  `u ≥ 10`. Hence `θ(b) > θ(a)`, and a prime `p` has `x³ < p ≤ b < (x+1)³`.
* **Small range, `1 ≤ x < 9`.** With `k = ⌊2x⌋ ∈ [2, 17]`, a prime `p` with
  `(k+1)³ < 8p < (k+2)³` gives `x³ < ((k+1)/2)³ < p < (k/2+1)³ ≤ (x+1)³` (16 explicit primes).
* **`2^{1/3} − 1 ≤ x < 1`.** `p = 2`: `x³ < 1 < 2 ≤ (x+1)³`, with equality only at `x = 2^{1/3} − 1`.
-/

set_option linter.constructorNameAsVariable false

namespace Mills

open Chebyshev Real

/-- A strict increase of `θ` over `(a, b]` (real endpoints) produces a prime there. -/
lemma exists_prime_of_theta_lt_real {a b : ℝ} (ha : 0 ≤ a) (h : θ a < θ b) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ (p : ℝ) ≤ b := by
  have hb : 0 ≤ b := by
    by_contra hb
    push Not at hb
    have : θ b = 0 := by
      unfold Chebyshev.theta
      rw [Nat.floor_eq_zero.mpr (by linarith)]
      simp
    have h0 : 0 ≤ θ a := Chebyshev.theta_nonneg a
    linarith
  have h' : θ ((⌊a⌋₊ : ℕ) : ℝ) < θ ((⌊b⌋₊ : ℕ) : ℝ) := by
    unfold Chebyshev.theta at h ⊢
    simpa only [Nat.floor_natCast] using h
  obtain ⟨p, hp, h1, h2⟩ := exists_prime_of_theta_lt h'
  refine ⟨p, hp, ?_, ?_⟩
  · exact (Nat.floor_lt ha).mp (by exact_mod_cast h1)
  · exact (Nat.le_floor_iff hb).mp (by exact_mod_cast h2)

/-- The key inequality: for real `x ≥ 9`, `2 · √b log² b / (8π) < 3x² + 3x` with
`b = (x+1)³ − 1`. -/
lemma cubes_inequality_sharp (x : ℝ) (hx : 9 ≤ x) :
    2 * (1 / (8 * π) * (√((x + 1) ^ 3 - 1) * Real.log ((x + 1) ^ 3 - 1) ^ 2))
      < 3 * x ^ 2 + 3 * x := by
  set b := (x + 1) ^ 3 - 1 with hb
  set u := x + 1 with hu
  have hu10 : 10 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  set t : ℝ := u ^ ((1 : ℝ) / ((4 : ℕ) : ℝ)) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hu0 _
  have ht4 : t ^ 4 = u := root_pow _ hu0.le 4 (by norm_num)
  have hu3 : (10 : ℝ) ^ 3 ≤ u ^ 3 := pow_le_pow_left₀ (by norm_num) hu10 3
  have hb1 : 1 ≤ b := by rw [hb]; linarith
  have hbu : b ≤ u ^ 3 := by rw [hb]; linarith
  -- `√b ≤ t⁶`
  have hsq : √b ≤ t ^ 6 := by
    have : u ^ 3 = (t ^ 6) ^ 2 := by rw [← ht4]; ring
    calc √b ≤ √((t ^ 6) ^ 2) := Real.sqrt_le_sqrt (this ▸ hbu)
      _ = t ^ 6 := Real.sqrt_sq (by positivity)
  -- `log t ≤ t / e`
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hlogt : Real.log t ≤ t / Real.exp 1 := by
    have h1 := Real.log_le_sub_one_of_pos (div_pos ht0 he)
    rw [Real.log_div ht0.ne' he.ne', Real.log_exp] at h1
    linarith
  -- `log b ≤ 12 t / e`
  have hlogb : Real.log b ≤ 12 * (t / Real.exp 1) := by
    calc Real.log b ≤ Real.log (u ^ 3) := Real.log_le_log (by linarith) hbu
      _ = 12 * Real.log t := by rw [← ht4, ← pow_mul, Real.log_pow]; push_cast; ring
      _ ≤ 12 * (t / Real.exp 1) := by linarith
  have hlogb0 : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hK : √b * Real.log b ^ 2 ≤ t ^ 6 * (12 * (t / Real.exp 1)) ^ 2 :=
    mul_le_mul hsq (pow_le_pow_left₀ hlogb0 hlogb 2) (by positivity) (by positivity)
  -- numerical constants
  have hpi : (3.14 : ℝ) < π := Real.pi_gt_d2
  have he1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hK' : √b * Real.log b ^ 2 ≤ 144 * t ^ 8 / 7.38 := by
    have : (12 * (t / Real.exp 1)) ^ 2 = 144 * t ^ 2 / (Real.exp 1) ^ 2 := by
      field_simp; ring
    rw [this] at hK
    have he2 : (7.38 : ℝ) ≤ Real.exp 1 ^ 2 := by nlinarith
    calc √b * Real.log b ^ 2 ≤ t ^ 6 * (144 * t ^ 2 / Real.exp 1 ^ 2) := hK
      _ ≤ t ^ 6 * (144 * t ^ 2 / 7.38) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact div_le_div_of_nonneg_left (by positivity) (by norm_num) he2
      _ = 144 * t ^ 8 / 7.38 := by ring
  have hpos : 0 ≤ √b * Real.log b ^ 2 := by positivity
  have hc : 2 * (1 / (8 * π) * (√b * Real.log b ^ 2)) ≤ 2 * (√b * Real.log b ^ 2) / 25.12 := by
    have : 1 / (8 * π) ≤ 1 / 25.12 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith
    have h := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right this hpos)
      (by norm_num : (0 : ℝ) ≤ 2)
    calc 2 * (1 / (8 * π) * (√b * Real.log b ^ 2))
        ≤ 2 * (1 / 25.12 * (√b * Real.log b ^ 2)) := h
      _ = 2 * (√b * Real.log b ^ 2) / 25.12 := by ring
  have ht8 : t ^ 8 = u ^ 2 := by rw [← ht4]; ring
  have hfin : 2 * (144 * t ^ 8 / 7.38) / 25.12 < 3 * x ^ 2 + 3 * x := by
    rw [ht8]
    have : 3 * x ^ 2 + 3 * x = 3 * u ^ 2 - 3 * u := by rw [hu]; ring
    rw [this]
    have e : 2 * (144 * u ^ 2 / 7.38) / 25.12 = (288 / (7.38 * 25.12)) * u ^ 2 := by ring
    rw [e]
    have hc : (288 / (7.38 * 25.12) : ℝ) ≤ 1.56 := by norm_num
    have h2 : 0 ≤ u ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hu10 hu0.le]
  calc 2 * (1 / (8 * π) * (√b * Real.log b ^ 2)) ≤ 2 * (√b * Real.log b ^ 2) / 25.12 := hc
    _ ≤ 2 * (144 * t ^ 8 / 7.38) / 25.12 := by
        apply div_le_div_of_nonneg_right _ (by norm_num); linarith
    _ < 3 * x ^ 2 + 3 * x := hfin

/-- **Analytic range**: under RH, every real `x ≥ 9` has a prime in `(x³, (x+1)³)`. -/
theorem primeStrictlyBetweenCubes_large (hRH : RiemannHypothesis) (x : ℝ) (hx : 9 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ (p : ℝ) < (x + 1) ^ 3 := by
  have hth := Schoenfeld.schoenfeldTheta_of_RH hRH
  set a := x ^ 3 with ha
  set b := (x + 1) ^ 3 - 1 with hb
  have hx0 : 0 < x := by linarith
  have ha599 : (599 : ℝ) ≤ a := by rw [ha]; nlinarith [mul_pos hx0 hx0]
  have hab : a ≤ b := by rw [ha, hb]; nlinarith [mul_pos hx0 hx0]
  have hA := hth a ha599
  have hB := hth b (le_trans ha599 hab)
  have hloga : 0 ≤ Real.log a := Real.log_nonneg (by linarith)
  have hmono : √a * Real.log a ^ 2 ≤ √b * Real.log b ^ 2 :=
    mul_le_mul (Real.sqrt_le_sqrt hab)
      (pow_le_pow_left₀ hloga (Real.log_le_log (by linarith) hab) 2) (by positivity)
      (Real.sqrt_nonneg _)
  have hkey := cubes_inequality_sharp x hx
  rw [← hb] at hkey
  rw [abs_lt] at hA hB
  have hc : 0 < 1 / (8 * π) := by positivity
  have hlt : θ a < θ b := by
    have hd : b - a = 3 * x ^ 2 + 3 * x := by rw [ha, hb]; ring
    have := mul_le_mul_of_nonneg_left hmono hc.le
    nlinarith [hA.1, hA.2, hB.1, hB.2]
  obtain ⟨p, hp, h1, h2⟩ := exists_prime_of_theta_lt_real (by positivity) hlt
  exact ⟨p, hp, h1, by linarith⟩

/-- The 16 small cells: for `2 ≤ k ≤ 17` a prime `p` with `(k+1)³ < 8p < (k+2)³`. -/
lemma small_cell (k : ℕ) (h1 : 2 ≤ k) (h2 : k ≤ 17) :
    ∃ p : ℕ, p.Prime ∧ (k + 1) ^ 3 < 8 * p ∧ 8 * p < (k + 2) ^ 3 := by
  interval_cases k
  · exact ⟨5, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨11, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨17, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨29, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨43, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨67, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨97, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨127, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨167, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨223, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨277, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨347, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨431, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨523, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨631, by norm_num, by norm_num, by norm_num⟩
  · exact ⟨739, by norm_num, by norm_num, by norm_num⟩

/-- **Small range**, no hypothesis: every real `1 ≤ x < 9` has a prime in `(x³, (x+1)³)`. -/
theorem primeStrictlyBetweenCubes_small (x : ℝ) (hx1 : 1 ≤ x) (hx9 : x < 9) :
    ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ (p : ℝ) < (x + 1) ^ 3 := by
  set k := ⌊2 * x⌋₊ with hk
  have h2x : 0 ≤ 2 * x := by linarith
  have hkle : (k : ℝ) ≤ 2 * x := Nat.floor_le h2x
  have hklt : 2 * x < k + 1 := Nat.lt_floor_add_one _
  have hk2 : 2 ≤ k := by
    have : (2 : ℝ) ≤ k := by
      have := Nat.floor_le_floor (show (2 : ℝ) ≤ 2 * x by linarith)
      rw [hk]; exact_mod_cast (by simpa using this)
    exact_mod_cast this
  have hk17 : k ≤ 17 := by
    have : (k : ℝ) < 18 := by linarith
    have : k < 18 := by exact_mod_cast this
    omega
  obtain ⟨p, hp, hp1, hp2⟩ := small_cell k hk2 hk17
  have hp1' : ((k : ℝ) + 1) ^ 3 < 8 * p := by exact_mod_cast hp1
  have hp2' : 8 * (p : ℝ) < ((k : ℝ) + 2) ^ 3 := by exact_mod_cast hp2
  refine ⟨p, hp, ?_, ?_⟩
  · have : (2 * x) ^ 3 < ((k : ℝ) + 1) ^ 3 := pow_lt_pow_left₀ hklt (by linarith) (by norm_num)
    nlinarith
  · have : ((k : ℝ) + 2) ^ 3 ≤ (2 * x + 2) ^ 3 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 3
    nlinarith

/-- `2^{1/3}` cubed is `2`. -/
lemma cbrt_two_pow : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 = 2 := by
  have := root_pow (2 : ℝ) (by norm_num) 3 (by norm_num)
  simpa using this

lemma one_lt_cbrt_two : 1 < (2 : ℝ) ^ ((1 : ℝ) / 3) :=
  Real.one_lt_rpow (by norm_num) (by norm_num)

/-- Under RH, every real `x ≥ 1` has a prime in `(x³, (x+1)³)`. -/
theorem primeStrictlyBetweenCubes_ge_one (hRH : RiemannHypothesis) (x : ℝ) (hx : 1 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x ^ 3 < p ∧ (p : ℝ) < (x + 1) ^ 3 := by
  rcases lt_or_ge x 9 with h | h
  · exact primeStrictlyBetweenCubes_small x hx h
  · exact primeStrictlyBetweenCubes_large hRH x h

/-- **Caldwell–Cheng 2005, Lemma 5**, from RH (with Schoenfeld's θ bound, proved in
schoenfeld-rh). -/
theorem caldwellChengLemma5_of_RH : CaldwellChengLemma5 := by
  intro hRH x hx
  rcases lt_or_ge x 1 with h | h
  · have hc := one_lt_cbrt_two
    have hx0 : 0 < x := by linarith
    refine ⟨2, Nat.prime_two, ?_, ?_⟩
    · have : x ^ 3 < 1 := pow_lt_one₀ hx0.le h (by norm_num)
      push_cast; linarith
    · have : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 ≤ (x + 1) ^ 3 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 3
      rw [cbrt_two_pow] at this
      push_cast; linarith
  · obtain ⟨p, hp, h1, h2⟩ := primeStrictlyBetweenCubes_ge_one hRH x h
    exact ⟨p, hp, h1, h2.le⟩

/-- The strict form of Lemma 5: under RH, every real `x > 2^{1/3} − 1` has a prime in the open
interval `(x³, (x+1)³)`. -/
theorem primeStrictlyBetweenCubes_of_RH : PrimeStrictlyBetweenCubesOfRH := by
  intro hRH x hx
  rcases lt_or_ge x 1 with h | h
  · have hc := one_lt_cbrt_two
    have hx0 : 0 < x := by linarith
    refine ⟨2, Nat.prime_two, ?_, ?_⟩
    · have : x ^ 3 < 1 := pow_lt_one₀ hx0.le h (by norm_num)
      push_cast; linarith
    · have : ((2 : ℝ) ^ ((1 : ℝ) / 3)) ^ 3 < (x + 1) ^ 3 :=
        pow_lt_pow_left₀ (by linarith) (by positivity) (by norm_num)
      rw [cbrt_two_pow] at this
      push_cast; linarith
  · exact primeStrictlyBetweenCubes_ge_one hRH x h

/-- The integer form used by `Mills.Upper`: under RH, `PrimeBetweenCubes 1`. -/
theorem primeBetweenCubes_one_of_RH (hRH : RiemannHypothesis) : PrimeBetweenCubes 1 := by
  intro x hx
  obtain ⟨p, hp, h1, h2⟩ := primeStrictlyBetweenCubes_ge_one hRH (x : ℝ) (by exact_mod_cast hx)
  refine ⟨p, hp, ?_, ?_⟩
  · exact_mod_cast h1
  · exact_mod_cast h2

end Mills
