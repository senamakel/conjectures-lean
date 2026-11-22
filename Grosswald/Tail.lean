import Grosswald.Analytic
import Grosswald.Crit

/-!
# Every `p ≥ 10^47` (replacing Robin's bound on `ω`)

MTT bound `ω(p-1)` with Robin's estimate. We use instead
`256^ω · ∏_{r < 256 prime} r ≤ (p - 1) · 256^{54}` (`Erdos985.pow_card_primeFactors_mul_le`),
which gives `2^ω < 4520 · p^{1/8}`, roughly. With `x = ⌊√p⌋ - 2`, `y = √x`, `z = √y` this says
`2^ω < 4520 z`, and the tangent bound `log y = 2 log z ≤ 2 (log 2^20 + z/2^20 - 1)` turns the
Theorem 2 inequality (sieve with `S = ∅`) into a quadratic inequality in `z`, true for
`z ≥ 7·10^5`.
-/

namespace Grosswald

open Real Erdos985

/-- `∏_{r < 256 prime} r`. -/
def primorial256 : ℕ :=
  64266330917908644872330635228106713310880186591609208114244758680898150367880703152525200743234420230

set_option maxRecDepth 100000 in
lemma prod_primes_lt_256 : ∏ r ∈ (Finset.range 256).filter Nat.Prime, r = primorial256 := by
  decide

set_option maxRecDepth 100000 in
lemma card_primes_lt_256 : ((Finset.range 256).filter Nat.Prime).card = 54 := by
  decide

lemma sieveK_zero (n : ℕ) : sieveK n 0 1 = 2 ^ n - 1 := by
  simp [sieveK]; norm_num

theorem sieveIneq_of_large {p : ℕ} (hp : 10 ^ 47 ≤ p) :
    SieveIneq (p - 1).primeFactors.card 0 1 p := by
  set k := (p - 1).primeFactors.card with hk
  unfold SieveIneq
  rw [sieveK_zero]
  set x := xOf p with hxdef
  -- sizes
  have hsq : (5 * 10 ^ 11) ^ 2 + 2 ≤ Nat.sqrt p := Nat.le_sqrt'.mpr (le_trans (by norm_num) hp)
  have hxY : (5 * 10 ^ 11) ^ 2 ≤ x := by simp only [hxdef, xOf]; omega
  have hxR : ((5 * 10 ^ 11 : ℝ)) ^ 2 ≤ x := by exact_mod_cast hxY
  set y := √(x : ℝ) with hy
  have hYy : (5 * 10 ^ 11 : ℝ) ≤ y := Real.le_sqrt_of_sq_le hxR
  have hy0 : 0 < y := by linarith
  have hxy : (x : ℝ) = y ^ 2 := by rw [hy, Real.sq_sqrt (by positivity)]
  set z := √y with hz
  have hZz : (7 * 10 ^ 5 : ℝ) ≤ z := Real.le_sqrt_of_sq_le (by linarith)
  have hz0 : 0 < z := by linarith
  have hyz : y = z ^ 2 := by rw [hz, Real.sq_sqrt hy0.le]
  have hp1 : 1 < p := lt_of_lt_of_le (by norm_num) hp
  have hpx : (p : ℝ) < ((x : ℝ) + 3) ^ 2 := by
    have h1 := Nat.lt_succ_sqrt' p
    have h2 : Nat.succ (Nat.sqrt p) = x + 3 := by simp only [hxdef, xOf]; omega
    rw [h2] at h1
    exact_mod_cast h1
  -- `2^ω < 4520 z`
  have hnat := pow_card_primeFactors_mul_le 256 (p - 1) (by omega)
  rw [← hk, prod_primes_lt_256, card_primes_lt_256] at hnat
  have hnatR : ((2 : ℝ) ^ k) ^ 8 * primorial256 ≤ p * 256 ^ 54 := by
    have h1 : 256 ^ k * primorial256 ≤ p * 256 ^ 54 :=
      hnat.trans (Nat.mul_le_mul_right _ (Nat.sub_le p 1))
    have h2 : ((2 : ℝ) ^ k) ^ 8 = (256 : ℝ) ^ k := by
      rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h2]
    exact_mod_cast h1
  have hpz : (p : ℝ) ≤ z ^ 8 * (1 + 3 / (5 * 10 ^ 11) ^ 2) ^ 2 := by
    have e : (x : ℝ) + 3 = z ^ 4 * (1 + 3 / z ^ 4) := by
      rw [hxy, hyz]; field_simp
    have h3 : 3 / z ^ 4 ≤ 3 / (5 * 10 ^ 11) ^ 2 := by
      have : (5 * 10 ^ 11 : ℝ) ^ 2 ≤ z ^ 4 := by
        rw [show z ^ 4 = y ^ 2 by rw [hyz]; ring]
        exact pow_le_pow_left₀ (by norm_num) hYy 2
      gcongr
    calc (p : ℝ) ≤ ((x : ℝ) + 3) ^ 2 := hpx.le
      _ = (z ^ 4) ^ 2 * (1 + 3 / z ^ 4) ^ 2 := by rw [e]; ring
      _ ≤ (z ^ 4) ^ 2 * (1 + 3 / (5 * 10 ^ 11) ^ 2) ^ 2 := by gcongr
      _ = z ^ 8 * (1 + 3 / (5 * 10 ^ 11) ^ 2) ^ 2 := by ring
  have hK : (2 : ℝ) ^ k ≤ 4520 * z := by
    by_contra hcon
    rw [not_le] at hcon
    have h1 : (4520 * z) ^ 8 ≤ ((2 : ℝ) ^ k) ^ 8 := pow_le_pow_left₀ (by positivity) hcon.le 8
    have h2 : (4520 * z) ^ 8 * primorial256 ≤ z ^ 8 * (1 + 3 / (5 * 10 ^ 11) ^ 2) ^ 2 * 256 ^ 54 := by
      calc (4520 * z) ^ 8 * (primorial256 : ℝ) ≤ ((2 : ℝ) ^ k) ^ 8 * primorial256 :=
            mul_le_mul_of_nonneg_right h1 (by positivity)
        _ ≤ (p : ℝ) * 256 ^ 54 := hnatR
        _ ≤ _ := by gcongr
    have hz8 : 0 < z ^ 8 := by positivity
    have h3 : (4520 : ℝ) ^ 8 * primorial256 ≤ (1 + 3 / (5 * 10 ^ 11) ^ 2) ^ 2 * 256 ^ 54 := by
      have : z ^ 8 * ((4520 : ℝ) ^ 8 * primorial256)
          ≤ z ^ 8 * ((1 + 3 / (5 * 10 ^ 11) ^ 2) ^ 2 * 256 ^ 54) := by
        rw [mul_pow] at h2; linarith
      exact le_of_mul_le_mul_left this hz8
    unfold primorial256 at h3
    norm_num at h3
  have hK0 : (0 : ℝ) ≤ 2 ^ k - 1 := by
    have : (1 : ℝ) ≤ 2 ^ k := one_le_pow₀ (by norm_num)
    linarith
  -- the bracket
  set La : ℝ := 20 * (6931471808 / 10 ^ 10) with hLa
  set a : ℝ := 2 ^ 20 with ha
  clear_value La a
  have hloga : Real.log a ≤ La := by
    rw [ha, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    norm_num at this ⊢
    linarith
  have hT : Real.log y ≤ 2 * (La + z / a - 1) := by
    have h1 := log_le_tangent z a hz0 (by positivity)
    have h2 : Real.log y = 2 * Real.log z := by rw [hyz, Real.log_pow]; norm_num
    linarith
  have hb := Crit.bracket_le p x (5 * 10 ^ 11) y (2 * (La + z / a - 1)) (by norm_num) hYy hxy hp1
    hpx hT
  set g : ℝ := 1 + 2 / (5 * 10 ^ 11) + 3 / (5 * 10 ^ 11) ^ 3 with hg
  have hbr : (2 / 3) * g * (4 * (2 * (La + z / a - 1)) + 6 / (5 * 10 ^ 11) ^ 2 + 5 / 3)
      + (2 * (2 * (La + z / a - 1)) + 2) / y ≤ 70 + (51 / 10 ^ 7) * z := by
    have e1 : (2 / 3) * g * (4 * (2 * (La + z / a - 1)) + 6 / (5 * 10 ^ 11) ^ 2 + 5 / 3)
        = (2 / 3) * g * (8 * La - 8 + 6 / (5 * 10 ^ 11) ^ 2 + 5 / 3) + (16 * g / (3 * a)) * z := by
      field_simp; ring
    have e2 : (2 * (2 * (La + z / a - 1)) + 2) / y = (4 * La - 2) / z ^ 2 + 4 / (a * z) := by
      rw [hyz]; field_simp; ring
    have h1 : (2 / 3) * g * (8 * La - 8 + 6 / (5 * 10 ^ 11) ^ 2 + 5 / 3) ≤ 69.8 := by
      rw [hg, hLa]; norm_num
    have h2 : 16 * g / (3 * a) ≤ 51 / 10 ^ 7 := by rw [hg, ha]; norm_num
    have hz2 : (7 * 10 ^ 5 : ℝ) ^ 2 ≤ z ^ 2 := pow_le_pow_left₀ (by norm_num) hZz 2
    have h3 : (4 * La - 2) / z ^ 2 ≤ (4 * La - 2) / (7 * 10 ^ 5) ^ 2 := by
      apply div_le_div_of_nonneg_left _ (by norm_num) hz2
      rw [hLa]; norm_num
    have h4 : 4 / (a * z) ≤ 4 / (a * (7 * 10 ^ 5)) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      rw [ha]; gcongr
    have h5 : (4 * La - 2) / (7 * 10 ^ 5) ^ 2 + 4 / (a * (7 * 10 ^ 5)) ≤ 0.2 := by
      rw [hLa, ha]; norm_num
    rw [e1, e2]
    nlinarith
  -- conclude
  have hquad : (2 ^ k - 1) * (70 + (51 / 10 ^ 7) * z) < z ^ 2 / 2 - 1 / 20 - 3 / z ^ 2 := by
    have hA0 : (0 : ℝ) ≤ 70 + (51 / 10 ^ 7) * z := by positivity
    have h1 : (2 ^ k - 1) * (70 + (51 / 10 ^ 7) * z) ≤ (4520 * z) * (70 + (51 / 10 ^ 7) * z) :=
      mul_le_mul_of_nonneg_right (by linarith) hA0
    have h2 : 3 / z ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    nlinarith [mul_nonneg (sub_nonneg.2 hZz) (sub_nonneg.2 hZz)]
  rw [show (x : ℝ) / 2 = y ^ 2 / 2 by rw [hxy]]
  have hfin : (2 ^ k - 1) * (bachC p x * y * Real.log p) ≤ y * ((2 ^ k - 1) * (70 + (51 / 10 ^ 7) * z)) := by
    have := mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_left hbr hy0.le)) hK0
    linarith
  have : y * ((2 ^ k - 1) * (70 + (51 / 10 ^ 7) * z)) < y * (z ^ 2 / 2 - 1 / 20 - 3 / z ^ 2) :=
    mul_lt_mul_of_pos_left hquad hy0
  have e : y * (z ^ 2 / 2 - 1 / 20 - 3 / z ^ 2) = y ^ 2 / 2 - (y / 20 + 3) := by
    rw [hyz]; field_simp; ring
  linarith

end Grosswald
