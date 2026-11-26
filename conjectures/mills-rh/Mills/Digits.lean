import Mathlib
import Mills.Statement2
import Mills.Certificates
import Mills.CubesSharp

/-!
# Digits of Mills' constant under RH: 30 and 87 decimals, Caldwell–Cheng's digits

For the least Mills number `A` and every `k`, `g k ≤ A^{3^{k+1}} < g k + 1`
(`minMills_pow_bounds`): the lower half needs no hypothesis (`g_le_pow`), the upper half is
`A ≤ greedyLimit` and `⌊greedyLimit^{3^{k+1}}⌋ = g k`, which needs primes between cubes.

So each certified Mills prime `g k` pins `A` to an interval of relative width about
`1 / (3^{k+1} g k)`. With `g 4 = b₅` (29 digits) the interval fixes 30 decimals, with
`g 5 = b₆` (85 digits) it fixes 87 (`millsDigits30_of_RH`, `millsDigits87_of_RH`); in both
cases the digits are the first ones of Caldwell–Cheng's Theorem 1. The comparisons
`D^m ≤ b · 10^{N m}` and `(b + 1) · 10^{N m} ≤ (D + 1)^m` are kernel `decide`s on natural numbers
(at most `88 · 729 ≈ 64,000` digits).
-/

set_option linter.constructorNameAsVariable false
set_option maxRecDepth 100000

namespace Mills

/-- The least Mills number satisfies `g k ≤ A^{3^{k+1}} < g k + 1`, given primes between cubes. -/
theorem minMills_pow_bounds {x₀ : ℕ} (h : PrimeBetweenCubes x₀) (hx : x₀ ≤ 2521008887)
    {A : ℝ} (hA : IsMinMills A) (k : ℕ) :
    (g k : ℝ) ≤ A ^ 3 ^ (k + 1) ∧ A ^ 3 ^ (k + 1) < g k + 1 := by
  refine ⟨g_le_pow hA.1.1 hA.1.2 k, ?_⟩
  have hle : A ≤ greedyLimit := hA.2 ⟨one_lt_greedyLimit h hx, isMills_greedyLimit h hx⟩
  have hA0 : 0 ≤ A := by linarith [hA.1.1]
  have h1 : A ^ 3 ^ (k + 1) ≤ greedyLimit ^ 3 ^ (k + 1) := pow_le_pow_left₀ hA0 hle _
  have h2 : greedyLimit ^ 3 ^ (k + 1) < (g k : ℝ) + 1 := by
    have := Nat.lt_floor_add_one (greedyLimit ^ 3 ^ (k + 1))
    rwa [floor_greedyLimit h hx k] at this
  linarith

/-- Turn the two natural-number comparisons into decimal digits of `A`. -/
theorem digits_of_pow_bounds {A : ℝ} (hA0 : 0 ≤ A) {b m N D : ℕ} (hm : m ≠ 0)
    (hlo : (b : ℝ) ≤ A ^ m) (hhi : A ^ m < b + 1)
    (hD : D ^ m ≤ b * 10 ^ (N * m)) (hD1 : (b + 1) * 10 ^ (N * m) ≤ (D + 1) ^ m) :
    (D : ℝ) / 10 ^ N ≤ A ∧ A < ((D : ℝ) + 1) / 10 ^ N := by
  have h10 : (0 : ℝ) < 10 ^ N := by positivity
  have hpow : ((10 : ℝ) ^ N) ^ m = 10 ^ (N * m) := by rw [← pow_mul]
  constructor
  · have hle : ((D : ℝ) / 10 ^ N) ^ m ≤ A ^ m := by
      rw [div_pow, hpow, div_le_iff₀ (by positivity)]
      have : (D : ℝ) ^ m ≤ b * 10 ^ (N * m) := by exact_mod_cast hD
      calc (D : ℝ) ^ m ≤ b * 10 ^ (N * m) := this
        _ ≤ A ^ m * 10 ^ (N * m) := mul_le_mul_of_nonneg_right hlo (by positivity)
    exact le_of_pow_le_pow_left₀ hm hA0 hle
  · have hlt : A ^ m < (((D : ℝ) + 1) / 10 ^ N) ^ m := by
      rw [div_pow, hpow, lt_div_iff₀ (by positivity)]
      have : ((b : ℝ) + 1) * 10 ^ (N * m) ≤ ((D : ℝ) + 1) ^ m := by exact_mod_cast hD1
      calc A ^ m * 10 ^ (N * m) < (b + 1) * 10 ^ (N * m) :=
            mul_lt_mul_of_pos_right hhi (by positivity)
        _ ≤ _ := this
    exact lt_of_pow_lt_pow_left₀ m (by positivity) hlt

/-- **30 decimals of Mills' constant under RH**, from the certified fifth Mills prime `b₅`:
`1.306377883863080690468614492602…`. -/
theorem millsDigits30_of_RH :
    MillsDigits 30
      1306377883863080690468614492602 := by
  intro hRH A hA
  have hb := minMills_pow_bounds (primeBetweenCubes_one_of_RH hRH) (by norm_num) hA 4
  have hm : (3 : ℕ) ^ (4 + 1) = 243 := by norm_num
  rw [hm] at hb
  refine digits_of_pow_bounds (m := 243) (b := g 4) (by linarith [hA.1.1]) (by norm_num)
    hb.1 hb.2 ?_ ?_
  · rw [g_four]; decide +kernel
  · rw [g_four]; decide +kernel

/-- **87 decimals of Mills' constant under RH**, from the certified sixth Mills prime `b₆`. -/
theorem millsDigits87_of_RH :
    MillsDigits 87
      1306377883863080690468614492602605712916784585156713644368053759966434053766826598821501 := by
  intro hRH A hA
  have hb := minMills_pow_bounds (primeBetweenCubes_one_of_RH hRH) (by norm_num) hA 5
  have hm : (3 : ℕ) ^ (5 + 1) = 729 := by norm_num
  rw [hm] at hb
  refine digits_of_pow_bounds (m := 729) (b := g 5) (by linarith [hA.1.1]) (by norm_num)
    hb.1 hb.2 ?_ ?_
  · rw [g_five]; decide +kernel
  · rw [g_five]; decide +kernel

/-- The 87 proved digits are the first 87 decimals of Caldwell–Cheng's Theorem 1. -/
theorem millsDigits87_prefix :
    caldwellChengDigits600 / 10 ^ (600 - 87) =
      1306377883863080690468614492602605712916784585156713644368053759966434053766826598821501 := by
  decide +kernel

end Mills
