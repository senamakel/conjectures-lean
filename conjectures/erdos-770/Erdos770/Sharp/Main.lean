import Erdos770.Main
import Erdos770.Sharp.Statement
import Erdos770.Sharp.Finite
import Erdos770.Sharp.LLSBound
import Erdos770.Sharp.Certs32
import Erdos770.Sharp.Certs8
import Erdos770.Sharp.Certs1
import Erdos770.Sharp.Analytic

/-!
# Erdős 770 (iii) with constant 5, from LLS Theorem 1.1

`explicitBound5_of_lls : LLS.LeastPrimeOutsideSubgroup → ExplicitBound5`, that is,
`h n ≤ max (P n) ⌈5 (log n)²⌉` for every `n ≥ 2`.

Let `K = ⌈5 log² n⌉`, `M = max (P n) K`. If `gcd(2ⁿ - 1, …, Mⁿ - 1) ≠ 1`, a bad prime `r > M`
divides every `iⁿ - 1`, `2 ≤ i ≤ M` (`exists_bad_prime`).

* `n < 216`: the direct check (`finOK_all`, `gcdUpTo_eq_one_of_finOK`).
* `n ≥ 216`: `K ≥ 100`. A prime `r < 3000` would force `M < 17` (`lt_17_of_small`), so
  `r ≥ 3000` and LLS gives `M < (log r + 13/4)²` (`lt_of_lls`). Then the products of `j` primes
  `≤ K'` with `K'^j < r` contradict `|H| ≤ n`: by the certificates for `n < 2^709`
  (`certs32_ok`, `certs8_ok`, `certs1_ok`, `block_false`) and by `analytic` beyond.
-/

namespace Erdos770.Sharp

open Erdos770

lemma ceil_ge_of_log {n : ℕ} {b : ℝ} {B : ℕ} (hb : 0 ≤ b) (hlog : b ≤ Real.log n)
    (hB : (B : ℝ) - 1 < 5 * b ^ 2) : B ≤ ⌈5 * Real.log n ^ 2⌉₊ := by
  have h1 : 5 * b ^ 2 ≤ 5 * Real.log n ^ 2 := by gcongr
  have h2 : 5 * Real.log n ^ 2 ≤ (⌈5 * Real.log n ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  have : (B : ℝ) < ⌈5 * Real.log n ^ 2⌉₊ + 1 := by linarith
  have : B < ⌈5 * Real.log n ^ 2⌉₊ + 1 := by exact_mod_cast this
  omega

lemma log_ge_of_pow {n k : ℕ} (hn : 2 ^ k ≤ n) : (k : ℝ) * 0.6931471803 ≤ Real.log n := by
  have h := Real.log_le_log (by positivity) (by exact_mod_cast hn : ((2 ^ k : ℕ) : ℝ) ≤ (n : ℝ))
  push_cast at h
  rw [Real.log_pow] at h
  have := Real.log_two_gt_d9
  nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

theorem explicitBound5_of_lls (hL : LLS.LeastPrimeOutsideSubgroup) : ExplicitBound5 := by
  intro n hn
  set K := ⌈5 * Real.log n ^ 2⌉₊ with hK_def
  set M := max (P n) K with hM_def
  have hKM : K ≤ M := le_max_right _ _
  have hPM : P n ≤ M := le_max_left _ _
  by_cases hsmall : n < 216
  · -- the direct check
    have hB : finB n ≤ K := by
      unfold finB
      split_ifs with h8
      · exact ceil_ge_of_log (b := 0.6931471803) (by norm_num)
          (by simpa using log_ge_of_pow (k := 1) (by omega)) (by norm_num)
      · exact ceil_ge_of_log (b := 3 * 0.6931471803) (by norm_num)
          (by simpa using log_ge_of_pow (k := 3) (by omega)) (by norm_num)
    have hB3 : 3 ≤ finB n := by unfold finB; split_ifs <;> omega
    exact h_le_of_gcd (by omega)
      (gcdUpTo_eq_one_of_finOK (by omega) (finOK_all n hsmall hn) (by omega) hPM)
  push Not at hsmall
  have hK291 : 100 ≤ K :=
    ceil_ge_of_log (b := 7 * 0.6931471803) (by norm_num)
      (by simpa using log_ge_of_pow (k := 7) (le_trans (by norm_num) hsmall)) (by norm_num)
  apply h_le_of_gcd (by omega)
  by_contra hg
  obtain ⟨r, hr, hMr, -, hdvd⟩ := exists_bad_prime (by omega) (by omega) hg
  have hnd : ¬ (r - 1) ∣ n := fun h => by have := le_P (by omega) hr h; omega
  have hr3000 : 3000 ≤ r := by
    by_contra h
    have := lt_17_of_small (by omega) hr (by omega) hnd hdvd
    omega
  have hlt := lt_of_lls hL (by omega) hr hr3000 hMr hPM hdvd
  by_cases h11 : n < 2 ^ 11
  · -- blocks with `q = 32`
    set k := Nat.log 2 (n ^ 32) with hk_def
    have hn32 : n ^ 32 ≠ 0 := by positivity
    have hk1 : 2 ^ k ≤ n ^ 32 := Nat.pow_log_le_self 2 hn32
    have hk2 : n ^ 32 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have hk248 : 248 ≤ k := by
      rw [hk_def]
      apply Nat.le_log_of_pow_le (by norm_num)
      calc 2 ^ 248 ≤ 216 ^ 32 := by norm_num
        _ ≤ n ^ 32 := Nat.pow_le_pow_left hsmall 32
    have hk352 : k < 352 := by
      rw [hk_def]
      apply Nat.log_lt_of_lt_pow hn32
      calc n ^ 32 < (2 ^ 11) ^ 32 := Nat.pow_lt_pow_left h11 (by norm_num)
        _ = 2 ^ 352 := (pow_mul 2 11 32).symm
    obtain ⟨K', j, m, p, hb, hp⟩ :=
      checkList_sound 248 certs32 certs32_ok k hk248 (by rw [certs32_len]; omega)
    exact block_false (by norm_num) (by omega) hb hp hk1 hk2 hKM hr hlt hdvd
  push Not at h11
  by_cases h42 : n < 2 ^ 42
  · -- blocks with `q = 8`
    set k := Nat.log 2 (n ^ 8) with hk_def
    have hn8 : n ^ 8 ≠ 0 := by positivity
    have hk1 : 2 ^ k ≤ n ^ 8 := Nat.pow_log_le_self 2 hn8
    have hk2 : n ^ 8 < 2 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have hk88 : 88 ≤ k := by
      rw [hk_def]
      apply Nat.le_log_of_pow_le (by norm_num)
      calc 2 ^ 88 = (2 ^ 11) ^ 8 := pow_mul 2 11 8
        _ ≤ n ^ 8 := Nat.pow_le_pow_left h11 8
    have hk336 : k < 336 := by
      rw [hk_def]
      apply Nat.log_lt_of_lt_pow hn8
      calc n ^ 8 < (2 ^ 42) ^ 8 := Nat.pow_lt_pow_left h42 (by norm_num)
        _ = 2 ^ 336 := (pow_mul 2 42 8).symm
    obtain ⟨K', j, m, p, hb, hp⟩ :=
      checkList_sound 88 certs8 certs8_ok k hk88 (by rw [certs8_len]; omega)
    exact block_false (by norm_num) (by omega) hb hp hk1 hk2 hKM hr hlt hdvd
  push Not at h42
  by_cases h709 : n < 2 ^ 709
  · -- dyadic blocks
    set k := Nat.log 2 n with hk_def
    have hn0 : n ≠ 0 := by omega
    have hk1 : 2 ^ k ≤ n ^ 1 := by rw [pow_one]; exact Nat.pow_log_le_self 2 hn0
    have hk2 : n ^ 1 < 2 ^ (k + 1) := by rw [pow_one]; exact Nat.lt_pow_succ_log_self (by norm_num) _
    have hk42 : 42 ≤ k := Nat.le_log_of_pow_le (by norm_num) h42
    have hk709 : k < 709 := Nat.log_lt_of_lt_pow hn0 h709
    obtain ⟨K', j, m, p, hb, hp⟩ :=
      checkList_sound 42 certs1 certs1_ok k hk42 (by rw [certs1_len]; omega)
    exact block_false le_rfl (by omega) hb hp hk1 hk2 hKM hr hlt hdvd
  -- the analytic range
  push Not at h709
  obtain ⟨j, hj, hcnt⟩ := analytic h709
  rw [← hK_def] at hj hcnt
  have hr1 : (1 : ℝ) < r := by exact_mod_cast hr.one_lt
  have hlogr : 0 < Real.log r := Real.log_pos hr1
  have hsqrt : Real.sqrt (K : ℝ) < Real.log r + 13 / 4 := by
    rw [Real.sqrt_lt' (by linarith)]
    have : (K : ℝ) ≤ M := by exact_mod_cast hKM
    linarith
  have hKpos : (0 : ℝ) < K := by
    have : (100 : ℝ) ≤ K := by exact_mod_cast hK291
    linarith
  have hKj : K ^ j < r := by
    have : (K : ℝ) ^ j < r := by
      rw [← Real.log_lt_log_iff (by positivity) (by positivity), Real.log_pow]
      linarith
    exact_mod_cast this
  have := choose_le_of_bad (by omega) hr hdvd K j hKM hKj
  omega

theorem erdos_770_iii_of_lls (hL : LLS.LeastPrimeOutsideSubgroup) : Erdos770Part3 :=
  erdos_770_iii_of_explicit (explicitBound5_of_lls hL)

end Erdos770.Sharp
