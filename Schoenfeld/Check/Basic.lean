import Mathlib

/-!
# Rational enclosures for the finite checks

Computable rational bounds, each with a soundness lemma:

* `rdDown`, `rdUp`: rounding to multiples of `2^{-64}`, so that denominators stay bounded;
* `logLo q ≤ log q ≤ logUp q` for rational `q ≥ 1`: write `q = 2^e r` with `1 ≤ r < 2`,
  then `log r = −log(1 − y)`, `y = 1 − 1/r ∈ [0, 1/2]`, by the series of Mathlib's
  `Real.abs_log_sub_add_sum_range_le` (40 terms, tail `≤ 2^{-40}`), and
  `0.6931471803 < log 2 < 0.6931471808` (`Real.log_two_gt_d9`, `Real.log_two_lt_d9`);
* `sqrtLo q ≤ √q` (`Nat.sqrt` at scale `2^{32}`);
* `invLo x ≤ 1/x ≤ invUp x` for `x > 0`;
* `F2lo a ≤ √a log² a/(8π)` and `F1lo a ≤ √a log a/(8π)` for `a ≥ 1`
  (`π < 3.141593`, `Real.pi_lt_d6`), and both right-hand sides are monotone on `[1, ∞)`.
-/

namespace Schoenfeld.Check

open Finset Real

/-- Working precision (bits). -/
def prec : ℕ := 64

/-- Round down to a multiple of `2^{-prec}`. -/
def rdDown (q : ℚ) : ℚ := (⌊q * 2 ^ prec⌋ : ℚ) / 2 ^ prec

/-- Round up to a multiple of `2^{-prec}`. -/
def rdUp (q : ℚ) : ℚ := (⌈q * 2 ^ prec⌉ : ℚ) / 2 ^ prec

lemma rdDown_le (q : ℚ) : rdDown q ≤ q := by
  unfold rdDown
  rw [div_le_iff₀ (by positivity)]
  exact Int.floor_le _

lemma le_rdUp (q : ℚ) : q ≤ rdUp q := by
  unfold rdUp
  rw [le_div_iff₀ (by positivity)]
  exact Int.le_ceil _

lemma rdDown_le_real {q : ℚ} {x : ℝ} (h : (q : ℝ) ≤ x) : (rdDown q : ℝ) ≤ x :=
  le_trans (by exact_mod_cast rdDown_le q) h

lemma le_rdUp_real {q : ℚ} {x : ℝ} (h : x ≤ (q : ℝ)) : x ≤ (rdUp q : ℝ) :=
  le_trans h (by exact_mod_cast le_rdUp q)

/-! ### Logarithms -/

/-- Number of terms of the series `log r = Σ_{i≥1} y^i / i`, `y = 1 − 1/r`. -/
def nTerms : ℕ := 40

/-- `Σ_{i<K} y^{i+1}/(i+1)`. -/
def logSeries (y : ℚ) : ℚ := ∑ i ∈ range nTerms, y ^ (i + 1) / (i + 1)

/-- The series tail bound `y^{K+1}/(1 − y)`. -/
def logTail (y : ℚ) : ℚ := y ^ (nTerms + 1) / (1 - y)

/-- Rational lower bound for `log 2` (`Real.log_two_gt_d9`). -/
def l2L : ℚ := 6931471803 / 10 ^ 10

/-- Rational upper bound for `log 2` (`Real.log_two_lt_d9`). -/
def l2U : ℚ := 6931471808 / 10 ^ 10

/-- Exponent `e` with `2^e ≤ q < 2^{e+1}` for `q ≥ 1`. -/
def lexp (q : ℚ) : ℕ := Nat.log 2 ⌊q⌋₊

/-- Lower bound for `log q`, `q ≥ 1`. -/
def logLo (q : ℚ) : ℚ :=
  let e := lexp q
  let y := 1 - 1 / (q / 2 ^ e)
  rdDown (e * l2L + (logSeries y - logTail y))

/-- Upper bound for `log q`, `q ≥ 1`. -/
def logUp (q : ℚ) : ℚ :=
  let e := lexp q
  let y := 1 - 1 / (q / 2 ^ e)
  rdUp (e * l2U + (logSeries y + logTail y))

lemma log_series_bounds {r : ℚ} (h1 : 1 ≤ r) (h2 : r ≤ 2) :
    ((logSeries (1 - 1 / r) - logTail (1 - 1 / r) : ℚ) : ℝ) ≤ Real.log r ∧
      Real.log r ≤ ((logSeries (1 - 1 / r) + logTail (1 - 1 / r) : ℚ) : ℝ) := by
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast h1
  have hr2 : (r : ℝ) ≤ 2 := by exact_mod_cast h2
  set y : ℝ := 1 - 1 / (r : ℝ) with hy
  have hy0 : 0 ≤ y := by
    rw [hy, sub_nonneg, div_le_one (by linarith)]; exact hr1
  have hy1 : y ≤ 1 / 2 := by
    rw [hy]
    have : 1 / 2 ≤ 1 / (r : ℝ) := one_div_le_one_div_of_le (by linarith) hr2
    linarith
  have habs : |y| < 1 := by rw [abs_of_nonneg hy0]; linarith
  have h := Real.abs_log_sub_add_sum_range_le habs nTerms
  rw [abs_of_nonneg hy0] at h
  have hlog : Real.log (1 - y) = -Real.log r := by
    rw [hy, sub_sub_cancel, one_div, Real.log_inv]
  rw [hlog] at h
  have hS : ((logSeries (1 - 1 / r) : ℚ) : ℝ) = ∑ i ∈ range nTerms, y ^ (i + 1) / (i + 1) := by
    simp only [logSeries, hy]; push_cast; rfl
  have hT : ((logTail (1 - 1 / r) : ℚ) : ℝ) = y ^ (nTerms + 1) / (1 - y) := by
    simp only [logTail, hy]; push_cast; rfl
  push_cast
  rw [hS, hT]
  constructor <;> linarith [(abs_le.mp h).1, (abs_le.mp h).2]

lemma lexp_facts {q : ℚ} (hq : 1 ≤ q) :
    1 ≤ q / 2 ^ lexp q ∧ q / 2 ^ lexp q ≤ 2 ∧
      Real.log q = lexp q * Real.log 2 + Real.log ((q / 2 ^ lexp q : ℚ) : ℝ) := by
  set n := ⌊q⌋₊ with hn
  have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast hq)
  set e := lexp q with he
  have he' : e = Nat.log 2 n := rfl
  have hpe : 2 ^ e ≤ n := by rw [he']; exact Nat.pow_log_le_self 2 (by omega)
  have hpe' : n < 2 ^ (e + 1) := by rw [he']; exact Nat.lt_pow_succ_log_self (by norm_num) n
  have hqn : (n : ℚ) ≤ q := Nat.floor_le (by linarith)
  have hqn' : q < n + 1 := Nat.lt_floor_add_one q
  have h2e : (0 : ℚ) < 2 ^ e := by positivity
  refine ⟨?_, ?_, ?_⟩
  · rw [le_div_iff₀ h2e, one_mul]
    exact le_trans (by exact_mod_cast hpe) hqn
  · rw [div_le_iff₀ h2e]
    have : ((n + 1 : ℕ) : ℚ) ≤ 2 ^ (e + 1) := by exact_mod_cast hpe'
    push_cast at this
    rw [pow_succ] at this
    linarith
  · have hq0' : (0 : ℚ) < q := by linarith
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq0'
    push_cast
    rw [Real.log_div hq0.ne' (by positivity), Real.log_pow]
    ring

lemma logLo_le {q : ℚ} (hq : 1 ≤ q) : (logLo q : ℝ) ≤ Real.log q := by
  obtain ⟨h1, h2, hsplit⟩ := lexp_facts hq
  have hs := (log_series_bounds h1 h2).1
  have hl2 : (l2L : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; simp only [l2L]; push_cast; linarith
  unfold logLo
  apply rdDown_le_real
  push_cast at hsplit ⊢
  rw [hsplit]
  have : (lexp q : ℝ) * l2L ≤ lexp q * Real.log 2 := mul_le_mul_of_nonneg_left hl2 (by positivity)
  push_cast at hs
  linarith

lemma le_logUp {q : ℚ} (hq : 1 ≤ q) : Real.log q ≤ (logUp q : ℝ) := by
  obtain ⟨h1, h2, hsplit⟩ := lexp_facts hq
  have hs := (log_series_bounds h1 h2).2
  have hl2 : Real.log 2 ≤ (l2U : ℝ) := by
    have := Real.log_two_lt_d9; simp only [l2U]; push_cast; linarith
  unfold logUp
  apply le_rdUp_real
  push_cast at hsplit ⊢
  rw [hsplit]
  have : (lexp q : ℝ) * Real.log 2 ≤ lexp q * l2U := mul_le_mul_of_nonneg_left hl2 (by positivity)
  push_cast at hs
  linarith

/-! ### Square roots and reciprocals -/

/-- Lower bound for `√q`. -/
def sqrtLo (q : ℚ) : ℚ := (Nat.sqrt ⌊q * 4 ^ 32⌋₊ : ℚ) / 2 ^ 32

lemma sqrtLo_le {q : ℚ} (hq : 0 ≤ q) : (sqrtLo q : ℝ) ≤ √(q : ℝ) := by
  set m := ⌊q * 4 ^ 32⌋₊
  set s := Nat.sqrt m
  have hsm : s * s ≤ m := Nat.sqrt_le m
  have hm : (m : ℚ) ≤ q * 4 ^ 32 := Nat.floor_le (by positivity)
  have hsq : ((s : ℚ) / 2 ^ 32) ^ 2 ≤ q := by
    rw [div_pow, div_le_iff₀ (by positivity)]
    have : ((s * s : ℕ) : ℚ) ≤ m := by exact_mod_cast hsm
    push_cast at this
    calc (s : ℚ) ^ 2 = s * s := by ring
      _ ≤ m := this
      _ ≤ q * 4 ^ 32 := hm
      _ = q * (2 ^ 32) ^ 2 := by norm_num
  have h0 : (0 : ℝ) ≤ (s : ℝ) / 2 ^ 32 := by positivity
  have hsq' : ((s : ℝ) / (2 : ℝ) ^ 32) ^ 2 ≤ (q : ℝ) := by
    have := (Rat.cast_le (K := ℝ)).mpr hsq
    push_cast at this
    exact this
  unfold sqrtLo
  push_cast
  rw [← Real.sqrt_sq h0]
  exact Real.sqrt_le_sqrt hsq'

/-- Upper bound for `1/x`. -/
def invUp (x : ℚ) : ℚ := rdUp (1 / x)

/-- Lower bound for `1/x`. -/
def invLo (x : ℚ) : ℚ := rdDown (1 / x)

lemma one_div_le_invUp {x : ℚ} {y : ℝ} (hx : 0 < x) (hxy : (x : ℝ) ≤ y) :
    1 / y ≤ (invUp x : ℝ) := by
  apply le_rdUp_real
  push_cast
  exact one_div_le_one_div_of_le (by exact_mod_cast hx) hxy

lemma invLo_le_one_div {x : ℚ} {y : ℝ} (hy : 0 < y) (hxy : y ≤ (x : ℝ)) :
    (invLo x : ℝ) ≤ 1 / y := by
  apply rdDown_le_real
  push_cast
  exact one_div_le_one_div_of_le hy hxy

/-! ### The right-hand sides -/

/-- Rational upper bound for `π` (`Real.pi_lt_d6`). -/
def piU : ℚ := 3141593 / 10 ^ 6

/-- `√x log² x/(8π)`. -/
noncomputable def F2 (x : ℝ) : ℝ := 1 / (8 * π) * (√x * Real.log x ^ 2)

/-- `√x log x/(8π)`. -/
noncomputable def F1 (x : ℝ) : ℝ := 1 / (8 * π) * (√x * Real.log x)

/-- Lower bound for `F2 a`. -/
def F2lo (a : ℚ) : ℚ := rdDown (sqrtLo a * (max 0 (logLo a)) ^ 2 / (8 * piU))

/-- Lower bound for `F1 a`. -/
def F1lo (a : ℚ) : ℚ := rdDown (sqrtLo a * max 0 (logLo a) / (8 * piU))

lemma inv8pi_ge : (1 / (8 * piU) : ℚ) ≤ (1 / (8 * π) : ℝ) := by
  have := Real.pi_lt_d6
  push_cast
  apply one_div_le_one_div_of_le (by positivity)
  simp only [piU]; push_cast; linarith

lemma F2lo_le {a : ℚ} (ha : 1 ≤ a) : (F2lo a : ℝ) ≤ F2 a := by
  have hl := logLo_le ha
  have hs := sqrtLo_le (by linarith : (0 : ℚ) ≤ a)
  have hm : ((max 0 (logLo a) : ℚ) : ℝ) ≤ Real.log a := by
    push_cast
    exact max_le (Real.log_nonneg (by exact_mod_cast ha)) hl
  have hm0 : (0 : ℝ) ≤ ((max 0 (logLo a) : ℚ) : ℝ) := by push_cast; exact le_max_left _ _
  have hs0 : (0 : ℝ) ≤ (sqrtLo a : ℝ) := by unfold sqrtLo; positivity
  unfold F2lo F2
  apply rdDown_le_real
  have hp := inv8pi_ge
  have e : ((sqrtLo a * (max 0 (logLo a)) ^ 2 / (8 * piU) : ℚ) : ℝ) =
      ((1 / (8 * piU) : ℚ) : ℝ) * ((sqrtLo a : ℝ) * ((max 0 (logLo a) : ℚ) : ℝ) ^ 2) := by
    push_cast; ring
  rw [e]
  apply mul_le_mul hp _ (by positivity) (by positivity)
  exact mul_le_mul hs (pow_le_pow_left₀ hm0 hm 2) (by positivity) (Real.sqrt_nonneg _)

lemma F1lo_le {a : ℚ} (ha : 1 ≤ a) : (F1lo a : ℝ) ≤ F1 a := by
  have hl := logLo_le ha
  have hs := sqrtLo_le (by linarith : (0 : ℚ) ≤ a)
  have hm : ((max 0 (logLo a) : ℚ) : ℝ) ≤ Real.log a := by
    push_cast
    exact max_le (Real.log_nonneg (by exact_mod_cast ha)) hl
  have hm0 : (0 : ℝ) ≤ ((max 0 (logLo a) : ℚ) : ℝ) := by push_cast; exact le_max_left _ _
  have hs0 : (0 : ℝ) ≤ (sqrtLo a : ℝ) := by unfold sqrtLo; positivity
  unfold F1lo F1
  apply rdDown_le_real
  have hp := inv8pi_ge
  have e : ((sqrtLo a * max 0 (logLo a) / (8 * piU) : ℚ) : ℝ) =
      ((1 / (8 * piU) : ℚ) : ℝ) * ((sqrtLo a : ℝ) * ((max 0 (logLo a) : ℚ) : ℝ)) := by
    push_cast; ring
  rw [e]
  apply mul_le_mul hp _ (by positivity) (by positivity)
  exact mul_le_mul hs hm hm0 (Real.sqrt_nonneg _)

lemma F2_mono {a x : ℝ} (ha : 1 ≤ a) (hx : a ≤ x) : F2 a ≤ F2 x := by
  unfold F2
  have hl0 : 0 ≤ Real.log a := Real.log_nonneg ha
  have hl : Real.log a ≤ Real.log x := Real.log_le_log (by linarith) hx
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul (Real.sqrt_le_sqrt hx) (pow_le_pow_left₀ hl0 hl 2) (by positivity)
    (Real.sqrt_nonneg _)

lemma F1_mono {a x : ℝ} (ha : 1 ≤ a) (hx : a ≤ x) : F1 a ≤ F1 x := by
  unfold F1
  have hl0 : 0 ≤ Real.log a := Real.log_nonneg ha
  have hl : Real.log a ≤ Real.log x := Real.log_le_log (by linarith) hx
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact mul_le_mul (Real.sqrt_le_sqrt hx) hl hl0 (Real.sqrt_nonneg _)

/-! ### Primes and prime powers -/

/-- Primality test used by the checkers. -/
def isPrime (n : ℕ) : Bool := 2 ≤ n && n.minFac == n

lemma isPrime_iff (n : ℕ) : isPrime n = true ↔ n.Prime := by
  rw [Nat.prime_def_minFac]
  simp [isPrime]

/-- Prime-power test: `n ≥ 2` and `n = p^{log_p n}` for `p = minFac n`. -/
def isPP (n : ℕ) : Bool := 2 ≤ n && n.minFac ^ Nat.log n.minFac n == n

lemma isPP_iff (n : ℕ) : isPP n = true ↔ IsPrimePow n := by
  rw [isPrimePow_nat_iff]
  simp only [isPP, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  constructor
  · rintro ⟨h2, h⟩
    have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
    refine ⟨n.minFac, Nat.log n.minFac n, hp, ?_, h⟩
    by_contra h0
    push Not at h0
    have : Nat.log n.minFac n = 0 := by omega
    rw [this, pow_zero] at h
    omega
  · rintro ⟨p, k, hp, hk, rfl⟩
    have hmf : (p ^ k).minFac = p := Nat.Prime.pow_minFac hp hk.ne'
    refine ⟨?_, ?_⟩
    · calc 2 ≤ p := hp.two_le
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk
    · rw [hmf, Nat.log_pow hp.one_lt]

end Schoenfeld.Check
