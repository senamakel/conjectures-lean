import SunPi.Statement
import SunPi.Analytic
import SunPi.Check

/-!
# Sun's Conjectures 2.7(i) and 2.14(ii)

Each conjecture splits into an analytic range (`SunPi.Analytic`, Chebyshev's bound from Mathlib)
and a finite range (`SunPi.Check`).

* 2.7(i): the regions `(j, s, i)` = `(6, 42, 2)`, `(7, 30, 2)`, `(8, 25, 2)`, `(9, 20, 3)`,
  `(10, 17, 3)`, `(11, 15, 3)` cover every pair with `n ≥ s` and `kn ≥ 2^j`. What is left,
  `n ≤ 63` and `kn < bndA n`, is `checkA_ok`, checked by the kernel (`decide +kernel`).
* 2.14(ii): the region `(18, 700, 4)` covers `n ≥ 700`. What is left, `3 ≤ n ≤ 699`, is
  `checkB_ok`, one `native_decide` (prime counting up to `700² = 490000`).
-/

open Real Filter Topology
open scoped Nat.Prime

namespace SunPi

open Check

set_option maxRecDepth 100000 in
/-- The finite range of Conjecture 2.7(i): `5 ≤ n ≤ 63`, `1 ≤ k ≤ n`, `kn < bndA n`. -/
theorem checkA_ok : checkA 5 59 = true := by decide +kernel

/-- The finite range of Conjecture 2.14(ii): `3 ≤ n ≤ 699`. -/
theorem checkB_ok : checkB 3 4 697 = true := by native_decide

theorem regionA_6 : (1 : ℝ) / 3 + 2 / (42 : ℕ) < Real.log 2 * (1 - (1 / 2 : ℝ) ^ 2)
    - ((2 : ℕ) * Real.log 2 - 1 + 4428 / 10000) / (6 : ℕ) := by
  norm_num; linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
theorem regionA_7 : (1 : ℝ) / 3 + 2 / (30 : ℕ) < Real.log 2 * (1 - (1 / 2 : ℝ) ^ 2)
    - ((2 : ℕ) * Real.log 2 - 1 + 4428 / 10000) / (7 : ℕ) := by
  norm_num; linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
theorem regionA_8 : (1 : ℝ) / 3 + 2 / (25 : ℕ) < Real.log 2 * (1 - (1 / 2 : ℝ) ^ 2)
    - ((2 : ℕ) * Real.log 2 - 1 + 4428 / 10000) / (8 : ℕ) := by
  norm_num; linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
theorem regionA_9 : (1 : ℝ) / 3 + 2 / (20 : ℕ) < Real.log 2 * (1 - (1 / 2 : ℝ) ^ 3)
    - ((3 : ℕ) * Real.log 2 - 1 + 4428 / 10000) / (9 : ℕ) := by
  norm_num; linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
theorem regionA_10 : (1 : ℝ) / 3 + 2 / (17 : ℕ) < Real.log 2 * (1 - (1 / 2 : ℝ) ^ 3)
    - ((3 : ℕ) * Real.log 2 - 1 + 4428 / 10000) / (10 : ℕ) := by
  norm_num; linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
theorem regionA_11 : (1 : ℝ) / 3 + 2 / (15 : ℕ) < Real.log 2 * (1 - (1 / 2 : ℝ) ^ 3)
    - ((3 : ℕ) * Real.log 2 - 1 + 4428 / 10000) / (11 : ℕ) := by
  norm_num; linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
theorem regionB_18 : (96 : ℝ) / 210 + (48 + 48 / 210) / (700 : ℕ)
    < Real.log 2 * (1 - (1 / 2 : ℝ) ^ 4)
      - ((4 : ℕ) * Real.log 2 - 1 + 4428 / 10000) / (18 : ℕ) := by
  norm_num; linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]

/-- Conjecture 2.7(i) in integers: `π((k+1)n)^k < π(kn)^{k+1}` for `n > 4`, `1 ≤ k ≤ n`. -/
theorem sun_2_7_i_nat (n k : ℕ) (hn : 4 < n) (hk1 : 1 ≤ k) (hkn : k ≤ n) :
    π ((k + 1) * n) ^ k < π (k * n) ^ (k + 1) := by
  have hX1 : n ≤ k * n := Nat.le_mul_of_pos_left n hk1
  have hX2 : k * n ≤ n * n := Nat.mul_le_mul_right n hkn
  by_cases hfin : n ≤ 63 ∧ k * n < bndA n
  · exact checkA_sound 59 5 checkA_ok n (by omega) (by omega) k hk1 hkn hfin.2
  · rw [not_and_or, not_lt] at hfin
    unfold bndA at hfin
    split_ifs at hfin with h42 h30 h25 h20 h17 h15
    · exact sunA_region n k 6 42 2 hk1 (by norm_num; omega) (by norm_num) h42 (by norm_num)
        (by norm_num) regionA_6
    · exact sunA_region n k 7 30 2 hk1 (by norm_num; omega) (by norm_num) h30 (by norm_num)
        (by norm_num) regionA_7
    · exact sunA_region n k 8 25 2 hk1 (by norm_num; omega) (by norm_num) h25 (by norm_num)
        (by norm_num) regionA_8
    · exact sunA_region n k 9 20 3 hk1 (by norm_num; omega) (by norm_num) h20 (by norm_num)
        (by norm_num) regionA_9
    · exact sunA_region n k 10 17 3 hk1 (by norm_num; omega) (by norm_num) h17 (by norm_num)
        (by norm_num) regionA_10
    · exact sunA_region n k 11 15 3 hk1 (by norm_num; omega) (by norm_num) h15 (by norm_num)
        (by norm_num) regionA_11
    · exfalso
      have : n * n ≤ 14 * 14 := Nat.mul_le_mul (by omega) (by omega)
      omega

/-- Conjecture 2.14(ii) in integers: `π((n+1)²)^n < π(n²)^{n+1}` for `n ≥ 3`. -/
theorem sun_2_14_ii_nat (n : ℕ) (hn : 3 ≤ n) :
    π ((n + 1) ^ 2) ^ n < π (n ^ 2) ^ (n + 1) := by
  rw [sq, sq]
  by_cases hfin : n < 700
  · have h9 : π (3 * 3) = 4 := by decide
    have hB := checkB_ok
    rw [← h9] at hB
    exact checkB_sound 697 3 hB n hn (by omega)
  · have hsq : 700 * 700 ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
    exact sunB_region n 18 700 4 (by norm_num; omega) (by norm_num) (by omega) (by norm_num)
      (by norm_num) regionB_18

/-- From integers to Sun's real powers: `b^k < a^{k+1}` gives `b^{1/(k+1)} < a^{1/k}`. -/
theorem rpow_lt_of_pow_lt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) {k : ℕ} (hk : 1 ≤ k)
    (h : b ^ k < a ^ (k + 1)) : b ^ ((1 : ℝ) / (k + 1)) < a ^ ((1 : ℝ) / k) := by
  by_contra hc
  push Not at hc
  have hN : 0 < k * (k + 1) := by positivity
  have := pow_le_pow_left₀ (by positivity) hc (k * (k + 1))
  have hk0 : (k : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have e1 : (a ^ ((1 : ℝ) / k)) ^ (k * (k + 1)) = a ^ (k + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ha, ← Real.rpow_natCast a (k + 1)]
    congr 1; push_cast; field_simp
  have e2 : (b ^ ((1 : ℝ) / (k + 1))) ^ (k * (k + 1)) = b ^ k := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hb, ← Real.rpow_natCast b k]
    congr 1; push_cast; field_simp
  rw [e1, e2] at this
  linarith

/-- **Sun's Conjecture 2.7(i)** (arXiv:1402.6641): for every `n > 4` and `1 ≤ k ≤ n`,
`π(kn)^{1/k} > π((k+1)n)^{1/(k+1)}`. -/
theorem sun_2_7_i : SunConjecture_2_7_i := by
  intro n hn k hk1 hkn
  have h := sun_2_7_i_nat n k hn hk1 hkn
  have h' : ((π ((k + 1) * n) : ℕ) : ℝ) ^ k < ((π (k * n) : ℕ) : ℝ) ^ (k + 1) := by
    exact_mod_cast h
  have := rpow_lt_of_pow_lt (by positivity) (by positivity) hk1 h'
  simpa using this

/-- **OEIS A238165 (ii)**: for `n > 4`, `k ↦ π(kn)^{1/k}` is strictly decreasing on `[1, n]`. -/
theorem oeis_A238165_ii : OeisA238165_ii := by
  intro n hn
  set f : ℕ → ℝ := fun k => (π (k * n) : ℝ) ^ ((1 : ℝ) / k) with hf
  have step : ∀ k, 1 ≤ k → k < n → f (k + 1) < f k := by
    intro k hk1 hkn
    have := sun_2_7_i n hn k hk1 hkn.le
    simpa [hf] using this
  intro a ha b hb hab
  obtain ⟨ha1, han⟩ := ha
  obtain ⟨hb1, hbn⟩ := hb
  induction b, hab using Nat.le_induction with
  | base => exact step a ha1 (by omega)
  | succ b hab ih =>
    exact lt_trans (step b (by omega) (by omega)) (ih (by omega) (by omega))

/-- **Sun's Conjecture 2.14(ii)** (arXiv:1402.6641): `π(n²)^{1/n}` is strictly decreasing for
`n ≥ 3`. -/
theorem sun_2_14_ii : SunConjecture_2_14_ii := by
  intro n hn
  have h := sun_2_14_ii_nat n hn
  have h' : ((π ((n + 1) ^ 2) : ℕ) : ℝ) ^ n < ((π (n ^ 2) : ℕ) : ℝ) ^ (n + 1) := by
    exact_mod_cast h
  have := rpow_lt_of_pow_lt (by positivity) (by positivity) (by omega : 1 ≤ n) h'
  simpa using this

/-- `a n = π(n²)` for `n ≥ 2`, since `n²` is not prime. -/
theorem a_eq (n : ℕ) (hn : 2 ≤ n) : a n = π (n ^ 2) := by
  unfold a
  rw [Nat.primesBelow_card_eq_primeCounting']
  have hnp : ¬ (n ^ 2).Prime := Nat.Prime.not_prime_pow' (by norm_num)
  have h1 : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
  have : π (n ^ 2) = π (n ^ 2 - 1) := by
    obtain ⟨m, hm⟩ : ∃ m, n ^ 2 = m + 1 := ⟨n ^ 2 - 1, by omega⟩
    rw [hm, Nat.add_sub_cancel]
    rw [hm] at hnp
    show Nat.count Nat.Prime (m + 1 + 1) = Nat.count Nat.Prime (m + 1)
    rw [Nat.count_succ]
    simp [hnp]
  rw [this, ← Nat.primeCounting_sub_one]

/-- **OEIS A038107 (i)**: `a(n)^{1/n}` is strictly decreasing for `n ≥ 3`, with limit 1. -/
theorem oeis_A038107_i : OeisA038107_i := by
  constructor
  · set f : ℕ → ℝ := fun n => (a n : ℝ) ^ ((1 : ℝ) / n) with hf
    have step : ∀ n, 3 ≤ n → f (n + 1) < f n := by
      intro n hn
      have := sun_2_14_ii n hn
      simp only [hf]
      rw [a_eq n (by omega), a_eq (n + 1) (by omega)]
      simpa using this
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    induction y, hxy using Nat.le_induction with
    | base => exact step x hx
    | succ y hxy ih => exact lt_trans (step y (by omega)) (ih (by omega))
  · -- squeeze: `1 ≤ a n ≤ n²` for `n ≥ 2`
    have hup : Tendsto (fun n : ℕ => ((n : ℝ) ^ ((1 : ℝ) / n)) ^ 2) atTop (𝓝 1) := by
      have := (tendsto_rpow_div.comp tendsto_natCast_atTop_atTop).pow 2
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have h1 : (1 : ℝ) ≤ a n := by
        rw [a_eq n hn]
        have : π 2 ≤ π (n ^ 2) := Nat.monotone_primeCounting (by nlinarith)
        have h2 : π 2 = 1 := by decide
        exact_mod_cast (h2 ▸ this)
      exact Real.one_le_rpow h1 (by positivity)
    · filter_upwards [eventually_ge_atTop 2] with n hn
      have hle : (a n : ℝ) ≤ (n : ℝ) ^ 2 := by
        have : a n ≤ n ^ 2 := by
          unfold a
          calc (Nat.primesBelow (n ^ 2)).card ≤ (Finset.range (n ^ 2)).card :=
                Finset.card_le_card (Finset.filter_subset _ _)
            _ = n ^ 2 := Finset.card_range _
        exact_mod_cast this
      rw [← Real.rpow_natCast ((n : ℝ) ^ ((1 : ℝ) / n)) 2, ← Real.rpow_mul (by positivity)]
      calc (a n : ℝ) ^ ((1 : ℝ) / n) ≤ ((n : ℝ) ^ 2) ^ ((1 : ℝ) / n) :=
            Real.rpow_le_rpow (by positivity) hle (by positivity)
        _ = (n : ℝ) ^ ((1 : ℝ) / n * (2 : ℕ)) := by
            rw [← Real.rpow_natCast (n : ℝ) 2, ← Real.rpow_mul (by positivity), mul_comm]

end SunPi
