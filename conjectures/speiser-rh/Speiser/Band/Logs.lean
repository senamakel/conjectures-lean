import Mathlib
import SpeiserCompute.Core

/-!
# Enclosures of `log 2`, `log 3`, `log 5`, `log 7` to `5·10⁻¹²`

From Mathlib's `Real.abs_log_sub_add_sum_range_le`:
`log 2 = -log(1 - 1/2)`, `log 3 = log 2 - log(1 - 1/3)`, `log 5 = 2 log 2 - log(1 - 1/5)`,
`log 7 = 3 log 2 + log(1 - 1/8)`.
-/

open Real SpeiserCompute

namespace Speiser.Band

lemma log_one_sub_bounds {x : ℝ} (hx : |x| < 1) (n : ℕ) :
    -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) - |x| ^ (n + 1) / (1 - |x|) ≤ log (1 - x) ∧
    log (1 - x) ≤ -(∑ i ∈ Finset.range n, x ^ (i + 1) / (i + 1)) + |x| ^ (n + 1) / (1 - |x|) := by
  have h := abs_le.mp (Real.abs_log_sub_add_sum_range_le hx n)
  constructor <;> linarith [h.1, h.2]

lemma log_two_tight : (6931471805599 : ℝ) / 10 ^ 13 ≤ log 2 ∧ log 2 ≤ 6931471805600 / 10 ^ 13 := by
  have h := log_one_sub_bounds (x := 1 / 2) (by norm_num [abs_of_pos]) 45
  have e : log (1 - 1 / 2 : ℝ) = -log 2 := by
    rw [show (1 - 1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
  rw [e] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [abs_of_pos] at h
  constructor <;> linarith [h.1, h.2]

lemma log_two_bounds : (693147180557 : ℝ) / 10 ^ 12 ≤ log 2 ∧ log 2 ≤ 693147180562 / 10 ^ 12 := by
  have := log_two_tight; constructor <;> linarith [this.1, this.2]

lemma log_three_bounds :
    (1098612288666 : ℝ) / 10 ^ 12 ≤ log 3 ∧ log 3 ≤ 1098612288671 / 10 ^ 12 := by
  have h := log_one_sub_bounds (x := 1 / 3) (by norm_num [abs_of_pos]) 28
  have e : log (1 - 1 / 3 : ℝ) = log 2 - log 3 := by
    rw [show (1 - 1 / 3 : ℝ) = 2 / 3 by norm_num, Real.log_div (by norm_num) (by norm_num)]
  rw [e] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [abs_of_pos] at h
  have h2 := log_two_tight
  constructor <;> linarith [h.1, h.2, h2.1, h2.2]

lemma log_five_bounds :
    (1609437912432 : ℝ) / 10 ^ 12 ≤ log 5 ∧ log 5 ≤ 1609437912437 / 10 ^ 12 := by
  have h := log_one_sub_bounds (x := 1 / 5) (by norm_num [abs_of_pos]) 20
  have e : log (1 - 1 / 5 : ℝ) = 2 * log 2 - log 5 := by
    rw [show (1 - 1 / 5 : ℝ) = 2 ^ 2 / 5 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  rw [e] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [abs_of_pos] at h
  have h2 := log_two_tight
  constructor <;> linarith [h.1, h.2, h2.1, h2.2]

lemma log_seven_bounds :
    (1945910149053 : ℝ) / 10 ^ 12 ≤ log 7 ∧ log 7 ≤ 1945910149058 / 10 ^ 12 := by
  have h := log_one_sub_bounds (x := 1 / 8) (by norm_num [abs_of_pos]) 16
  have e : log (1 - 1 / 8 : ℝ) = log 7 - 3 * log 2 := by
    rw [show (1 - 1 / 8 : ℝ) = 7 / 2 ^ 3 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]; push_cast; ring
  rw [e] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num [abs_of_pos] at h
  have h2 := log_two_tight
  constructor <;> linarith [h.1, h.2, h2.1, h2.2]

/-- The rational bounds used by the checker, for the primes. -/
lemma logQ_bounds {p : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7) :
    ((logLoQ p : ℤ) : ℝ) / 10 ^ 12 ≤ log p ∧ log p ≤ ((logHiQ p : ℤ) : ℝ) / 10 ^ 12 := by
  rcases hp with rfl | rfl | rfl | rfl
  · have := log_two_bounds; simp only [logLoQ, logHiQ]; push_cast; exact this
  · have := log_three_bounds; simp only [logLoQ, logHiQ]; push_cast; exact this
  · have := log_five_bounds; simp only [logLoQ, logHiQ]; push_cast; exact this
  · have := log_seven_bounds; simp only [logLoQ, logHiQ]; push_cast; exact this

end Speiser.Band
