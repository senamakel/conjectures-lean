import Mathlib

/-!
# The integrated Chebyshev function at integers and its second difference

`Ψ₁(n) = Σ_{k<n} Λ(k) (n − k)`. Its second difference with step `h` is bounded by `h` times
the von Mangoldt mass of `[a, a + 2h)`:
`Ψ₁(a+2h) − 2Ψ₁(a+h) + Ψ₁(a) ≤ h · Σ_{a ≤ k < a+2h} Λ(k)`.
-/

namespace Cramer

open ArithmeticFunction Finset

/-- `Ψ₁(n) = Σ_{k<n} Λ(k)(n − k)`, the integral of `ψ` from `0` to `n`. -/
noncomputable def psi1N (n : ℕ) : ℝ := ∑ k ∈ range n, (Λ k : ℝ) * ((n : ℝ) - k)

/-- `Ψ₁(n) = n · Σ_{k<n} Λ(k)(1 − k/n)`, the left side of erdos-985's `explicit_formula_zeta`. -/
lemma psi1N_eq_mul (n : ℕ) (hn : 1 ≤ n) :
    psi1N n = n * ∑ k ∈ range n, (Λ k : ℝ) * (1 - (k : ℝ) / n) := by
  rw [psi1N, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp

lemma psi1N_eq_sum_max {n N : ℕ} (hn : n ≤ N) :
    psi1N n = ∑ k ∈ range N, (Λ k : ℝ) * max ((n : ℝ) - k) 0 := by
  rw [psi1N]
  rw [← sum_subset (range_subset_range.mpr hn)]
  · refine sum_congr rfl fun k hk => ?_
    have : (k : ℝ) < n := by exact_mod_cast mem_range.mp hk
    rw [max_eq_left (by linarith)]
  · intro k _ hk
    have : (n : ℝ) ≤ k := by exact_mod_cast not_lt.mp (by simpa using hk)
    rw [max_eq_right (by linarith), mul_zero]

/-- The second difference of `Ψ₁` is at most `h` times the von Mangoldt mass of `[a, a+2h)`. -/
theorem psi1N_second_diff_le (a h : ℕ) :
    psi1N (a + 2 * h) - 2 * psi1N (a + h) + psi1N a
      ≤ h * ∑ k ∈ Ico a (a + 2 * h), (Λ k : ℝ) := by
  set b := a + 2 * h
  rw [psi1N_eq_sum_max (N := b) le_rfl, psi1N_eq_sum_max (N := b) (by omega),
    psi1N_eq_sum_max (n := a) (N := b) (by omega), mul_sum, ← sum_sub_distrib,
    ← sum_add_distrib]
  rw [← sum_range_add_sum_Ico _ (show a ≤ b by omega)]
  have h0 : ∑ k ∈ range a, ((Λ k : ℝ) * max ((b : ℝ) - k) 0 - 2 * ((Λ k : ℝ) *
      max (((a + h : ℕ) : ℝ) - k) 0) + (Λ k : ℝ) * max ((a : ℝ) - k) 0) = 0 := by
    refine sum_eq_zero fun k hk => ?_
    have hk' : (k : ℝ) < a := by exact_mod_cast mem_range.mp hk
    have hb : (b : ℝ) = a + 2 * h := by simp [b]
    push_cast
    have hh : (0 : ℝ) ≤ h := h.cast_nonneg
    rw [max_eq_left (by rw [hb]; linarith), max_eq_left (by linarith),
      max_eq_left (by linarith), hb]
    ring
  rw [h0, zero_add, Finset.mul_sum]
  refine sum_le_sum fun k hk => ?_
  obtain ⟨hk1, hk2⟩ := mem_Ico.mp hk
  have hΛ : (0 : ℝ) ≤ Λ k := vonMangoldt_nonneg
  have hak : (a : ℝ) ≤ k := by exact_mod_cast hk1
  have hkb : (k : ℝ) < a + 2 * h := by exact_mod_cast hk2
  have hb : (b : ℝ) = a + 2 * h := by simp [b]
  rw [max_eq_right (show (a : ℝ) - k ≤ 0 by linarith), hb]
  push_cast
  have key : max ((a : ℝ) + 2 * h - k) 0 - 2 * max ((a : ℝ) + h - k) 0 ≤ h := by
    rcases le_total ((a : ℝ) + h) k with h1 | h1
    · rw [max_eq_right (show (a : ℝ) + h - k ≤ 0 by linarith),
        max_eq_left (show (0 : ℝ) ≤ a + 2 * h - k by linarith)]; linarith
    · rw [max_eq_left (show (0 : ℝ) ≤ a + h - k by linarith),
        max_eq_left (show (0 : ℝ) ≤ a + 2 * h - k by linarith)]; linarith
  nlinarith
end Cramer
