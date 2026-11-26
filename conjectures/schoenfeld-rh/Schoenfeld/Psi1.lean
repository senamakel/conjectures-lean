import Mathlib

/-!
# The integrated Chebyshev function `Ψ₁`

`Ψ₁(t) = Σ_{n ≤ t} Λ(n)(t − n)` and monotone differencing
`h ψ(s) ≤ Ψ₁(s+h) − Ψ₁(s) ≤ h ψ(s+h)`. Copied from robin-rh (`Robin/Defs.lean`,
`Robin/RH/Psi1.lean`, same author), so that this project does not depend on robin-rh.
-/

namespace Schoenfeld

open ArithmeticFunction Real Chebyshev

/-- `Ψ₁(t) = Σ_{n ≤ t} Λ(n)(t − n)`. -/
noncomputable def psi1 (t : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (Λ n : ℝ) * (t - n)

/-- Extending a sum over `n ≤ ⌊s⌋₊` to `n ≤ N`, when the new terms vanish. -/
lemma sum_range_floor_eq (s : ℝ) {N : ℕ} (hN : ⌊s⌋₊ ≤ N) (f g : ℕ → ℝ)
    (h0 : f 0 = g 0) (h1 : ∀ n : ℕ, n ≠ 0 → (n : ℝ) ≤ s → f n = g n)
    (h2 : ∀ n : ℕ, s < n → g n = 0) :
    ∑ n ∈ Finset.range (⌊s⌋₊ + 1), f n = ∑ n ∈ Finset.range (N + 1), g n := by
  rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by omega) :
    Finset.range (⌊s⌋₊ + 1) ⊆ Finset.range (N + 1))]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rcases eq_or_ne n 0 with rfl | hn0
    · exact h0
    · simp only [Finset.mem_range] at hn
      exact h1 n hn0 ((Nat.le_floor_iff' hn0).mp (by omega))
  · intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    exact h2 n (Nat.lt_of_floor_lt (by omega))

lemma psi1_eq_sum_max {t : ℝ} {N : ℕ} (hN : ⌊t⌋₊ ≤ N) :
    psi1 t = ∑ n ∈ Finset.range (N + 1), (Λ n : ℝ) * max (t - n) 0 :=
  sum_range_floor_eq t hN _ _ (by simp)
    (fun n _ hn => by rw [max_eq_left (by linarith)])
    (fun n hn => by rw [max_eq_right (by linarith), mul_zero])

lemma psi_eq_sum_range (t : ℝ) : ψ t = ∑ n ∈ Finset.range (⌊t⌋₊ + 1), (Λ n : ℝ) := by
  rw [psi_eq_sum_Icc, Nat.range_succ_eq_Icc_zero]

lemma psi_eq_sum_ite {t : ℝ} {N : ℕ} (hN : ⌊t⌋₊ ≤ N) :
    ψ t = ∑ n ∈ Finset.range (N + 1), if (n : ℝ) ≤ t then (Λ n : ℝ) else 0 := by
  rw [psi_eq_sum_range]
  exact sum_range_floor_eq t hN _ _ (by simp) (fun n _ hn => by simp [hn])
    (fun n hn => by simp [not_le.mpr hn])

/-- Monotone differencing: `h ψ(s) ≤ Ψ₁(s+h) − Ψ₁(s) ≤ h ψ(s+h)`. -/
lemma psi1_diff (s h : ℝ) (hh : 0 ≤ h) :
    h * ψ s ≤ psi1 (s + h) - psi1 s ∧ psi1 (s + h) - psi1 s ≤ h * ψ (s + h) := by
  have hN : ⌊s⌋₊ ≤ ⌊s + h⌋₊ := Nat.floor_le_floor (by linarith)
  rw [psi1_eq_sum_max hN, psi1_eq_sum_max le_rfl, psi_eq_sum_ite hN, psi_eq_sum_ite le_rfl,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  constructor
  · refine Finset.sum_le_sum fun n _ => ?_
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    split_ifs with hn
    · rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      exact le_of_eq (by ring)
    · rw [mul_zero, ← mul_sub]
      exact mul_nonneg hΛ (sub_nonneg.mpr (max_le_max (by linarith) le_rfl))
  · refine Finset.sum_le_sum fun n _ => ?_
    have hΛ : (0 : ℝ) ≤ Λ n := vonMangoldt_nonneg
    split_ifs with hn
    · rw [← mul_sub, mul_comm h]
      refine mul_le_mul_of_nonneg_left ?_ hΛ
      have := le_max_left (s - n) 0
      have := le_max_right (s - n) 0
      have : max (s + h - n) 0 ≤ max (s - n) 0 + h := max_le (by linarith) (by linarith)
      linarith
    · push Not at hn
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      simp

/-- At a natural `m ≥ 1`, `Ψ₁(m) = m · Σ_{n<m} Λ(n)(1 − n/m)`. -/
lemma psi1_nat (m : ℕ) (hm : 1 ≤ m) :
    psi1 m = m * ∑ n ∈ Finset.range m, (Λ n : ℝ) * (1 - (n : ℝ) / m) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  unfold psi1
  rw [Nat.floor_natCast, Finset.sum_range_succ, sub_self, mul_zero, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  field_simp

end Schoenfeld
