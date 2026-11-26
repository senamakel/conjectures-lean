import CooksonHills.Statement

/-!
# Cookson Hills from Flint Hills

`sin (2x) = 2 sin x cos x` gives `sin² (2x) ≤ 4 cos² x`, so the `n`-th Cookson Hills term is at
most `32` times the Flint Hills term at `2n`:

  `1 / (n³ cos² n) ≤ 32 / ((2n)³ sin² (2n))`.

The even-index subseries of a convergent series of nonnegative terms converges, so the Flint Hills
series implies the Cookson Hills series. This file uses Mathlib only.
-/

namespace FlintCooksonHills

/-- `sin m ≠ 0` for every positive integer `m`, since `π` is irrational. -/
theorem sin_natCast_ne_zero {m : ℕ} (hm : 0 < m) : Real.sin (m : ℝ) ≠ 0 := by
  rw [Real.sin_ne_zero_iff]
  intro k hk
  by_cases hk0 : k = 0
  · subst hk0
    simp only [Int.cast_zero, zero_mul] at hk
    exact (Nat.cast_ne_zero.mpr hm.ne') hk.symm
  · exact (irrational_pi.intCast_mul hk0).ne_int (m : ℤ) (by simpa using hk)

/-- The Cookson Hills term at `x` is at most `32` times the Flint Hills term at `2x`. -/
theorem cookson_term_le (x : ℝ) (hx : 0 < x) (hs : Real.sin (2 * x) ≠ 0) :
    1 / (x ^ 3 * Real.cos x ^ 2) ≤ 32 * (1 / ((2 * x) ^ 3 * Real.sin (2 * x) ^ 2)) := by
  by_cases hc : Real.cos x = 0
  · rw [hc]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, div_zero]
    positivity
  · have hsin2 : Real.sin (2 * x) ^ 2 ≤ 4 * Real.cos x ^ 2 := by
      rw [Real.sin_two_mul]
      nlinarith [Real.sin_sq_le_one x, sq_nonneg (Real.cos x)]
    have hpos : 0 < (2 * x) ^ 3 * Real.sin (2 * x) ^ 2 := by positivity
    have hpos' : 0 < x ^ 3 * Real.cos x ^ 2 := by positivity
    rw [mul_one_div, div_le_div_iff₀ hpos' hpos]
    have hx3 : 0 < x ^ 3 := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hsin2 hx3.le]

/-- **Flint Hills implies Cookson Hills.** -/
theorem cookson_hills_of_flint_hills (h : FlintHillsStatement) : CooksonHillsStatement := by
  unfold FlintHillsStatement at h
  unfold CooksonHillsStatement
  have hinj : Function.Injective (fun n : ℕ => 2 * n + 1) := by
    intro a b hab
    simp only at hab
    omega
  have hsub := (h.comp_injective hinj).mul_left 32
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hsub
  have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hs : Real.sin (2 * ((n : ℝ) + 1)) ≠ 0 := by
    have := sin_natCast_ne_zero (m := 2 * n + 2) (by omega)
    push_cast at this
    convert this using 2
    ring
  have key := cookson_term_le ((n : ℝ) + 1) hx hs
  simp only [Function.comp_apply]
  push_cast
  have e : (2 * (n : ℝ) + 1 + 1) = 2 * ((n : ℝ) + 1) := by ring
  rw [e]
  exact key

end FlintCooksonHills
