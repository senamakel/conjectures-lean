import Mathlib

/-! A generic Rankin bound for the finite set of smooth numbers up to a cutoff. -/

namespace Implications.SmoothGapRankin

/-- The multiplicative weight `n ↦ n ^ (-s)`. -/
noncomputable def rankinWeight (s : ℝ) : ℕ →* ℝ where
  toFun n := (n : ℝ) ^ (-s)
  map_one' := by simp
  map_mul' m n := by
    rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]

private theorem rankinWeight_prime_norm_lt_one {s : ℝ} (hs : 0 < s) {p : ℕ}
    (hp : p.Prime) : ‖rankinWeight s p‖ < 1 := by
  rw [rankinWeight, Real.norm_eq_abs, abs_of_pos]
  · exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by linarith)
  · exact Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _

/-- Rankin's inequality: the number of `Y`-smooth positive integers up to `X` is bounded by
`X ^ s` times the finite Euler product for the weight `n ^ (-s)`. -/
theorem smoothNumbersUpTo_card_le_rankin (X Y : ℕ) (s : ℝ) (hX : 0 < X)
    (hs : 0 < s) :
    (X.smoothNumbersUpTo Y).card ≤
      X ^ s * ∏ p ∈ Y.primesBelow, (1 - rankinWeight s p)⁻¹ := by
  sorry

end Implications.SmoothGapRankin
