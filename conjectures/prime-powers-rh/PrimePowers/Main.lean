import Mathlib
import Mills.CubesSharp
import PrimePowers.Statement

/-!
# A prime between `x^α` and `(x+1)^α` for every real `α ≥ 3`, from RH

The premise is mills-rh's `Mills.primeStrictlyBetweenCubes_of_RH` (Caldwell–Cheng's Lemma 5):
under RH every real `y > 2^{1/3} − 1` has a prime in `(y³, (y+1)³)`.

Put `y = x^{α/3}`. Then `y³ = x^α`, and since `t ↦ t^r` is superadditive for `r = α/3 ≥ 1`,
`y + 1 = x^r + 1^r ≤ (x+1)^r`, so `(y+1)³ ≤ (x+1)^α`. The cube interval sits inside.
-/

namespace PrimePowers

open Real

lemma rpow_third_cube {x α : ℝ} (hx : 0 ≤ x) : (x ^ (α / 3)) ^ 3 = x ^ α := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
  norm_num

/-- The sharp form: `x ≥ 0` with `x^{α/3} > 2^{1/3} − 1`. -/
theorem primeBetweenPowers_of_RH (hRH : RiemannHypothesis) {α x : ℝ} (hα : 3 ≤ α)
    (hx0 : 0 ≤ x) (hx : (2 : ℝ) ^ ((1 : ℝ) / 3) - 1 < x ^ (α / 3)) :
    ∃ p : ℕ, p.Prime ∧ x ^ α < p ∧ (p : ℝ) < (x + 1) ^ α := by
  obtain ⟨p, hp, h1, h2⟩ := Mills.primeStrictlyBetweenCubes_of_RH hRH _ hx
  refine ⟨p, hp, by rwa [rpow_third_cube hx0] at h1, ?_⟩
  have hr : (1 : ℝ) ≤ α / 3 := by linarith
  have hsup : x ^ (α / 3) + 1 ≤ (x + 1) ^ (α / 3) := by
    simpa using Real.add_rpow_le_rpow_add hx0 zero_le_one hr
  have hy : 0 ≤ x ^ (α / 3) + 1 := by positivity
  calc (p : ℝ) < (x ^ (α / 3) + 1) ^ 3 := h2
    _ ≤ ((x + 1) ^ (α / 3)) ^ 3 := pow_le_pow_left₀ hy hsup 3
    _ = (x + 1) ^ α := rpow_third_cube (by linarith)

/-- **A prime between `x^α` and `(x+1)^α`, real `α ≥ 3`, real `x ≥ 1`, from RH.** -/
theorem primeBetweenRealPowers_of_RH (hRH : RiemannHypothesis) : PrimeBetweenRealPowers := by
  intro α x hα hx
  have hr : (1 : ℝ) ≤ x ^ (α / 3) := Real.one_le_rpow hx (by linarith)
  have hc : (2 : ℝ) ^ ((1 : ℝ) / 3) < 2 := by
    have := Real.rpow_lt_rpow_of_exponent_lt (x := 2) (by norm_num) (show (1 : ℝ) / 3 < 1 by norm_num)
    simpa using this
  exact primeBetweenPowers_of_RH hRH hα (by linarith) (by linarith)

/-- **A prime between `n^m` and `(n+1)^m`, integer `m ≥ 3`, `n ≥ 1`, from RH.** -/
theorem primeBetweenIntegerPowers_of_RH (hRH : RiemannHypothesis) : PrimeBetweenIntegerPowers := by
  intro m n hm hn
  obtain ⟨p, hp, h1, h2⟩ := primeBetweenRealPowers_of_RH hRH (m : ℝ) (n : ℝ)
    (by exact_mod_cast hm) (by exact_mod_cast hn)
  refine ⟨p, hp, ?_, ?_⟩
  · have : ((n ^ m : ℕ) : ℝ) < p := by simpa [Real.rpow_natCast] using h1
    exact_mod_cast this
  · have : (p : ℝ) < (((n + 1) ^ m : ℕ) : ℝ) := by
      simpa [Real.rpow_natCast] using h2
    exact_mod_cast this

end PrimePowers
