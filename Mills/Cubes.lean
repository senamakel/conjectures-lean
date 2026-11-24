import Mathlib
import Schoenfeld.Theta
import Mills.Upper

/-!
# Under RH there is a prime between `x³` and `(x+1)³` for `x ≥ 10^9`

From `Schoenfeld.thetaBound_of_RH : ThetaBound (1/4) 599`, i.e. `|θ(y) − y| < √y log² y / 4` for
`y ≥ 599` under RH (a weaker constant than Schoenfeld's `1/(8π)`, proved in `schoenfeld-rh`).

Take `a = x³` and `b = (x+1)³ − 1 = x³ + 3x² + 3x`.  Then `θ(b) − θ(a) > 0` as soon as
`b − a = 3x² + 3x > ½ √b log² b`; a prime `p` with `a < p ≤ b` exists whenever `θ a < θ b`.
With `t = (x+1)^{1/8}` one has `√b ≤ t¹²`, `log b ≤ 24 t`, so the requirement follows from
`3 (t⁸ − 1)² > 288 t¹⁴`, which holds for `t ≥ 13`, i.e. `x ≥ 10^9` (`13⁸ < 10⁹`).
`10^9 ≤ 2521008887`, so this is what `Mills.Upper` needs.
-/

set_option linter.constructorNameAsVariable false

namespace Mills

open Chebyshev

/-- A strict increase of `θ` over `(a, b]` produces a prime there. -/
lemma exists_prime_of_theta_lt {a b : ℕ} (h : θ (a : ℝ) < θ (b : ℝ)) :
    ∃ p : ℕ, p.Prime ∧ a < p ∧ p ≤ b := by
  by_contra hne
  push Not at hne
  refine absurd h (not_lt.mpr ?_)
  unfold Chebyshev.theta
  simp only [Nat.floor_natCast]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp ⊢
    obtain ⟨⟨h0, hpb⟩, hpp⟩ := hp
    refine ⟨⟨h0, ?_⟩, hpp⟩
    by_contra hlt
    push Not at hlt
    exact absurd hpb (not_le.mpr (hne p hpp hlt))
  · intro p hp _
    simp only [Finset.mem_filter, Finset.mem_Ioc] at hp
    exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)

lemma cubes_inequality (X : ℝ) (hX : (10 : ℝ) ^ 9 ≤ X) :
    1 / 2 * (√(X ^ 3 + 3 * X ^ 2 + 3 * X) * Real.log (X ^ 3 + 3 * X ^ 2 + 3 * X) ^ 2)
      < 3 * X ^ 2 + 3 * X := by
  have hX0 : 0 < X := by linarith
  set b := X ^ 3 + 3 * X ^ 2 + 3 * X with hb
  have hu : 0 < X + 1 := by linarith
  set t : ℝ := (X + 1) ^ ((1 : ℝ) / ((8 : ℕ) : ℝ)) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hu _
  have ht8 : t ^ 8 = X + 1 := root_pow _ hu.le 8 (by norm_num)
  have ht13 : 13 ≤ t := by
    by_contra hlt
    push Not at hlt
    have : t ^ 8 < 13 ^ 8 := pow_lt_pow_left₀ hlt ht0.le (by norm_num)
    norm_num at this
    nlinarith
  have hbpos : 1 ≤ b := by rw [hb]; nlinarith
  have hbu : b ≤ (X + 1) ^ 3 := by rw [hb]; nlinarith
  have hu3 : (X + 1) ^ 3 = (t ^ 12) ^ 2 := by rw [← ht8]; ring
  have hsq : √b ≤ t ^ 12 := by
    calc √b ≤ √((t ^ 12) ^ 2) := Real.sqrt_le_sqrt (hu3 ▸ hbu)
      _ = t ^ 12 := Real.sqrt_sq (by positivity)
  have hlog : Real.log b ≤ 24 * t := by
    calc Real.log b ≤ Real.log ((X + 1) ^ 3) := Real.log_le_log (by linarith) hbu
      _ = 24 * Real.log t := by rw [Real.log_pow, ← ht8, Real.log_pow]; push_cast; ring
      _ ≤ 24 * t := by
        have := Real.log_le_sub_one_of_pos ht0
        linarith
  have hlog0 : 0 ≤ Real.log b := Real.log_nonneg hbpos
  have hK : √b * Real.log b ^ 2 ≤ t ^ 12 * (24 * t) ^ 2 :=
    mul_le_mul hsq (pow_le_pow_left₀ hlog0 hlog 2) (by positivity) (by positivity)
  have hX8 : X = t ^ 8 - 1 := by linarith
  have h100 : 100 ≤ t ^ 8 := by
    have : (13 : ℝ) ^ 8 ≤ t ^ 8 := pow_le_pow_left₀ (by norm_num) ht13 8
    norm_num at this; linarith
  have h169 : 169 * t ^ 14 ≤ t ^ 16 := by
    have : (169 : ℝ) ≤ t ^ 2 := by nlinarith
    calc 169 * t ^ 14 ≤ t ^ 2 * t ^ 14 := mul_le_mul_of_nonneg_right this (by positivity)
      _ = t ^ 16 := by ring
  have hX2 : (99 / 100 * t ^ 8) ^ 2 ≤ X ^ 2 := by
    apply pow_le_pow_left₀ (by positivity); rw [hX8]; linarith
  have h16 : (t ^ 8) ^ 2 = t ^ 16 := by ring
  have h14 : 0 < t ^ 14 := by positivity
  nlinarith [mul_pos h14 (by norm_num : (0:ℝ) < 1)]

/-- **Primes between cubes under RH**, for `x ≥ 10^9` (and `10^9 ≤ 2521008887`). -/
theorem primeBetweenCubes_of_RH (hRH : RiemannHypothesis) : PrimeBetweenCubes (10 ^ 9) := by
  intro x hx
  have hX : (10 : ℝ) ^ 9 ≤ (x : ℝ) := by exact_mod_cast hx
  set A : ℕ := x ^ 3 with hA
  set B : ℕ := x ^ 3 + 3 * x ^ 2 + 3 * x with hB
  have hAr : (A : ℝ) = (x : ℝ) ^ 3 := by simp [hA]
  have hBr : (B : ℝ) = (x : ℝ) ^ 3 + 3 * (x : ℝ) ^ 2 + 3 * x := by simp [hB]
  have hx0 : (0 : ℝ) < x := by linarith
  have hA599 : (599 : ℝ) ≤ A := by
    rw [hAr]; nlinarith [mul_pos hx0 hx0]
  have hAB : (A : ℝ) ≤ B := by rw [hAr, hBr]; nlinarith [mul_pos hx0 hx0]
  have hth := Schoenfeld.thetaBound_of_RH hRH
  have hA1 := hth (A : ℝ) hA599
  have hB1 := hth (B : ℝ) (le_trans hA599 hAB)
  have hlogA : 0 ≤ Real.log (A : ℝ) := Real.log_nonneg (by linarith)
  have hmono : √(A : ℝ) * Real.log (A : ℝ) ^ 2 ≤ √(B : ℝ) * Real.log (B : ℝ) ^ 2 :=
    mul_le_mul (Real.sqrt_le_sqrt hAB)
      (pow_le_pow_left₀ hlogA (Real.log_le_log (by linarith) hAB) 2) (by positivity)
      (Real.sqrt_nonneg _)
  have hkey := cubes_inequality (x : ℝ) hX
  rw [← hBr] at hkey
  rw [abs_lt] at hA1 hB1
  have hlt : θ (A : ℝ) < θ (B : ℝ) := by
    have : (B : ℝ) - A = 3 * (x : ℝ) ^ 2 + 3 * x := by rw [hAr, hBr]; ring
    nlinarith [hA1.1, hA1.2, hB1.1, hB1.2]
  obtain ⟨p, hp, h1, h2⟩ := exists_prime_of_theta_lt hlt
  refine ⟨p, hp, h1, ?_⟩
  have : (x + 1) ^ 3 = B + 1 := by simp only [hB]; ring
  omega

end Mills
