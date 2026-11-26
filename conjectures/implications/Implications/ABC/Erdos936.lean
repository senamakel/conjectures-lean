import Implications.ABC.Radical

/-!
# Erdős 936 under the abc conjecture

The four statements `erdos_936.variants.*` of formal-conjectures
(`FormalConjectures/ErdosProblems/936.lean`, commit `9097e2f`): each of `2^n + 1`, `2^n - 1`,
`n! + 1`, `n! - 1` is powerful for only finitely many `n`. Each follows from
`ABC.ABCConjecture` at `ε = 1/2`.

Deduction (Cushing–Pascoe, arXiv:1611.01192, Lemma 4.3; CrowdMath, arXiv:2005.07321, Thm 2.3):
a powerful `x` has `rad(x)² ≤ x`.

* `2^n ± 1`: the triple `(1, 2^n, 2^n + 1)` or `(1, 2^n - 1, 2^n)` has `rad(abc) ≤ 2 rad(x)` with
  `x` the powerful term, and `(2 rad x)³ < c²` once `c > 64`.
* `n! ± 1`: the triple `(1, n!, n! + 1)` or `(1, n! - 1, n!)` has `rad(abc) ≤ 4^n rad(x)`, since
  `rad(n!)` is the primorial of `n`, which is at most `4^n`; then `(4^n rad x)³ < c²` once
  `4096^n < n!`.

In each case `n ≤ c`, so the finite exceptional set of abc bounds `n`.
-/

namespace Implications.Abc

open _root_.ABC Erdos936 Nat

lemma mem_abcSet_of_le {a b c X : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (hac : Nat.Coprime a c) (hbc : Nat.Coprime b c) (hsum : a + b = c)
    (hX : radical (a * b * c) ≤ X) (h : X ^ 3 < c ^ 2) : (a, b, c) ∈ abcSet (1 / 2) :=
  mem_abcSet_of_cube_lt_sq ha hb hab hac hbc hsum
    (lt_of_le_of_lt (Nat.pow_le_pow_left hX 3) h)

lemma coprime_pred_self {m : ℕ} (hm : 0 < m) : Nat.Coprime (m - 1) m := by
  have : m = (m - 1) + 1 := by omega
  conv_rhs => rw [this]
  exact Nat.coprime_self_add_right.2 (Nat.coprime_one_right _)

lemma coprime_self_succ (m : ℕ) : Nat.Coprime m (m + 1) :=
  Nat.coprime_self_add_right.2 (Nat.coprime_one_right _)

/-- abc implies `erdos_936.variants.two_pow_add_one`. -/
theorem erdos_936_two_pow_add_one_of_abc (habc : ABCConjecture) : TwoPowAddOne := by
  refine eventually_of_abcSet_finite (abcSet_finite habc (by norm_num : (0 : ℝ) < 1 / 2)) _
    (fun n => (1, 2 ^ n, 2 ^ n + 1)) 7 (fun n hn hP => ?_)
    (fun n => (Nat.lt_two_pow_self).le.trans (Nat.le_succ _))
  have h7 : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hn0 : n ≠ 0 := by omega
  refine mem_abcSet_of_le Nat.one_pos (by positivity) (Nat.coprime_one_left _)
    (Nat.coprime_one_left _) (coprime_self_succ _) (by ring) (X := 2 * radical (2 ^ n + 1))
    ?_ (two_mul_cube_lt_sq (radical_sq_le_of_powerful (by omega) hP) (by omega))
  rw [one_mul, radical_mul (coprime_self_succ _), radical_prime_pow Nat.prime_two hn0]

/-- abc implies `erdos_936.variants.two_pow_sub_one`. -/
theorem erdos_936_two_pow_sub_one_of_abc (habc : ABCConjecture) : TwoPowSubOne := by
  refine eventually_of_abcSet_finite (abcSet_finite habc (by norm_num : (0 : ℝ) < 1 / 2)) _
    (fun n => (1, 2 ^ n - 1, 2 ^ n)) 7 (fun n hn hP => ?_)
    (fun n => (Nat.lt_two_pow_self).le)
  have h7 : 2 ^ 7 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hn0 : n ≠ 0 := by omega
  have hpos : 0 < 2 ^ n := by positivity
  have hb0 : 2 ^ n - 1 ≠ 0 := by omega
  refine mem_abcSet_of_le Nat.one_pos (by omega) (Nat.coprime_one_left _)
    (Nat.coprime_one_left _) (coprime_pred_self hpos) (by omega)
    (X := 2 * radical (2 ^ n - 1)) ?_
    (two_mul_cube_lt_sq ((radical_sq_le_of_powerful hb0 hP).trans (by omega)) (by omega))
  rw [one_mul, radical_mul (coprime_pred_self hpos), radical_prime_pow Nat.prime_two hn0,
    mul_comm]

/-- `(4^n)^6 < n!` for all large `n`. -/
lemma exists_four_pow_six_lt_factorial : ∃ N, ∀ n ≥ N, (4 ^ n) ^ 6 < n ! := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 (eventually_pow_lt_factorial 4096)
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  rwa [← pow_mul, mul_comm, pow_mul, show (4 : ℕ) ^ 6 = 4096 by norm_num]

/-- abc implies `erdos_936.variants.factorial_add_one`. -/
theorem erdos_936_factorial_add_one_of_abc (habc : ABCConjecture) : FactorialAddOne := by
  obtain ⟨N, hN⟩ := exists_four_pow_six_lt_factorial
  refine eventually_of_abcSet_finite (abcSet_finite habc (by norm_num : (0 : ℝ) < 1 / 2)) _
    (fun n => (1, n !, n ! + 1)) N (fun n hn hP => ?_)
    (fun n => (Nat.self_le_factorial n).trans (Nat.le_succ _))
  refine mem_abcSet_of_le Nat.one_pos (Nat.factorial_pos n) (Nat.coprime_one_left _)
    (Nat.coprime_one_left _) (coprime_self_succ _) (by ring)
    (X := 4 ^ n * radical (n ! + 1)) ?_
    (four_pow_mul_cube_lt_sq (radical_sq_le_of_powerful (by omega) hP)
      ((hN n hn).trans (Nat.lt_succ_self _)))
  rw [one_mul, radical_mul (coprime_self_succ _)]
  exact Nat.mul_le_mul_right _ (radical_factorial_le n)

/-- abc implies `erdos_936.variants.factorial_sub_one`. -/
theorem erdos_936_factorial_sub_one_of_abc (habc : ABCConjecture) : FactorialSubOne := by
  obtain ⟨N, hN⟩ := exists_four_pow_six_lt_factorial
  refine eventually_of_abcSet_finite (abcSet_finite habc (by norm_num : (0 : ℝ) < 1 / 2)) _
    (fun n => (1, (n !) - 1, n !)) N (fun n hn hP => ?_) (fun n => Nat.self_le_factorial n)
  have hbig := hN n hn
  have h1 : 1 ≤ (4 ^ n) ^ 6 := Nat.one_le_pow _ _ (by positivity)
  have hpos : 0 < n ! := Nat.factorial_pos n
  have hb0 : (n !) - 1 ≠ 0 := by omega
  refine mem_abcSet_of_le Nat.one_pos (by omega) (Nat.coprime_one_left _)
    (Nat.coprime_one_left _) (coprime_pred_self hpos) (by omega)
    (X := 4 ^ n * radical ((n !) - 1)) ?_
    (four_pow_mul_cube_lt_sq ((radical_sq_le_of_powerful hb0 hP).trans (by omega)) hbig)
  rw [one_mul, radical_mul (coprime_pred_self hpos), mul_comm]
  exact Nat.mul_le_mul_right _ (radical_factorial_le n)

end Implications.Abc
