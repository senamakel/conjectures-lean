import Implications.Dickson.Schinzel

/-!
# Bunyakovsky's conjecture implies Landau's fourth problem

The conclusion is formal-conjectures' `PrimesAndPerfectSquares.infinite_prime_sq_add_one`
(`FormalConjectures/Wikipedia/PrimesAndPerfectSquares.lean`, commit `9097e2f`, research open),
copied verbatim: infinitely many `n` with `n ^ 2 + 1` prime.

Bunyakovsky's conjecture (`Implications.Dickson.BunyakovskyConjecture`, verbatim from
formal-conjectures) applies to `f = X ^ 2 + 1`: it has degree 2, positive leading coefficient,
is irreducible over `ℤ` (a monic quadratic with no integer root), and `f(0) = 1` is divisible by
no prime, which is the Schinzel condition for `{f}`. Since Schinzel's hypothesis H implies
Bunyakovsky's conjecture (`bunyakovsky_of_schinzel`), it implies Landau's problem too.
-/

open Polynomial

namespace Implications.Dickson.Landau

/-- `X ^ 2 + 1` is irreducible over `ℤ`. -/
theorem irreducible_X_sq_add_one : Irreducible (X ^ 2 + 1 : ℤ[X]) := by
  have hm : (X ^ 2 + 1 : ℤ[X]).Monic := monic_X_pow_add_C 1 two_ne_zero
  have hd : (X ^ 2 + 1 : ℤ[X]).natDegree = 2 := by
    rw [natDegree_add_eq_left_of_natDegree_lt] <;> simp
  rw [hm.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    roots_eq_zero_iff_not_isRoot hm.ne_zero]
  intro x hx
  simp only [IsRoot, eval_add, eval_pow, eval_X, eval_one] at hx
  nlinarith [sq_nonneg x]

theorem bunyakovskyCondition_X_sq_add_one : BunyakovskyCondition (X ^ 2 + 1 : ℤ[X]) := by
  have hm : (X ^ 2 + 1 : ℤ[X]).Monic := monic_X_pow_add_C 1 two_ne_zero
  refine ⟨?_, irreducible_X_sq_add_one, ?_⟩
  · rw [degree_add_eq_left_of_degree_lt] <;> simp
  · rw [hm.leadingCoeff]; exact one_pos

theorem schinzelCondition_X_sq_add_one : SchinzelCondition {(X ^ 2 + 1 : ℤ[X])} := by
  intro p hp
  refine ⟨0, fun f hf => ?_⟩
  rw [Finset.mem_singleton] at hf
  subst hf
  simp only [eval_add, eval_pow, eval_X, eval_one, Nat.cast_zero]
  norm_num
  exact_mod_cast hp.not_dvd_one

/-- **Bunyakovsky's conjecture implies Landau's fourth problem** (formal-conjectures
`PrimesAndPerfectSquares.infinite_prime_sq_add_one`, conclusion verbatim). -/
theorem infinite_prime_sq_add_one_of_bunyakovsky (h : BunyakovskyConjecture) :
    {n : ℕ | Prime (n^2 + 1)}.Infinite := by
  have H := h (X ^ 2 + 1) ⟨bunyakovskyCondition_X_sq_add_one, schinzelCondition_X_sq_add_one⟩
  rw [Set.infinite_coe_iff] at H
  convert H using 1
  ext n
  simp only [Set.mem_ofPred_eq, eval_add, eval_pow, eval_X, eval_one]
  rw [show ((n : ℤ) ^ 2 + 1) = ((n ^ 2 + 1 : ℕ) : ℤ) by push_cast; ring, Int.natAbs_natCast,
    Nat.prime_iff]

/-- **Schinzel's hypothesis H implies Landau's fourth problem.** -/
theorem infinite_prime_sq_add_one_of_schinzel (h : SchinzelConjecture) :
    {n : ℕ | Prime (n^2 + 1)}.Infinite :=
  infinite_prime_sq_add_one_of_bunyakovsky (bunyakovsky_of_schinzel h)

end Implications.Dickson.Landau
