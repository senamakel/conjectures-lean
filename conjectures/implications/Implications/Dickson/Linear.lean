import Implications.Dickson.Statement

/-!
# Linear forms satisfying the hypotheses of Dickson's conjecture

Helper lemmas: a form `a X + b` over `ℤ` with `a > 0` and `b`, `a` relatively prime has degree 1
and satisfies `BunyakovskyCondition`; and Dickson's conjecture for two forms `a n + b`, `c n + d`
with natural coefficients.
-/

open Polynomial

namespace Implications.Dickson

/-- A linear form `a X + b` with `a > 0` and `IsRelPrime b a` meets the per-form hypothesis of
`DicksonConjecture`. -/
theorem linear_degree_bunyakovsky {a b : ℤ} (ha : 0 < a) (hab : IsRelPrime b a) :
    (C a * X + C b).degree = 1 ∧ BunyakovskyCondition (C a * X + C b) := by
  have hd : (C a * X + C b).degree = 1 := degree_linear ha.ne'
  refine ⟨hd, hd.ge, ?_, ?_⟩
  · refine irreducible_of_degree_eq_one_of_isRelPrime_coeff hd ?_
    simpa [coeff_add, coeff_C_mul, coeff_X, coeff_C] using hab
  · rw [leadingCoeff_linear ha.ne']
    exact ha

theorem natAbs_linear (a b n : ℕ) : ((a : ℤ) * (n : ℤ) + (b : ℤ)).natAbs = a * n + b := by
  rw [show ((a : ℤ) * (n : ℤ) + (b : ℤ)) = ((a * n + b : ℕ) : ℤ) by push_cast; ring,
    Int.natAbs_natCast]

/-- Dickson's conjecture for two forms `a n + b` and `c n + d` with natural coefficients. -/
theorem infinite_pair_of_dickson (h : DicksonConjecture) (a b c d : ℕ) (ha : 0 < a) (hc : 0 < c)
    (hab : Nat.Coprime b a) (hcd : Nat.Coprime d c)
    (hS : ∀ p : ℕ, p.Prime → ∃ n : ℕ, ¬ p ∣ a * n + b ∧ ¬ p ∣ c * n + d) :
    {n : ℕ | (a * n + b).Prime ∧ (c * n + d).Prime}.Infinite := by
  have H := h {C (a : ℤ) * X + C (b : ℤ), C (c : ℤ) * X + C (d : ℤ)} ?_ ?_
  · rw [Set.infinite_coe_iff] at H
    convert H using 1
    ext n
    simp [natAbs_linear]
  · intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · exact linear_degree_bunyakovsky (by exact_mod_cast ha)
        (Nat.isCoprime_iff_coprime.mpr hab).isRelPrime
    · exact linear_degree_bunyakovsky (by exact_mod_cast hc)
        (Nat.isCoprime_iff_coprime.mpr hcd).isRelPrime
  · intro p hp
    obtain ⟨n, h1, h2⟩ := hS p hp
    refine ⟨n, ?_⟩
    intro f hf
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    rcases hf with rfl | rfl
    · simp only [eval_add, eval_mul, eval_C, eval_X]
      exact_mod_cast h1
    · simp only [eval_add, eval_mul, eval_C, eval_X]
      exact_mod_cast h2

end Implications.Dickson
