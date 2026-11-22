import Erdos985.Statement

namespace Erdos985

/-!
# Bach's explicit bounds under GRH

These are Lemma 1 of K. McGown, E. Treviño, T. Trudgian, *Resolving Grosswald's conjecture
on GRH*, Funct. Approx. Comment. Math. (2016), arXiv:1508.05182, which they derive following
the proof of Lemma 2.1 in E. Bach, *Comments on search procedures for primitive roots*,
Math. Comp. 66 (1997), 1719–1727.  We use them only at integer `x ≥ 1`.

The non-principal part is proved in `Erdos985.Analytic.bach_nonprincipal_of_GRH`
(`Erdos985/Analytic/ExplicitFormula.lean`), via the Hadamard product of the completed
L-function and a weighted explicit formula. The principal part below is the one remaining
`sorry` on the path to `erdos_985_of_GRH`.
-/

open ArithmeticFunction Real

/-- The constant `c(p, x)` of MTT Lemma 1. -/
noncomputable def bachC (p x : ℝ) : ℝ :=
  (2 / 3) * (1 + 2 / √x + 3 / x ^ (3 / 2 : ℝ)) * (1 + (5 / 3) / Real.log p)
    + (Real.log x + 2) / (√x * Real.log p)

/-- The weighted prime sum `Σ_{n < x} Λ(n) χ(n) (1 - n/x)`. -/
noncomputable def bachSum {N : ℕ} (χ : DirichletCharacter ℂ N) (x : ℕ) : ℂ :=
  ∑ n ∈ Finset.range x, (Λ n : ℂ) * χ n * (1 - (n : ℂ) / x)

/-- MTT Lemma 1, principal part (needs only RH, i.e. GRH for the character mod 1). -/
theorem bach_principal (_hGRH : DirichletLNonvanishingRightOfHalf) (x : ℕ) (_hx : 1 ≤ x) :
    |∑ n ∈ Finset.range x, (Λ n : ℝ) * (1 - (n : ℝ) / x) - x / 2| ≤ √x / 20 + 3 := by
  sorry

end Erdos985
