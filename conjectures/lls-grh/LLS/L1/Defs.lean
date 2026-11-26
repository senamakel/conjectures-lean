import LLS.Defs

/-!
# Definitions for LLS Theorem 1.5 (`L(1, χ)` bounds)

* `l1Sum χ x = Σ_{n ≤ x} Λ(n) χ(n)/(n log n) · log(x/n)/log x` (LLS Lemma 2.5's main sum).
* `l1Sum1 x` is the same sum for the trivial weight `χ = 1`.
* `EshiftLo x`: a lower bound for the gamma part of the shifted Cesàro formula.
-/

namespace LLS

open Complex ArithmeticFunction

/-- `Σ_{n ≤ x} Λ(n) χ(n)/(n log n) · log(x/n)/log x`. -/
noncomputable def l1Sum {M : ℕ} (χ : DirichletCharacter ℂ M) (x : ℕ) : ℂ :=
  ∑ n ∈ Finset.range (x + 1),
    (Λ n : ℂ) * χ n / ((n : ℂ) * (Real.log n : ℂ)) * (Real.log ((x : ℝ) / n) / Real.log x : ℝ)

/-- `Σ_{n ≤ x} Λ(n)/(n log n) · log(x/n)/log x`. -/
noncomputable def l1Sum1 (x : ℕ) : ℝ :=
  ∑ n ∈ Finset.range (x + 1),
    (Λ n : ℝ) / ((n : ℝ) * Real.log n) * (Real.log ((x : ℝ) / n) / Real.log x)

/-- Lower bound for the gamma part of LLS Lemma 2.3 (both parities). -/
noncomputable def EshiftLo (x : ℝ) : ℝ :=
  -(1 / 2) * (1 - 1 / x) * Real.log Real.pi - Real.eulerMascheroniConstant / 2 - Real.log 2
    - 1 / x

end LLS
