import Mathlib

/-!
# Target statements (fixed; see the conjectures tracker, rule 3)

`G(n) = Σ_{a+b=n} Λ(a) Λ(b)` is the von Mangoldt-weighted count of Goldbach representations, and
`S(x) = Σ_{n ≤ x} G(n)` its summatory function.

Under RH, `S(x) = x²/2 + O(x^{3/2+ε})` for every `ε > 0`. This is equation (5.2) of Granville,
*Refinements of Goldbach's conjecture, and the generalized Riemann hypothesis*, Funct. Approx.
Comment. Math. 37 (2007), 159–173 (his Theorem 1A states the equivalence with RH); Granville's
proof of the converse had a gap that Bhowmik–Ruzsa, arXiv:1711.06442, closed. The O(x^{3/2})
upper bound under RH is due to Fujii, Acta Arith. 58 (1991), 173–179. Only the direction
RH ⇒ bound is in scope here.

No formal-conjectures statement exists (searched 2026-11-24: the only Goldbach file there is
`Wikipedia/GoldbachConjecture.lean`, which has no von Mangoldt average), so the statements below
are written here.

`GoldbachAverageBound` is the fixed target. `GoldbachAverageSharp C` is the stronger explicit
form `|S(x) − x²/2| ≤ C x^{3/2} log² x` for `x ≥ 2`, from which the target follows.
-/

namespace GoldbachAverage

open ArithmeticFunction Filter Asymptotics

/-- `G(n) = Σ_{a+b=n} Λ(a) Λ(b)`. -/
noncomputable def goldbachWeight (n : ℕ) : ℝ :=
  ∑ p ∈ Finset.HasAntidiagonal.antidiagonal n, (Λ p.1 : ℝ) * (Λ p.2 : ℝ)

/-- `S(x) = Σ_{1 ≤ n ≤ x} G(n)`. -/
noncomputable def goldbachSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, goldbachWeight n

/-- Target: `S(x) = x²/2 + O(x^{3/2+ε})` for every `ε > 0`. -/
def GoldbachAverageBound : Prop :=
  ∀ ε : ℝ, 0 < ε →
    (fun x : ℝ => goldbachSum x - x ^ 2 / 2) =O[atTop] fun x : ℝ => x ^ ((3 : ℝ) / 2 + ε)

/-- Explicit form: `|S(x) − x²/2| ≤ C x^{3/2} log² x` for all real `x ≥ 2`. -/
def GoldbachAverageSharp (C : ℝ) : Prop :=
  ∀ x : ℝ, 2 ≤ x →
    |goldbachSum x - x ^ 2 / 2| ≤ C * (x * Real.sqrt x * Real.log x ^ 2)

end GoldbachAverage
