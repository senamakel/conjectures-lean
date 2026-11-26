import Mathlib

/-!
# Target statements, round 5: class numbers (fixed once written; do not edit to make a proof go
through)

Source: Y. Lamzouri, X. Li, K. Soundararajan, *Conditional bounds for the least quadratic
non-residue and related problems*, Math. Comp. 84 (2015), 2391–2412, arXiv:1309.3595, read from
the corrected arXiv source `QuaResL1Corrected.tex` (v3, 2016), Corollary 1.3 (`ClassBounds`):

> Assume GRH. Let `−q` be a fundamental discriminant, and let `h(−q)` denote the class number of
> `ℚ(√−q)`. If `q ≥ 10^10` then
> `h(−q) ≥ (π/(12e^γ)) √q (log log q − log 2 + 1/2 + 1/log log q + 14 log log q/log q)⁻¹`, and
> `h(−q) ≤ (2e^γ/π) √q (log log q − log 2 + 1/2 + 1/log log q)`.

Bounds of this shape go back to Littlewood, *On the class-number of the corpus `P(√−k)`*,
Proc. London Math. Soc. (2) 27 (1928), 358–372.

Conventions. The negative fundamental discriminants are exactly the discriminants of the
imaginary quadratic fields, and `ℚ(√−q)` has discriminant `−q`. So "`−q` a fundamental
discriminant, `h(−q)` the class number of `ℚ(√−q)`" is stated as: for every number field `K`
of degree `2` with `NumberField.discr K = −q`, a bound on `NumberField.classNumber K`. This
avoids any choice of a model for `ℚ(√−q)`.

`ClassNumberFormula` is Dirichlet's class number formula for imaginary quadratic fields, in the
normalisation LLS use (`h(−q) = (√q/π) L(1, χ_{−q})`, `q > 4`), with the Kronecker symbol
`χ_{−q}` characterised by its values at odd `n`: `χ(n) = J(−q | n)`. It is a theorem
(Dirichlet 1839), not a conjecture, but Mathlib does not have it at this pin; it enters the main
library as an explicit hypothesis (tier H) and is discharged in `Unconditional/` from
leanprover-community/riemann-hypothesis (`GlobalTheory.QuadraticZeta.LFunction_one_and_mean_log_eta`,
whose `IsKroneckerChar χ` is the condition below written out).
-/

namespace LLS

open Real NumberField Module

/-- **LLS Corollary 1.3**, upper bound. -/
def ClassNumberUpperBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ q : ℕ, discr K = -q →
    (10 : ℝ) ^ 10 ≤ q →
      (classNumber K : ℝ)
        ≤ 2 * exp eulerMascheroniConstant / π * √q
            * (log (log q) - log 2 + 1 / 2 + 1 / log (log q))

/-- **LLS Corollary 1.3**, lower bound. -/
def ClassNumberLowerBound : Prop :=
  ∀ (K : Type) [Field K] [NumberField K], finrank ℚ K = 2 → ∀ q : ℕ, discr K = -q →
    (10 : ℝ) ^ 10 ≤ q →
      π / (12 * exp eulerMascheroniConstant) * √q
          * (log (log q) - log 2 + 1 / 2 + 1 / log (log q) + 14 * log (log q) / log q)⁻¹
        ≤ classNumber K

/-- Dirichlet's class number formula for imaginary quadratic fields of discriminant `−q < −4`:
`L(1, χ_{−q}) = π h(−q)/√q`, where `χ_{−q}` is the Kronecker symbol, i.e. the character mod `q`
with `χ(n) = J(−q | n)` for odd `n`. (A theorem; tier-H input here, see the module doc.) -/
def ClassNumberFormula : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (q : ℕ) [NeZero q], finrank ℚ K = 2 →
    discr K = -q → 4 < q → ∀ χ : DirichletCharacter ℂ q,
      (∀ n : ℕ, Odd n → χ n = ((jacobiSym (-(q : ℤ)) n : ℤ) : ℂ)) →
        χ.LFunction 1 = (π * classNumber K / √q : ℝ)

end LLS
