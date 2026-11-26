import Mathlib

namespace Erdos985

/-!
# Erdős Problem 985, conditional on GRH for Dirichlet L-functions

*Reference:* <https://www.erdosproblems.com/985>

The hypothesis `DirichletLNonvanishingRightOfHalf` is copied verbatim from
`src/Statements.lean` of <https://github.com/leanprover-community/riemann-hypothesis>,
against the same Mathlib revision, so that repository's theorem
`LFunction_ne_zero_of_half_lt_re` discharges it directly.
-/

/-- GRH for Dirichlet L-functions: no `L(s, χ)` vanishes for `Re s > 1/2`
(except the pole of the trivial character at `s = 1`). -/
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- Erdős Problem 985, in the form used by `google-deepmind/formal-conjectures`
(`FormalConjectures/ErdosProblems/985.lean`): every odd prime `p` has a prime
primitive root `q < p`. -/
def Erdos985Statement : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∃ q, q.Prime ∧ q < p ∧ orderOf (q : ZMod p) = p - 1

end Erdos985
