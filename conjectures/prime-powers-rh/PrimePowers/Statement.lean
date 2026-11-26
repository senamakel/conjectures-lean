import Mathlib

/-!
# Target statements: a prime between consecutive real powers

Source: Chamberland and Straub, *Weakening the Legendre conjecture*, arXiv:2602.22502 (2026),
Theorem 1.2(a): assuming RH, the interval `[x^{2+δ}, (x+1)^{2+δ}]` contains a prime for every
real `x ≥ 1` once `δ ≥ 1/4` (the statement was read on the arXiv listing and not re-read in the
full text; (unverified) as to numbering). The statements below are the part with exponent
`α = 2 + δ ≥ 3`, with the open interval. They are fixed.
-/

namespace PrimePowers

/-- For every real exponent `α ≥ 3` and every real `x ≥ 1`, a prime lies strictly between
`x ^ α` and `(x + 1) ^ α`. -/
def PrimeBetweenRealPowers : Prop :=
  ∀ α x : ℝ, 3 ≤ α → 1 ≤ x → ∃ p : ℕ, p.Prime ∧ x ^ α < p ∧ (p : ℝ) < (x + 1) ^ α

/-- For every integer exponent `m ≥ 3` and every `n ≥ 1`, a prime lies strictly between `n ^ m`
and `(n + 1) ^ m`. -/
def PrimeBetweenIntegerPowers : Prop :=
  ∀ m n : ℕ, 3 ≤ m → 1 ≤ n → ∃ p : ℕ, p.Prime ∧ n ^ m < p ∧ p < (n + 1) ^ m

end PrimePowers
