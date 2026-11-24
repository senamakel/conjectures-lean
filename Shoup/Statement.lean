import Mathlib
import Erdos985.Statement

/-!
# The least primitive root under GRH (target statements — do not change the definitions)

Write `g(p)` for the least positive integer that is a primitive root modulo the prime `p`, and
`r = ω(p - 1)` for the number of distinct prime factors of `p - 1`.

* V. Shoup, *Searching for primitive roots in finite fields*, Math. Comp. **58** (1992),
  369–380, Theorem 1.3: assuming the ERH, `g(p) = O(r⁴ (log r + 1)⁴ (log p)²)`.
* Shoup's introduction reports that Wang Yuan (1959) proved, assuming the ERH,
  `g(p) = O(r⁶ (log p)²)`.
* Unconditionally only Burgess-type bounds `g(p) ≪ p^{1/4 + ε}` are known.

There is no statement of these bounds in `google-deepmind/formal-conjectures` (searched
2026-11-24 for "primitive root", "Shoup", "Wang Yuan", "Ankeny"); the primitive-root predicate
`orderOf (g : ZMod p) = p - 1` is the one used there (`Erdos985.erdos_985`) and in erdos-985 and
grosswald-grh.

The `O`-bounds are transcribed with an existential absolute constant `C` over all odd primes:
for odd `p` we have `r ≥ 1`, so each right-hand side is positive and "for all large `p`" is
equivalent to "for all odd `p`" after enlarging `C`. (For `p = 2`, `r = 0` and the right-hand
sides vanish, so the asymptotic statements say nothing about it.) "`∃ g` with `0 < g ≤ B`" is
the same as "`g(p) ≤ B`".

GRH enters as `Erdos985.DirichletLNonvanishingRightOfHalf`, copied verbatim in erdos-985 from
`src/Statements.lean` of leanprover-community/riemann-hypothesis.
-/

namespace Shoup

open ArithmeticFunction
open scoped ArithmeticFunction.omega

/-- `p` has a primitive root `g` with `0 < g ≤ B`, i.e. `g(p) ≤ B`. -/
def HasPrimitiveRootLE (p : ℕ) (B : ℝ) : Prop :=
  ∃ g : ℕ, 0 < g ∧ (g : ℝ) ≤ B ∧ orderOf (g : ZMod p) = p - 1

/-- `p` has a *prime* primitive root `q ≤ B`. -/
def HasPrimePrimitiveRootLE (p : ℕ) (B : ℝ) : Prop :=
  ∃ q : ℕ, q.Prime ∧ (q : ℝ) ≤ B ∧ orderOf (q : ZMod p) = p - 1

/-- **Shoup (1992), Theorem 1.3** (the fixed target):
`g(p) = O(r⁴ (log r + 1)⁴ (log p)²)` with `r = ω(p - 1)`. -/
def ShoupStatement : Prop :=
  ∃ C : ℝ, ∀ p : ℕ, p.Prime → p ≠ 2 →
    HasPrimitiveRootLE p
      (C * (ω (p - 1) : ℝ) ^ 4 * (Real.log (ω (p - 1)) + 1) ^ 4 * Real.log p ^ 2)

/-- **Wang Yuan (1959)**, as reported by Shoup: `g(p) = O(r⁶ (log p)²)`. -/
def WangStatement : Prop :=
  ∃ C : ℝ, ∀ p : ℕ, p.Prime → p ≠ 2 →
    HasPrimitiveRootLE p (C * (ω (p - 1) : ℝ) ^ 6 * Real.log p ^ 2)

/-- The exponential-in-`ω` bound `g(p) = O((2^{ω(p-1)} log p)²)` that the plain character
expansion of the primitive-root indicator gives (the Ankeny/Linnik route; secondary sources
state Ankeny's 1952 result in this or a similar exponential form). Weaker than both targets. -/
def AnkenyTypeStatement : Prop :=
  ∃ C : ℝ, ∀ p : ℕ, p.Prime → p ≠ 2 →
    HasPrimitiveRootLE p (C * ((2 : ℝ) ^ ω (p - 1) * Real.log p) ^ 2)

end Shoup
