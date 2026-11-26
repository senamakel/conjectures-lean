import Shoup.Statement

/-!
# A real-exponent target (added 2026-11-24)

`PolyOmegaStatement A` (`Shoup/Statement.lean`) takes a natural-number exponent. To record
exponents strictly between Shoup's `4 + o(1)` and Wang's `6`, this file adds the same bound with
a real exponent. The definitions in `Shoup/Statement.lean` are unchanged.
-/

namespace Shoup

open ArithmeticFunction
open scoped ArithmeticFunction.omega

/-- `g(p) = O(ω(p-1)^A (log p)²)` with a real exponent `A`. For a natural number `A` this is
`PolyOmegaStatement A` (`ω(p-1) ≥ 1` for odd `p`). -/
def PolyOmegaRealStatement (A : ℝ) : Prop :=
  ∃ C : ℝ, ∀ p : ℕ, p.Prime → p ≠ 2 →
    HasPrimitiveRootLE p (C * (ω (p - 1) : ℝ) ^ A * Real.log p ^ 2)

end Shoup
