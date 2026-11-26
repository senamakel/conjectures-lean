import Mertens.Statement2
import Mertens.Statement3

/-!
# Target statements, fourth batch (fixed once written; see the conjectures tracker, rule 3)

* `LiouvilleSharpBound`: the Liouville analogue of Titchmarsh's bound (`MertensSharpBound`),
  `|L(x)| ≤ √x · exp(C log x / log log x)` for large `x`, with `L = liouvilleSum` of
  `Mertens/Statement2.lean`. It follows from Titchmarsh's bound for `M` through
  `L(x) = ∑_{d² ≤ x} M(x/d²)`, at the cost of a factor `log x`. No formal-conjectures
  counterpart (searched google-deepmind/formal-conjectures for Liouville-function bounds,
  2026-11-24).
-/

namespace Mertens

/-- `|L(x)| ≤ √x exp(C log x / log log x)` for all large `x`. -/
def LiouvilleSharpBound : Prop :=
  ∃ C x₀ : ℝ, ∀ x : ℝ, x₀ ≤ x →
    |(liouvilleSum x : ℝ)| ≤ Real.sqrt x * Real.exp (C * Real.log x / Real.log (Real.log x))

end Mertens
