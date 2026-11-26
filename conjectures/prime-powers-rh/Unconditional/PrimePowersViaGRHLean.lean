import GRH.Bridge  -- conjectures/grh: lsernau/grh-lean (compact edition), ported to our pin
import PrimePowers

/-!
# A prime between consecutive powers, with RH from the vendored grh-lean proof

The same two theorems as `PrimePowersUnconditional.lean`, with `riemannHypothesis` taken from
`conjectures/grh` (a source-built copy of the compact edition of lsernau/grh-lean, Apache-2.0)
instead of leanprover-community/riemann-hypothesis. Only the import differs.

Not part of the default build. Run `scripts/check-via-grh-lean.sh`.
-/

namespace PrimePowers.ViaGRHLean

/-- A prime strictly between `x ^ α` and `(x + 1) ^ α` for every real `α ≥ 3` and real `x ≥ 1`. -/
theorem prime_between_real_powers : PrimePowers.PrimeBetweenRealPowers :=
  PrimePowers.primeBetweenRealPowers_of_RH riemannHypothesis

/-- A prime strictly between `n ^ m` and `(n + 1) ^ m` for every integer `m ≥ 3` and `n ≥ 1`. -/
theorem prime_between_integer_powers : PrimePowers.PrimeBetweenIntegerPowers :=
  PrimePowers.primeBetweenIntegerPowers_of_RH riemannHypothesis

end PrimePowers.ViaGRHLean

#print axioms PrimePowers.ViaGRHLean.prime_between_real_powers
#print axioms PrimePowers.ViaGRHLean.prime_between_integer_powers
