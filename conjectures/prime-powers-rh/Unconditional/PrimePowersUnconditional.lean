import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import PrimePowers

/-!
# A prime between consecutive powers, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

/-- A prime strictly between `x ^ α` and `(x + 1) ^ α` for every real `α ≥ 3` and real `x ≥ 1`. -/
theorem prime_between_real_powers_unconditional : PrimePowers.PrimeBetweenRealPowers :=
  PrimePowers.primeBetweenRealPowers_of_RH riemannHypothesis

/-- A prime strictly between `n ^ m` and `(n + 1) ^ m` for every integer `m ≥ 3` and `n ≥ 1`. -/
theorem prime_between_integer_powers_unconditional : PrimePowers.PrimeBetweenIntegerPowers :=
  PrimePowers.primeBetweenIntegerPowers_of_RH riemannHypothesis

#print axioms prime_between_real_powers_unconditional
#print axioms prime_between_integer_powers_unconditional
