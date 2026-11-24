import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import Shoup

/-!
# The least primitive root bound, with GRH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

open scoped ArithmeticFunction.omega

theorem ankenyType_unconditional : Shoup.AnkenyTypeStatement :=
  Shoup.ankenyType_of_GRH LFunction_ne_zero_of_half_lt_re

theorem leastPrimitiveRoot_le_unconditional (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Shoup.HasPrimitiveRootLE p (1089 * ((2 : ℝ) ^ ω (p - 1) * Real.log p) ^ 2) :=
  Shoup.leastPrimitiveRoot_le_of_GRH LFunction_ne_zero_of_half_lt_re p hp hp2

#print axioms ankenyType_unconditional
#print axioms leastPrimitiveRoot_le_unconditional
