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

theorem polyOmega_unconditional : Shoup.PolyOmegaStatement 136 :=
  Shoup.polyOmega_of_GRH LFunction_ne_zero_of_half_lt_re

theorem leastPrimitiveRoot_le_poly_unconditional (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Shoup.HasPrimitiveRootLE p (Shoup.Sieve.polyC * (ω (p - 1) : ℝ) ^ 136 * Real.log p ^ 2) :=
  Shoup.leastPrimitiveRoot_le_poly_of_GRH LFunction_ne_zero_of_half_lt_re p hp hp2

theorem polyOmega7_unconditional : Shoup.PolyOmegaStatement 7 :=
  Shoup.polyOmega7_of_GRH LFunction_ne_zero_of_half_lt_re

theorem leastPrimitiveRoot_le_seven_unconditional (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Shoup.HasPrimitiveRootLE p (Shoup.C7total * (ω (p - 1) : ℝ) ^ 7 * Real.log p ^ 2) :=
  Shoup.leastPrimitiveRoot_le_seven_of_GRH LFunction_ne_zero_of_half_lt_re p hp hp2

theorem polyOmega6_unconditional : Shoup.PolyOmegaStatement 6 :=
  Shoup.polyOmega6_of_GRH LFunction_ne_zero_of_half_lt_re

theorem leastPrimitiveRoot_le_six_unconditional (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Shoup.HasPrimitiveRootLE p (Shoup.C6total * (ω (p - 1) : ℝ) ^ 6 * Real.log p ^ 2) :=
  Shoup.leastPrimitiveRoot_le_six_of_GRH LFunction_ne_zero_of_half_lt_re p hp hp2

/-- Wang Yuan's bound `g(p) = O(ω(p-1)^6 (log p)²)`, unconditionally. -/
theorem wang_unconditional : Shoup.WangStatement :=
  Shoup.wang_of_GRH LFunction_ne_zero_of_half_lt_re

/-- `g(p) = O(ω(p-1)^{21/5} (log p)²)`, unconditionally. -/
theorem polyOmegaReal_unconditional : Shoup.PolyOmegaRealStatement (21 / 5) :=
  Shoup.polyOmegaReal_of_GRH LFunction_ne_zero_of_half_lt_re

theorem leastPrimitiveRoot_le_real_unconditional (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    Shoup.HasPrimitiveRootLE p (Shoup.Creal * (ω (p - 1) : ℝ) ^ (21 / 5 : ℝ) * Real.log p ^ 2) :=
  Shoup.leastPrimitiveRoot_le_real_of_GRH LFunction_ne_zero_of_half_lt_re p hp hp2

theorem polyOmega5_unconditional : Shoup.PolyOmegaStatement 5 :=
  Shoup.polyOmega5_of_GRH LFunction_ne_zero_of_half_lt_re

#print axioms ankenyType_unconditional
#print axioms leastPrimitiveRoot_le_unconditional
#print axioms polyOmega_unconditional
#print axioms leastPrimitiveRoot_le_poly_unconditional
#print axioms polyOmega7_unconditional
#print axioms leastPrimitiveRoot_le_seven_unconditional
#print axioms polyOmega6_unconditional
#print axioms leastPrimitiveRoot_le_six_unconditional
#print axioms wang_unconditional
#print axioms polyOmegaReal_unconditional
#print axioms leastPrimitiveRoot_le_real_unconditional
#print axioms polyOmega5_unconditional
