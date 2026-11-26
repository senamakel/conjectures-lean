import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import Erdos770
import Erdos770.Sharp.GRH

/-!
# Erdős 770(iii) under GRH, with GRH supplied by the riemann-hypothesis repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`.

The results below are conditional on the Lean proof of GRH in
leanprover-community/riemann-hypothesis, which has not been independently verified.
-/

namespace Erdos770.Unconditional

theorem explicitBound : ExplicitBound 420 2 :=
  explicitBound_of_GRH LFunction_ne_zero_of_half_lt_re

theorem erdos_770_iii : Erdos770Part3 :=
  erdos_770_iii_of_GRH LFunction_ne_zero_of_half_lt_re

/-- The sharper constant: `h n ≤ max (P n) ⌈200 (log n)²⌉` for `n ≥ 2`, from Bach's bound with
constant `2` (lls-grh). -/
theorem explicitBound200 : ExplicitBound200 :=
  explicitBound200_of_GRH LFunction_ne_zero_of_half_lt_re

/-- The constant `5`: `h n ≤ max (P n) ⌈5 (log n)²⌉` for `n ≥ 2`, from LLS Theorem 1.1
(lls-grh, `Erdos770/Sharp/`). -/
theorem explicitBound5 : ExplicitBound5 :=
  Sharp.explicitBound5_of_GRH LFunction_ne_zero_of_half_lt_re

end Erdos770.Unconditional

#print axioms Erdos770.Unconditional.explicitBound
#print axioms Erdos770.Unconditional.explicitBound200
#print axioms Erdos770.Unconditional.erdos_770_iii
#print axioms Erdos770.Unconditional.explicitBound5
