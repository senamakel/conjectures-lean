import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import Erdos770

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

end Erdos770.Unconditional

#print axioms Erdos770.Unconditional.explicitBound
#print axioms Erdos770.Unconditional.erdos_770_iii
