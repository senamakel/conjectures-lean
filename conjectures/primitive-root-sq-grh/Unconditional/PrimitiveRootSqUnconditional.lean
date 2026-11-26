import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import PrimitiveRootSq

/-!
# Prime primitive roots modulo `p²` and `p ^ k`, with GRH supplied by the riemann-hypothesis
repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`.

The results below are conditional on the Lean proof of GRH in
leanprover-community/riemann-hypothesis, which has not been independently verified.
-/

namespace PrimitiveRootSq.Unconditional

theorem primitiveRootSq : PrimitiveRootSqStatement :=
  primitiveRootSq_of_GRH LFunction_ne_zero_of_half_lt_re

theorem primitiveRootPow : PrimitiveRootPowStatement :=
  primitiveRootPow_of_GRH LFunction_ne_zero_of_half_lt_re

end PrimitiveRootSq.Unconditional

#print axioms PrimitiveRootSq.Unconditional.primitiveRootSq
#print axioms PrimitiveRootSq.Unconditional.primitiveRootPow
