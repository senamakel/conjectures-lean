import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import LLS

/-!
# The LLS results with GRH supplied by the riemann-hypothesis repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`. Each theorem closes the GRH hypothesis in one line.
-/

theorem leastNonresidueBelowLogSq_unconditional : LLS.LeastNonresidueBelowLogSq :=
  LLS.leastNonresidueBelowLogSq_of_GRH LFunction_ne_zero_of_half_lt_re

theorem bach_unconditional : Ankeny.BachSubgroupBound (11 / 4) :=
  LLS.bach_of_GRH LFunction_ne_zero_of_half_lt_re

theorem leastNonresidue_unconditional : Ankeny.LeastNonresidueBound (11 / 4) :=
  LLS.leastNonresidue_of_GRH LFunction_ne_zero_of_half_lt_re

theorem miller_unconditional : Miller.MillerStatement (11 / 4) :=
  LLS.miller_of_GRH LFunction_ne_zero_of_half_lt_re

theorem l1UpperBoundWith_unconditional : LLS.L1UpperBoundWith 5 :=
  LLS.l1UpperBoundWith_of_GRH LFunction_ne_zero_of_half_lt_re

theorem l1LowerBoundWith_unconditional : LLS.L1LowerBoundWith 5 :=
  LLS.l1LowerBoundWith_of_GRH LFunction_ne_zero_of_half_lt_re

#print axioms leastNonresidueBelowLogSq_unconditional
#print axioms bach_unconditional
#print axioms leastNonresidue_unconditional
#print axioms miller_unconditional
#print axioms l1UpperBoundWith_unconditional
#print axioms l1LowerBoundWith_unconditional
