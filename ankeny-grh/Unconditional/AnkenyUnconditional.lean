import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import Ankeny.Main

/-!
# Bach's theorem and the least quadratic non-residue, with GRH supplied by the
# riemann-hypothesis repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`.
-/

theorem bach_unconditional : Ankeny.BachSubgroupBound (21 / 5) :=
  Ankeny.bach_of_GRH LFunction_ne_zero_of_half_lt_re

theorem leastNonresidue_unconditional : Ankeny.LeastNonresidueBound (21 / 5) :=
  Ankeny.leastNonresidue_of_GRH LFunction_ne_zero_of_half_lt_re

#print axioms bach_unconditional
#print axioms leastNonresidue_unconditional
