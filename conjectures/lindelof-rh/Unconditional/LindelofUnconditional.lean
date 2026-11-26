import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`,
                 -- `LFunction_ne_zero_of_half_lt_re`
import Lindelof

/-!
# The Lindelöf hypothesis, with RH and GRH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

theorem lindelof_hypothesis : Lindelof.LindelofHypothesis :=
  Lindelof.lindelof_of_RH riemannHypothesis

theorem dirichletLindelof : Lindelof.DirichletLindelofHypothesis :=
  Lindelof.dirichletLindelof_of_GRH LFunction_ne_zero_of_half_lt_re

#print axioms lindelof_hypothesis
#print axioms dirichletLindelof
