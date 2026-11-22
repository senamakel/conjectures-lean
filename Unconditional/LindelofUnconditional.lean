import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Lindelof

/-!
# The Lindelöf hypothesis, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

theorem lindelof_hypothesis : Lindelof.LindelofHypothesis :=
  Lindelof.lindelof_of_RH riemannHypothesis

#print axioms lindelof_hypothesis
