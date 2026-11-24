import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Erdos969

/-!
# Axer's bound for the squarefree error term, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

theorem axer_unconditional : Erdos969.AxerBound :=
  Erdos969.axer_of_RH riemannHypothesis

#print axioms axer_unconditional
