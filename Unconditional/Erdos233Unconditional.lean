import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Erdos233

/-!
# Selberg's bound for Erdős 233, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.

This is `erdos_233.variants.upper_bound` of formal-conjectures (`Σ_{n<N} d_n² ≪ N log⁴ N`),
not the open conjecture `erdos_233` (`≪ N log² N`).
-/

theorem erdos_233_upper_bound : Erdos233.Erdos233UpperBoundStatement :=
  Erdos233.erdos_233_upper_bound_of_RH riemannHypothesis

#print axioms erdos_233_upper_bound
