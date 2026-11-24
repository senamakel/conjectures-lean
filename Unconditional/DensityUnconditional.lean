import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Density

/-!
# The density hypothesis, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

theorem density_hypothesis : DensityHypothesis.Statement :=
  DensityHypothesis.densityHypothesis_of_RH riemannHypothesis

#print axioms density_hypothesis
