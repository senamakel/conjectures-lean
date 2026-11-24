import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Density

/-!
# The density hypothesis, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

theorem density_hypothesis : DensityHypothesis.Statement :=
  DensityHypothesis.densityHypothesis_of_RH riemannHypothesis

/-- The Guth–Maynard zero-density *statement*, obtained here as a corollary of RH (via the
density hypothesis); this is not a formalisation of Guth–Maynard's unconditional proof. -/
theorem guth_maynard_zero_density : DensityHypothesis.GuthMaynardStatement :=
  DensityHypothesis.guthMaynard_of_RH riemannHypothesis

#print axioms density_hypothesis
#print axioms guth_maynard_zero_density
