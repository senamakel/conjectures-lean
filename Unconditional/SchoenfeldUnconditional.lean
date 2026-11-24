import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Schoenfeld

/-!
# Schoenfeld's bounds, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

theorem psi_bound : Schoenfeld.PsiBound (1 / 8) 73.2 :=
  Schoenfeld.psiBound_of_RH riemannHypothesis

theorem theta_bound : Schoenfeld.ThetaBound (1 / 4) 599 :=
  Schoenfeld.thetaBound_of_RH riemannHypothesis

theorem pi_bound : Schoenfeld.PiBound (9 / 20) 2657 :=
  Schoenfeld.piBound_of_RH riemannHypothesis

#print axioms psi_bound
#print axioms theta_bound
#print axioms pi_bound
