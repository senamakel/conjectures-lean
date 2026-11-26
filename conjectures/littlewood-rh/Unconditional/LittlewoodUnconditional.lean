import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Littlewood

/-!
# Littlewood's bound, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

theorem littlewood_bound : Littlewood.LittlewoodBound :=
  Littlewood.littlewood_of_RH riemannHypothesis

#print axioms littlewood_bound
