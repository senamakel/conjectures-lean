import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Mertens

/-!
# Mertens, Riesz, Hardy–Littlewood and Redheffer bounds, with RH supplied by the
# riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

theorem invZeta_bound : Mertens.InvZetaBound :=
  Mertens.invZeta_bound_of_RH riemannHypothesis

theorem mertens_bound : Mertens.MertensBound :=
  Mertens.mertens_of_RH riemannHypothesis

theorem riesz_bound : Mertens.RieszBound :=
  Mertens.riesz_of_RH riemannHypothesis

theorem hardyLittlewood_bound : Mertens.HardyLittlewoodBound :=
  Mertens.hardyLittlewood_of_RH riemannHypothesis

theorem redheffer_bound : Mertens.RedhefferBound :=
  Mertens.redheffer_of_RH riemannHypothesis

#print axioms invZeta_bound
#print axioms mertens_bound
#print axioms riesz_bound
#print axioms hardyLittlewood_bound
#print axioms redheffer_bound
