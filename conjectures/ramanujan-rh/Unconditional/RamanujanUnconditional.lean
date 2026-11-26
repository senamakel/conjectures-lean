import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Ramanujan

/-!
# Ramanujan's inequality, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.
-/

/-- Ramanujan's inequality `π(x)² < (e x/log x) π(x/e)` for every real `x ≥ e⁴⁰`. -/
theorem ramanujan_inequality_from_exp40 : Ramanujan.RamanujanInequalityFrom (Real.exp 40) :=
  Ramanujan.ramanujan_of_RH riemannHypothesis

/-- Ramanujan's inequality for every real `x ≥ 38,358,837,683`, given the cited finite range
`[38,358,837,683, e⁴⁰]`. -/
theorem ramanujan_of_verified (hV : Ramanujan.RamanujanVerifiedRange) :
    Ramanujan.RamanujanStatement :=
  Ramanujan.ramanujan_of_RH_of_verified riemannHypothesis hV

#print axioms ramanujan_inequality_from_exp40
#print axioms ramanujan_of_verified
