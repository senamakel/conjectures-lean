import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import LegendreExceptions

/-!
# Exceptional sets for Legendre, Oppermann, Andrica and Brocard, with RH supplied

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh`.

Each theorem closes the `RiemannHypothesis` argument of the main-library theorem with
`riemannHypothesis` from leanprover-community/riemann-hypothesis. These are bounds for the
exceptional sets, not the four conjectures.
-/

namespace LegendreExceptions.Unconditional

/-- Legendre fails for `O(log³ N)` of the `n ≤ N`. -/
theorem legendre_exceptions : LegendreExceptionBound :=
  legendre_exceptions_of_RH riemannHypothesis

/-- Oppermann fails for `O(log³ N)` of the `x ≤ N`. -/
theorem oppermann_exceptions : OppermannExceptionBound :=
  oppermann_exceptions_of_RH riemannHypothesis

/-- Andrica fails for `O(log³ N)` of the `n ≤ N`. -/
theorem andrica_exceptions : AndricaExceptionBound :=
  andrica_exceptions_of_RH riemannHypothesis

/-- Brocard fails for `O(log³ N)` of the `n ≤ N`. -/
theorem brocard_exceptions : BrocardExceptionBound :=
  brocard_exceptions_of_RH riemannHypothesis

end LegendreExceptions.Unconditional

#print axioms LegendreExceptions.Unconditional.legendre_exceptions
#print axioms LegendreExceptions.Unconditional.oppermann_exceptions
#print axioms LegendreExceptions.Unconditional.andrica_exceptions
#print axioms LegendreExceptions.Unconditional.brocard_exceptions
