import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Robin

/-!
# Robin's and Lagarias's inequalities, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`.

Neither theorem uses `sorry`. The range `5040 < n ≤ exp(e^{30})` verified by Morrill–Platt
(arXiv:1809.10813, Theorem 13) stays an explicit hypothesis, `Robin.RobinVerifiedRange`.
-/

theorem robin_of_verified (hcomp : Robin.RobinVerifiedRange) : Robin.RobinStatement :=
  Robin.robin_of_RH_of_verified riemannHypothesis hcomp

theorem lagarias_of_verified (hcomp : Robin.RobinVerifiedRange) : Robin.LagariasStatement :=
  Robin.lagarias_of_RH_of_verified riemannHypothesis hcomp

#print axioms robin_of_verified
#print axioms lagarias_of_verified
