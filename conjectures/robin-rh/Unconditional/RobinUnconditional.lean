import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Robin

/-!
# Robin's and Lagarias's inequalities, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`.

No theorem here uses `sorry`. `robin_unconditional` and `lagarias_unconditional` use the range
`5040 < n ≤ exp(e^{30})` proved by the verified computation (`Robin.robin_verified_range`);
`robin_of_verified` / `lagarias_of_verified` keep it as a hypothesis.
-/

theorem robin_of_verified (hcomp : Robin.RobinVerifiedRange) : Robin.RobinStatement :=
  Robin.robin_of_RH_of_verified riemannHypothesis hcomp

theorem lagarias_of_verified (hcomp : Robin.RobinVerifiedRange) : Robin.LagariasStatement :=
  Robin.lagarias_of_RH_of_verified riemannHypothesis hcomp

theorem robin_unconditional : Robin.RobinStatement :=
  Robin.robin_of_RH riemannHypothesis

theorem lagarias_unconditional : Robin.LagariasStatement :=
  Robin.lagarias_of_RH riemannHypothesis

#print axioms robin_of_verified
#print axioms lagarias_of_verified
#print axioms robin_unconditional
#print axioms lagarias_unconditional
