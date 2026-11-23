import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Robin

/-!
# Robin's and Lagarias's inequalities, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`.

`robin_of_verified` has no `sorry`: the range checked by Morrill–Platt is a hypothesis.
`robin_unconditional` and `lagarias_unconditional` use the cited `Robin.robin_small_range`.
-/

theorem robin_of_verified (hcomp : Robin.RobinVerifiedRange) : Robin.RobinStatement :=
  Robin.robin_of_RH_of_verified riemannHypothesis hcomp

theorem robin_unconditional : Robin.RobinStatement :=
  Robin.robin_of_RH riemannHypothesis

theorem lagarias_unconditional : Robin.LagariasStatement :=
  Robin.lagarias_of_RH riemannHypothesis

#print axioms robin_of_verified
#print axioms robin_unconditional
#print axioms lagarias_unconditional
