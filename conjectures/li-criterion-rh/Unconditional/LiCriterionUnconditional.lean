import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import LiCriterion

/-!
# Li's criterion (RH ⇒ positivity), with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
Run `scripts/check-unconditional.sh` to check it.

`li_criterion_rhs` is formal-conjectures' `RiemannHypothesis.li_criterion_rhs`, statement for
statement.
-/

theorem li_criterion_rhs {n : ℕ} (hn : 0 < n) : 0 < RiemannHypothesis.lambda n :=
  RiemannHypothesis.li_criterion_rhs_of_RH riemannHypothesis hn

#print axioms li_criterion_rhs
