import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Abundant

/-!
# The abundant-rh theorems, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`.
-/

theorem solePlanat_unconditional : Abundant.SolePlanatStatement :=
  Abundant.solePlanat_of_RH riemannHypothesis

#print axioms solePlanat_unconditional
