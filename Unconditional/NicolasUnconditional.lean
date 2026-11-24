import Main      -- leanprover-community/riemann-hypothesis: `riemannHypothesis`
import Nicolas

/-!
# Nicolas' inequality, with RH supplied by the riemann-hypothesis repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`.
-/

theorem nicolas_unconditional : Nicolas.NicolasStatement :=
  Nicolas.nicolas_of_RH riemannHypothesis

#print axioms nicolas_unconditional
