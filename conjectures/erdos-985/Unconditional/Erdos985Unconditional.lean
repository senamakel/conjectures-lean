import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import Erdos985

/-!
# Erdős Problem 985, with GRH supplied by the riemann-hypothesis repository

Not part of the default build: it needs the riemann-hypothesis project's compiled modules.
See `README.md` for how to check it.
-/

theorem erdos_985 : Erdos985.Erdos985Statement :=
  Erdos985.erdos_985_of_GRH LFunction_ne_zero_of_half_lt_re

#print axioms erdos_985
