import Main      -- leanprover-community/riemann-hypothesis: `LFunction_ne_zero_of_half_lt_re`
import Goldbach.Main

/-!
# Ternary Goldbach with GRH supplied by the riemann-hypothesis repository

Not part of the default build: it needs that project's compiled modules. Run
`scripts/check-unconditional.sh`. Zinoviev's theorem stays a hypothesis (tier U + H).
-/

theorem ternary_goldbach_of_zinoviev (hZ : Goldbach.ZinovievTheorem) :
    Goldbach.TernaryGoldbachStatement :=
  Goldbach.ternary_goldbach_of_GRH LFunction_ne_zero_of_half_lt_re hZ

#print axioms ternary_goldbach_of_zinoviev
